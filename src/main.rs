#![feature(try_from)]
#[macro_use]

extern crate crypto;
extern crate rand;
extern crate rpassword;
extern crate rusqlite;
extern crate rustc_serialize;
extern crate sarkara;

use crypto::scrypt::{scrypt,ScryptParams};
use rand::os::OsRng;
use rand::Rng;
use rpassword::prompt_password_stderr;
use rusqlite::Connection;
use rustc_serialize::hex::{FromHex,ToHex};
use sarkara::aead::Ascon;
use sarkara::hash::{ Blake2b, Hash, GenericHash };
use sarkara::kex::{ KeyExchange, NewHope };
use sarkara::sealedbox::SealedBox;
use std::convert::TryFrom;
use std::env;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::ops::*;
use std::path::PathBuf;

const PK_EXT:&'static str=".pqp";
const SK_EXT:&'static str=".pqs";
const MAC_LENGTH:usize=64;
const SALT_LENGTH:usize=MAC_LENGTH;
const FPR_LENGTH:usize=32;

fn xor8(a:&Vec<u8>,b:&Vec<u8>)->Option<Vec<u8>>{
  if a.len()==b.len(){
    let mut out:Vec<u8>=Vec::with_capacity(a.len());
    for i in 0..a.len(){
      let c=(a[..][i])^(b[..][i]);
      out.push(c);
    }
    return Some(out);
  } else {
    return None;
  }
}

fn setup_directory()->PathBuf{
  let mut path=env::home_dir().unwrap();
  path.push(".pqpg");
  if !path.exists(){
    assert!(std::fs::create_dir(&path).is_ok());
  }
  return path;
}

fn get_key(key_directory:&PathBuf, fpr:&Vec<u8>, ext:&str)->Option<Vec<u8>>{
  let filename = fpr[..].to_hex();
  let mut file_path = key_directory.clone();
  file_path.push(filename+&String::from(ext));
  let mut output:Vec<u8> = Vec::new();
  match File::open(file_path){
    Ok(f) => {
      let mut f = f; // Seriously?
      if f.read_to_end(&mut output).is_err(){
        return None;
      }
    },
    _ => return None
  }
  return Some(output);
}

fn put_key(key_directory:&PathBuf, key:&Vec<u8>, fpr:&Vec<u8>, ext:&str)->bool{
  let mut file_path=key_directory.clone();
  let filename=fpr[..].to_hex();
  file_path.push(filename+&String::from(ext));
  return File::create(file_path)
    .unwrap()
      .write(&key)
        .is_ok();
}

fn get_new_passphrase()->Vec<u8>{
  let (qa,qb)=("New passphrase: ","again: ");
  let mut a=prompt_password_stderr(qa).unwrap();
  let mut b=prompt_password_stderr(qb).unwrap();
  while a!=b {
    a=prompt_password_stderr("Passphrases don't match.\nNew nassphrase: ").unwrap();
    b=prompt_password_stderr(qb).unwrap();
  }
  return a.into_bytes();
}

fn encrypt_key(key:&Vec<u8>)->Vec<u8>{
  let passphrase:Vec<u8>=get_new_passphrase();
  let mut rng=OsRng::new().unwrap();
  let random32=rng.next_u32();
  let (log_n,r,p)=(
    match env::var("SCRYPT_LOG_N"){
      Ok(v) => v.parse::<u8>().unwrap(),
      _ => 16u8-((random32&7) as u8) // in range [9,16]
    },
    match env::var("SCRYPT_R"){
      Ok(v) => v.parse::<u32>().unwrap(),
      _ => 31u32-((random32>>3u32)&15u32) // in range [16,31]
    },
    match env::var("SCRYPT_P"){
      Ok(v) => v.parse::<u32>().unwrap(),
      _ => 1
    }
  );
  /* randomizing the SCrypt parameters a little should make a custom hardware attack more expensive */
  let params=ScryptParams::new(log_n,r,p);
  let mut salt=[0u8;SALT_LENGTH];
  rng.fill_bytes(&mut salt);
  let mut scrypt_pad=key.clone();
  scrypt(&passphrase[..],&salt[..],&params,&mut scrypt_pad[..]);
  let mut output:Vec<u8>=Vec::with_capacity(9+MAC_LENGTH+key.len());
  output.extend_from_slice(&[
    log_n,
    ((r&(255u32<<24))>>24) as u8,
    ((r&(255u32<<16))>>16) as u8,
    ((r&(255u32<<8))>>8) as u8,
    (r&(255u32)) as u8,
    ((p&(255u32<<24))>>24) as u8,
    ((p&(255u32<<16))>>16) as u8,
    ((p&(255u32<<8))>>8) as u8,
    (p&(255u32)) as u8
  ][..]);
  output.extend_from_slice(&salt[..]);
  {
    let mac=xor8(
      &Blake2b::default()
        .with_size(MAC_LENGTH)
          .hash::<Vec<u8>>(&key),
      &Blake2b::default()
        .with_size(MAC_LENGTH)
          .hash::<Vec<u8>>(&scrypt_pad)
    ).unwrap();
    output.extend_from_slice(&mac[..]);
  }
  {
    let encrypted_key=xor8(&scrypt_pad,&key).unwrap();
    output.extend_from_slice(&encrypted_key[..]);
  }
  return output;
}

fn decrypt_key(key:&Vec<u8>)->Vec<u8>{
  let mut passphrase:Vec<u8>=
      prompt_password_stderr("Passphrase: ")
        .unwrap()
          .into_bytes();
  loop {
    let log_n=key[0];
    let r:u32=((key[1] as u32)<<24u32)|
      ((key[2] as u32)<<16u32)|
      ((key[3] as u32)<<8u32)|
      ((key[4] as u32));
    let p:u32=((key[5] as u32)<<24u32)|
      ((key[6] as u32)<<16u32)|
      ((key[7] as u32)<<8u32)|
      ((key[8] as u32));
    let salt:Vec<u8>=Vec::from(&key[9..9+MAC_LENGTH]);
    let mac:Vec<u8>=Vec::from(&key[9+MAC_LENGTH..9+2*MAC_LENGTH]);
    let encrypted_key:Vec<u8>=Vec::from(&key[9+2*MAC_LENGTH..]);
    let params=ScryptParams::new(log_n,r,p);
    let mut scrypt_pad=encrypted_key.clone();
    scrypt(&passphrase[..],&salt[..],&params,&mut scrypt_pad[..]);
    let decrypted_key=xor8(&scrypt_pad,&encrypted_key).unwrap();
    if mac==xor8(
        &Blake2b::default()
          .with_size(MAC_LENGTH)
            .hash::<Vec<u8>>(&decrypted_key),
        &Blake2b::default()
          .with_size(MAC_LENGTH)
            .hash::<Vec<u8>>(&scrypt_pad)
      ).unwrap(){
      return decrypted_key;
      } else {
        passphrase=prompt_password_stderr("Wrong passphrase.\n Try again: ")
        .unwrap()
          .into_bytes();
      }
  }
}

fn keygen(name:&String)->Vec<u8>{
  let (sk, pk) = NewHope::keygen();
  let sk_bytes:Vec<u8> = sk.into();
  let pk_bytes:Vec<u8> = pk.into();
  let fpr:Vec<u8>=
    Blake2b::default()
      .with_size(FPR_LENGTH)
        .hash::<Vec<u8>>(&pk_bytes);
  let dir=setup_directory();
  put_key(&dir,&pk_bytes,&fpr,PK_EXT);
  let ek_bytes=encrypt_key(&sk_bytes);
  put_key(&dir,&ek_bytes,&fpr,SK_EXT);
  let db=setup_db();
  db.execute("
    insert into contacts
    values($1,$2,\"\",\"\",3,3,\"\");
  ",&[&fpr,name]).expect("writing to address book failed");
  return fpr;
}

fn decrypt_data(ciphertext:&Vec<u8>,sk_bytes:&Vec<u8>)->Option<Vec<u8>>{
  let sk:<NewHope as KeyExchange>::PrivateKey =
    <NewHope as KeyExchange>::
      PrivateKey::
        try_from(&sk_bytes[..])
          .unwrap();
  let plaintext=Ascon::open::<NewHope>(&sk,&ciphertext);
  return match plaintext{
    Ok(val)=> Some(val),
    Err(_)=> None
  }
}

fn encrypt_data(plaintext:&Vec<u8>,pk_bytes:&Vec<u8>)->Vec<u8>{
  let pk:<NewHope as KeyExchange>::PublicKey =
    <NewHope as KeyExchange>::
      PublicKey::
        try_from(&pk_bytes[..])
          .unwrap();
  return Ascon::seal::<NewHope>(&pk,&plaintext);
}

fn encrypt_file(fpr:&Vec<u8>, input:Option<&String>, output:Option<&String>){
  let mut plaintext:Vec<u8>=Vec::new();
  match input{
    None => io::stdin().read_to_end(&mut plaintext).unwrap(),
    Some(name) => File::open(name).unwrap().read_to_end(&mut plaintext).unwrap()
  };
  let pk_bytes=get_key(&setup_directory(),fpr,PK_EXT)
    .expect("public key not found");
  let mut ciphertext=fpr.clone();
  ciphertext.extend_from_slice(&encrypt_data(&plaintext,&pk_bytes)[..]);
  match output{
    None => assert_eq!(io::stdout().write(&ciphertext).unwrap(),ciphertext.len()),
    Some(name) => assert_eq!(File::create(name).unwrap().write(&ciphertext).unwrap(),ciphertext.len())
  }
}

fn decrypt_file(input:Option<&String>, output:Option<&String>){
  let mut ciphertext:Vec<u8>=Vec::new();
  match input{
    None => io::stdin().read_to_end(&mut ciphertext).unwrap(),
    Some(name) => File::open(name).unwrap().read_to_end(&mut ciphertext).unwrap()
  };
  let hash=Vec::from(&ciphertext[0..FPR_LENGTH]);
  let ciphertext=Vec::from(&ciphertext[FPR_LENGTH..]);
  let sk_bytes=decrypt_key(&get_key(&setup_directory(),&hash,SK_EXT).expect("private key not found"));
  let plaintext=decrypt_data(&ciphertext,&sk_bytes).unwrap();
  match output{
    None => assert_eq!(io::stdout().write(&plaintext).unwrap(),plaintext.len()),
    Some(name) => assert_eq!(File::create(name).unwrap().write(&plaintext).unwrap(),plaintext.len())
  }
}

fn main(){
  let args:Vec<String>=env::args().collect();
  match args.len(){
    0 => print_help(&args[0]),
    1 => print_help(&args[0]),
    _ => match &args[1][..]{
      "test" => run_tests(),
      "keygen" => println!("Done. Your public key file is in ~/.pqpg/{}{}",keygen(&args[2]).to_hex(),PK_EXT),
      "import" => println!(
        "Done. Your public key file is in ~/.pqpg/{}{}",
        import_key(
          match &args[2][..]{
            "-" => None,
            _ => Some(&args[2])
          },
          &args[3],
          match args.len(){
            4 => None,
            _ => Some(&args[4])
          }
        ).to_hex(),
        PK_EXT),
      "encrypt" => encrypt_file(
        &get_fingerprint(&args[2])
          .expect("no matching fingerprint found"),
        match args.len(){
          3 => None,
          _ => Some(&args[3])
        },
        match args.len(){
          4 => None,
          _ => Some(&args[4])
        }
      ),
      "decrypt" => decrypt_file(
        match args.len(){
          2 => None,
          _ => Some(&args[2])
        },
        match args.len(){
          3 => None,
          _ => Some(&args[3])
        },
      ),
      "chpass" => change_passphrase(
        &get_fingerprint(&args[2])
          .expect("no matching fingerprint found")
      ),
      "list" => list_keys(
        match args.len(){
          2 => None,
          _ => Some(&args[2])
        }
      ),
      _ => print_help(&args[0])
    }
  }
}

fn run_tests(){
  let mut rng=OsRng::new().unwrap();
  {
    println!("{}","testing key encryption...");
    let mut testvec:Vec<u8>=Vec::from(&[0;1<<16][..]);
    rng.fill_bytes(&mut testvec[..]);
    assert_eq!(testvec,decrypt_key(&encrypt_key(&testvec)));
  }
  {
    println!("{}","testing data encryption...");
    let (sk, pk) = NewHope::keygen();
    let sk_bytes:Vec<u8> = sk.into();
    let pk_bytes:Vec<u8> = pk.into();
    let mut testvec:Vec<u8>=Vec::from(&[0;1<<16][..]);
    rng.fill_bytes(&mut testvec[..]);
    assert_eq!(testvec,decrypt_data(
      &encrypt_data(&testvec,&pk_bytes),
      &sk_bytes).unwrap());
  }
  println!("{}","Looks like everything is OK.");
}

fn print_help(this_command:&String){
  println!("\
Usage: {} <subcommand> [args]
  subcommands:
    keygen <name>
      returns the fingerprint of your public key
    import <public_key_file> <name> [address],
      adds a public key to your database
    encrypt <name_or_fingerprint> <plaintext_file> <ciphertext_file>
      obvious
    decrypt <ciphertext_file> <plaintext_file>
      obvious (fingerprint is automatically detected)
    chpass <name_or_fingerprint>
      change the passphrase (of a private key)
    list [name_or_fingerprint]
      list all or search known keys
    test
      do a self-test\
          ",this_command);
}

fn get_fingerprint(search:&String)->Option<Vec<u8>>{
  let db=setup_db();
  let mut stmt = db.prepare("\
    select fingerprint
    from contacts
    where upper(name) like upper($1)
    or upper(address) like upper($1)
    or hex(fingerprint) like upper($1);
  ").expect("preparing SQL statement failed");
  let mut hits=stmt.query(&[search]).unwrap();
  return match hits.next(){
    Some(v) => Some(v.unwrap().get(0)),
    _ => None
  };
}

fn change_passphrase(fingerprint:&Vec<u8>){
  let dir=setup_directory();
  let old_sk_bytes=get_key(&dir,&fingerprint,SK_EXT)
    .expect("private key not found");
  let sk_bytes=decrypt_key(&old_sk_bytes);
  let new_sk_bytes=encrypt_key(&sk_bytes);
  assert_eq!(new_sk_bytes.len(),old_sk_bytes.len());
  // let's not overwrite the key file if encrypt_key() crashes
  put_key(&dir,&new_sk_bytes,&fingerprint,SK_EXT);
}

fn setup_db()->Connection{
  let mut dir=setup_directory();
  dir.push("contacts.sqlite");
  let out=Connection::open(&dir)
    .expect("opening database failed");
  out.execute("
    create table if not exists
      contacts(
        fingerprint blob(32),
        name text(256),
        protocol text(256),
        address text(1024),
        trust integer(-1,3),
        verified integer(-1,3),
        comment text(1024)
      );",&[]).expect("database is damaged");
  return out;
}

fn list_keys(search:Option<&String>){
  let db=setup_db();
  let mut stmt=db.prepare("
    select
      fingerprint,
      hex(fingerprint),
      name,
      protocol,
      address,
      trust,
      verified,
      comment
    from
      contacts
    where
      upper(name) like upper($1)
      or upper(address) like upper($1)
      or hex(fingerprint) like upper($1);
    ").unwrap();
  let mut hits=stmt
    .query(&[search.unwrap_or(&String::from("%"))])
       .unwrap();
  let dir=setup_directory();
  while let Some(result_hit) = hits.next(){
    let hit=result_hit.unwrap();
    let (a,b,c,d,e,f,g,h):(
      &str,String,String,String,String,i64,i64,String
    )=(
      match get_key(&dir,&hit.get(0),SK_EXT){
        Some(_) => "S",
        None => "P"
      },
      hit.get(1),hit.get(2),hit.get(3),
      hit.get(4),hit.get(5),hit.get(6),hit.get(7)
    );
    println!("{}\t{}\t{}\t<{}:{}>\t{}/{}\t{}",a,b,c,d,e,f,g,h);
  }
}

fn import_key(input:Option<&String>,name:&String,addr:Option<&String>)->Vec<u8>{
  let mut pk_bytes:Vec<u8>=Vec::new();
  match input{
    None => io::stdin().read_to_end(&mut pk_bytes).unwrap(),
    Some(file_name) => File::open(file_name).unwrap().read_to_end(&mut pk_bytes).unwrap()
  };
  let fpr:Vec<u8>=
    Blake2b::default()
      .with_size(FPR_LENGTH)
        .hash::<Vec<u8>>(&pk_bytes);
  put_key(&setup_directory(),&pk_bytes,&fpr,PK_EXT);
  let db=setup_db();
  db.execute("
    insert into contacts
    values($1,$2,\"\",$3,0,0,\"\");
  ",&[&fpr,name,addr.unwrap_or(&String::new())]).expect("writing to address book failed");
  return fpr;
}
