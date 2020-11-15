use rsa_rs::{PrivateKey, PublicKey};
use std::time::Instant;
use rsa_rs::numbers::APUInt;
use std::fs;
use clap::Clap;
use clap::crate_version;
use clap::crate_authors;
use clap::crate_description;
use lazy_static::lazy_static;
use nom::sequence::{tuple, preceded};
use nom::combinator::all_consuming;
use nom::bytes::complete::{tag, take_while1};

#[derive(Clap)]
#[clap(
    version = crate_version!(),
    author = crate_authors!("\n"),
    about = crate_description!(),
)]
struct Options {
    #[clap(subcommand)]
    sub_command: SubCommand
}

#[derive(Clap)]
enum SubCommand {
    Generate(Generate),
    Check(Check),
    Encrypt(Encrypt),
    Decrypt(Decrypt),
}

lazy_static! {
    static ref DEFAULT_COMMENT: String = format!("{}@{}", whoami::username(), whoami::hostname());
}

#[derive(Clap)]
#[clap(about = "Generate private and public key pairs")]
struct Generate {
    #[clap(short, long, default_value = "768", about = "number of bits for prime product n")]
    bits: usize,
    #[clap(short, long, default_value = "32", about = "number of Miller-Rabin prime tests to perform")]
    prime_tests: u64,
    #[clap(short, long, default_value = &DEFAULT_COMMENT[..])]
    comment: String,
    #[clap(default_value = "id_rsa", about = "the file path to the private key file")]
    output: String,
}

#[derive(Clap)]
#[clap(about = "Check whether private and public keys are valid")]
struct Check {
    #[clap(short, takes_value = false)]
    exclude_output: bool,
    #[clap(default_value = "id_rsa", about = "the file path to the private key file")]
    key: String,
}

#[derive(Clap)]
#[clap(about = "Encrypt file with RSA")]
struct Encrypt {
    #[clap(short, long,default_value = "id_rsa", about = "the file path to the private key file")]
    key: String,
    #[clap(about = "the file path to the input file", required = true)]
    input: String,
    #[clap(about = "the file path to the encrypted output file", required = true)]
    output: String,
}

#[derive(Clap)]
#[clap(about = "Decrypt file with RSA")]
struct Decrypt {
    #[clap(short, long,default_value = "id_rsa", about = "the file path to the private key file")]
    key: String,
    #[clap(about = "the file path to the input file", required = true)]
    input: String,
    #[clap(about = "the file path to the decrypted output file", required = true)]
    output: String,
}

fn parse_public_file(input: &str) -> Result<(&str, &str), nom::Err<nom::error::Error<&str>>> {
    all_consuming(preceded(
        tuple((
            tag("ssh-rsa"),
            take_while1(|x: char| x.is_ascii_whitespace()),
        )),
        tuple((
            take_while1(|x: char| x.is_ascii_alphanumeric() || x == '+' || x == '/' || x == '='),
            preceded(
                take_while1(|x: char| x.is_ascii_whitespace()),
                take_while1(|x: char| !x.is_ascii_whitespace()),
            ),
        )),
    ))(input)
        .map(|x| x.1)
}

fn main() {
    let before = Instant::now();
    let opts: Options = Options::parse();
    match opts.sub_command {
        SubCommand::Generate(Generate { bits, prime_tests, comment, output }) => {
            let private_key = PrivateKey::<APUInt>::generate(
                bits,
                prime_tests,
                num_cpus::get(),
                comment,
            );
            let private_key_content = pem::encode_config(&pem::Pem {
                tag: "OPENSSH PRIVATE KEY".into(),
                contents: private_key.to_buffer(),
            }, pem::EncodeConfig {
                line_ending: pem::LineEnding::LF,
            });
            fs::write(&output, private_key_content.as_bytes()).unwrap();
            let public_key = private_key.get_public_key();
            let public_key_content = format!(
                "ssh-rsa {} {}\n", base64::encode(&public_key.to_buffer()), public_key.get_comment());
            fs::write(&format!("{}.pub", output), public_key_content.as_bytes()).unwrap();
        }
        SubCommand::Check(Check { exclude_output, key }) => {
            let private_key = PrivateKey::parse(
                &pem::parse(&fs::read_to_string(&key).unwrap()).unwrap().contents).unwrap();
            print!("Checking private key ... ");
            match private_key.check() {
                Ok(_) => println!("Ok"),
                Err(err) => println!("Err: {}", err),
            }
            if !exclude_output {
                print!("Checking public key ... ");
                let public_file = fs::read_to_string(&format!("{}.pub", key)).unwrap();
                let public_file = parse_public_file(public_file.trim()).unwrap();
                let public_key = PublicKey::parse(&base64::decode(public_file.0).unwrap(),
                                                  public_file.1.into()).unwrap();
                match private_key.check_match(&public_key) {
                    Ok(_) => println!("Ok"),
                    Err(err) => println!("Err: {}", err),
                }
            }
        }
        SubCommand::Encrypt(Encrypt { key, input, output }) => {
            let public_file = fs::read_to_string(&format!("{}.pub", key)).unwrap();
            let public_file = parse_public_file(public_file.trim()).unwrap();
            let public_key = PublicKey::parse(&base64::decode(public_file.0).unwrap(),
                                              public_file.1.into()).unwrap();
            let text = fs::read(&input).unwrap();
            fs::write(&output, public_key.encrypt(&text, None).0).unwrap();
        }
        SubCommand::Decrypt(Decrypt { key, input, output }) => {
            let private_key = PrivateKey::parse(
                &pem::parse(&fs::read_to_string(&key).unwrap()).unwrap().contents).unwrap();
            let text = fs::read(&input).unwrap();
            fs::write(&output, private_key.decrypt(&text, None).0).unwrap();
        }
    }
    println!("Elapsed {:?}", before.elapsed());
}
