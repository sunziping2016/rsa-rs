use rsa_rs::PrivateKey;
use std::time::Instant;
use rsa_rs::numbers::APUInt;
use std::fs::File;
use std::io::Write;

fn main() {
    let before = Instant::now();
    let num_bits = 2048usize;
    let num_prime_tests = 32u64;
    let private_key = PrivateKey::<APUInt>::generate(
        num_bits,
        num_prime_tests,
        num_cpus::get(),
        format!("{}@{}", whoami::username(), whoami::hostname()),
    );
    let private_key_content = pem::encode_config(&pem::Pem {
        tag: "OPENSSH PRIVATE KEY".into(),
        contents: private_key.to_buffer(),
    }, pem::EncodeConfig {
        line_ending: pem::LineEnding::LF,
    });
    File::create("id_rsa").unwrap().write(private_key_content.as_bytes()).unwrap();
    let public_key = private_key.get_public_key();
    let public_key_content = format!(
        "ssh-rsa {} {}", base64::encode(&public_key.to_buffer()), public_key.get_comment());
    File::create("id_rsa.pub").unwrap().write(public_key_content.as_bytes()).unwrap();
    println!("Elapsed {:?}", before.elapsed())
}
