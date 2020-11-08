use rsa_rs::PrivateKey;
use std::time::Instant;
use rsa_rs::numbers::APUInt;

fn main() {
    // let private_key = PrivateKey::parse(&pem::parse(KEY).unwrap().contents).unwrap();
    // println!("{:?}", private_key.n);
    // println!("{:?}", private_key.check());
    let before = Instant::now();
    let num_bits = 2048usize;
    let num_prime_tests = 16u64;
    let _private_key = PrivateKey::<APUInt>::generate(
        num_bits,
        num_prime_tests,
        num_cpus::get(),
    );
    println!("Elapsed {:?}", before.elapsed())
}
