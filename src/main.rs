use rsa_rs::find_prime_range;
use rsa_rs::numbers::APUInt;
use rsa_rs::traits::{MinBits, MaxBits};
use std::time::Instant;

fn main() {
    let num_bits = 2048usize;
    let before = Instant::now();
    let prime = find_prime_range(
        &APUInt::min_bits(num_bits),
        &APUInt::max_bits(num_bits),
        32u64,
        num_cpus::get(),
    );
    println!("{:?}", prime);
    println!("Elapsed {:?}", before.elapsed())
}
