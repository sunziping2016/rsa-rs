use nom::IResult;
use nom::bytes::complete::{tag, take, take_while_m_n};
use nom::combinator::{map, all_consuming};
use nom::sequence::{preceded, tuple, terminated};
use nom::number::complete::be_u32;
use nom::combinator::verify;
use crate::numbers::APUInt;
use nom::multi::many_m_n;
use crate::traits::{IsPrimeMillerRabin, One, Zero, Bits, MinBits, MaxBits, ModularInverse};
use rand::distributions::uniform::SampleUniform;
use rand::distributions::{Uniform, Distribution};
use std::ops::{AddAssign, Sub, Add, Mul, Div};
use std::sync::mpsc::channel;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

fn parse_u32(input: &[u8]) -> IResult<&[u8], u32> {
    be_u32(input)
}

fn parse_string(input: &[u8]) -> IResult<&[u8], &[u8]> {
    parse_u32(input)
        .and_then(|(input, bytes)| take(bytes)(input))
}

fn parse_ap_uint(input: &[u8]) -> IResult<&[u8], APUInt> {
    map(parse_string, |x| {
        let mut bytes = x.to_vec();
        bytes.reverse();
        let bytes = bytes.chunks(8)
            .map(|x| {
                let mut num = [0u8; 8];
                for (i, v) in x.iter().enumerate() {
                    num[7 - i] = *v;
                }
                u64::from_be_bytes(num)
            })
            .collect::<Vec<_>>();
        APUInt::from(bytes)
    })(input)
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct PrivateKey<T> {
    pub n: T,
    pub e: T,
    pub d: T,
    pub iqmp: T,
    pub p: T,
    pub q: T,
    pub comment: String,
}

impl PrivateKey<APUInt> {
    pub fn parse(input: &[u8]) -> Result<PrivateKey<APUInt>, nom::Err<nom::error::Error<&[u8]>>> {
        all_consuming(preceded(
            tuple((
                tag(b"openssh-key-v1\0"),
                verify(parse_string, |x: &[u8]| x == b"none"), // cipher name
                verify(parse_string, |x: &[u8]| x == b"none"), // kdf name
                verify(parse_string, |x: &[u8]| x == b""), // kdf options
                |input| parse_u32(input)
                    .and_then(|(input, num)| many_m_n(
                        num as usize,
                        num as usize,
                        parse_string,
                    )(input)), // public keys
            )),
            parse_string, // secret
        ))(input)
            .and_then(|(_, secret)| {
                preceded(
                    tuple((
                        parse_u32, // check0
                        parse_u32, // check1
                        verify(parse_string, |x: &[u8]| x == b"ssh-rsa"), // key type
                    )),
                    map(terminated(tuple((
                        parse_ap_uint, // n
                        parse_ap_uint, // e
                        parse_ap_uint, // d
                        parse_ap_uint, // iqmp
                        parse_ap_uint, // p
                        parse_ap_uint, // q
                        parse_string, // comment
                    )), take_while_m_n(0, 7, |_| true)),
                        |(n, e, d, iqmp, p, q, c)|
                            Self {
                                n, e, d, iqmp, p, q,
                                comment: String::from_utf8(c.to_vec()).unwrap()
                            }
                    ),
                )(secret)
            })
            .map(|x| x.1)
    }

    pub fn check(&self) -> Result<(), &'static str> {
        if self.n != &self.p * &self.q {
            return Err("n != p * q");
        }
        if !self.p.is_prime_miller_rabin(32) {
            return Err("p is not prime");
        }
        if !self.q.is_prime_miller_rabin(32) {
            return Err("q is not prime");
        }
        let phi = (&self.p - APUInt::one()) * (&self.q - APUInt::one());
        if (&self.e * &self.d) % phi != APUInt::one() {
            return Err("e * d != 1  mod phi(n)")
        }
        if (&self.q * &self.iqmp) % &self.p != APUInt::one() {
            return Err("q * iqmp != 1  mod p")
        }
        Ok(())
    }
}

pub fn find_prime_range<T>(low: &T, high: &T, num_prime_tests: u64, num_workers: usize) -> T
    where
        T: 'static + SampleUniform + Clone + Send + Bits + One + IsPrimeMillerRabin +
            for<'a> AddAssign<&'a T> + Ord + Zero + From<u64> + Into<u64>,
        for<'a> &'a T: Add<&'a T, Output=T> + Sub<&'a T, Output=T> {
    let (sender, receiver) = channel();
    let finished = Arc::new(AtomicBool::new(false));
    let three = &(&T::one() + &T::one()) + &T::one();
    let _workers = (0..num_workers)
        .map(|_| {
            let low = low.clone();
            let high = high.clone();
            let three = three.clone();
            let finished = finished.clone();
            let sender = sender.clone();
            thread::spawn(move || {
                let between = Uniform::from(low..=high.clone());
                let num_prime_tests = T::from(num_prime_tests);
                let mut rng = rand::thread_rng();
                while !finished.load(Ordering::Relaxed) {
                    let mut n = between.sample(&mut rng);
                    if match n.cmp(&three) {
                        std::cmp::Ordering::Less | std::cmp::Ordering::Equal =>
                            !n.is_one() && !n.is_zero(),
                        std::cmp::Ordering::Greater => {
                            if !n.get(0) {
                                n += &T::one();
                                if n > high {
                                    continue
                                }
                            }
                            let times = std::cmp::min(&n - &three, num_prime_tests.clone()).into();
                            n.is_prime_miller_rabin(times)
                        },
                    } {
                        let _ = sender.send(n);
                        finished.store(true, Ordering::Relaxed);
                        break;
                    }
                }
            })
        })
        .collect::<Vec<_>>();
    receiver.recv().unwrap()
}

impl<T> PrivateKey<T>
    where
        T: 'static + SampleUniform + Clone + Send + Bits + IsPrimeMillerRabin + ModularInverse +
            for<'a> AddAssign<&'a T> + Ord + Zero + From<u64> + Into<u64> + MinBits + MaxBits +
            One + From<u64>,
        for<'a> &'a T: Add<&'a T, Output=T> + Sub<&'a T, Output=T> + Div<&'a T, Output=T> +
        Mul<&'a T, Output=T> {
    pub fn generate(num_bits: usize, num_prime_tests: u64, num_workers: usize) -> Self {
        let p = find_prime_range(
            &T::min_bits(num_bits / 2),
            &T::max_bits(num_bits / 2),
            num_prime_tests,
            num_workers,
        );
        let q = find_prime_range(
            &(&T::min_bits(num_bits) / &p),
            &(&T::max_bits(num_bits) / &p),
            num_prime_tests,
            num_workers,
        );
        let n = &p * &q;
        let lambda = &(&p - &T::one()) * &(&q - &T::one());
        let e = T::from(65537u64);
        let d= e.modular_inverse(&lambda).1;
        let iqmp = q.modular_inverse(&p).1;
        Self { p, q, n, e, d, iqmp, comment: String::new() }
    }
}