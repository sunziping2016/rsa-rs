use nom::IResult;
use nom::bytes::complete::{tag, take, take_while_m_n};
use nom::combinator::{map, all_consuming};
use nom::sequence::{preceded, tuple, terminated};
use nom::number::complete::be_u32;
use nom::combinator::verify;
use crate::numbers::{APUInt, APUFloat};
use nom::multi::many_m_n;
use crate::traits::{IsPrimeMillerRabin, One, Zero, Bits, MinBits, MaxBits, ModularInverse, Recip, FastExponentWithRecip};
use rand::distributions::{Uniform, Distribution};
use std::sync::mpsc::channel;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::iter::repeat;
use lazy_static::lazy_static;
use crate::ap_uint;

fn parse_u32(input: &[u8]) -> IResult<&[u8], u32> {
    be_u32(input)
}

fn to_buffer_u32(number: u32) -> Vec<u8> {
    number.to_be_bytes().to_vec()
}

fn parse_string(input: &[u8]) -> IResult<&[u8], &[u8]> {
    parse_u32(input)
        .and_then(|(input, bytes)| take(bytes)(input))
}

fn to_buffer_string(string: &[u8]) -> Vec<u8> {
    let mut result = to_buffer_u32(string.len() as u32);
    result.extend(string);
    result
}

fn parse_ap_uint(input: &[u8]) -> IResult<&[u8], APUInt> {
    map(parse_string, |x| {
        let bytes = x.to_vec().rchunks(8)
            .map(|x| {
                let mut num = [0u8; 8];
                for (i, v) in x.iter().enumerate() {
                    num[i + 8 - x.len()] = *v;
                }
                u64::from_be_bytes(num)
            })
            .collect::<Vec<_>>();
        APUInt::from(bytes)
    })(input)
}

fn to_buffer_ap_uint(number: &APUInt) -> Vec<u8> {
    if number.is_zero() {
        to_buffer_string(b"")
    } else {
        let mut bytes = number.bits.iter().rev()
            .flat_map(|x|
                x.to_be_bytes().iter()
                    .copied()
                    .collect::<Vec<_>>()
            )
            .skip(7 - (number.n_bits - 1) / 8 % 8)
            .collect::<Vec<_>>();
        if let Some(first) = bytes.first() {
            if first & 0x80 != 0 {
                bytes.insert(0, 0u8);
            }
        }
        to_buffer_string(&bytes)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct PrivateKey<T> {
    pub(crate) n: T,
    pub(crate) e: T,
    pub(crate) d: T,
    pub(crate) iqmp: T,
    pub(crate) p: T,
    pub(crate) q: T,
    pub(crate) comment: String,
}

impl<T: Clone> PrivateKey<T> {
    pub fn get_public_key(&self) -> PublicKey<T> {
        PublicKey::<T> {
            n: self.n.clone(),
            e: self.e.clone(),
            comment: self.comment.clone(),
        }
    }
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
                                n,
                                e,
                                d,
                                iqmp,
                                p,
                                q,
                                comment: String::from_utf8(c.to_vec()).unwrap(),
                            },
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
            return Err("e * d != 1  mod phi(n)");
        }
        if (&self.q * &self.iqmp) % &self.p != APUInt::one() {
            return Err("q * iqmp != 1  mod p");
        }
        Ok(())
    }

    pub fn check_match(&self, public: &PublicKey<APUInt>) -> Result<(), &'static str> {
        if self.n != public.n {
            return Err("private.n != public.n");
        }
        if self.e != public.e {
            return Err("private.e != public.e");
        }
        Ok(())
    }

    pub fn to_buffer(&self) -> Vec<u8> {
        let mut result = Vec::new();
        result.extend(b"openssh-key-v1\0");
        result.extend(to_buffer_string(b"none")); // cipher name
        result.extend(to_buffer_string(b"none")); // kdf name
        result.extend(to_buffer_string(b"")); // kdf options
        result.extend(to_buffer_u32(1)); // public keys
        let mut public_key = Vec::new();
        public_key.extend(to_buffer_string(b"ssh-rsa")); // key type
        public_key.extend(to_buffer_ap_uint(&self.e));
        public_key.extend(to_buffer_ap_uint(&self.n));
        result.extend(to_buffer_string(&public_key));
        let mut private_key = Vec::new(); // private key
        private_key.extend(to_buffer_u32(0)); // check0
        private_key.extend(to_buffer_u32(0)); // check1
        private_key.extend(to_buffer_string(b"ssh-rsa")); // key type
        private_key.extend(to_buffer_ap_uint(&self.n));
        private_key.extend(to_buffer_ap_uint(&self.e));
        private_key.extend(to_buffer_ap_uint(&self.d));
        private_key.extend(to_buffer_ap_uint(&self.iqmp));
        private_key.extend(to_buffer_ap_uint(&self.p));
        private_key.extend(to_buffer_ap_uint(&self.q));
        private_key.extend(to_buffer_string(self.comment.as_bytes()));
        private_key.extend(&[1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8]
            [0..(7 - (private_key.len() - 1) % 8)]);
        result.extend(to_buffer_string(&private_key));
        result
    }
}

lazy_static! {
    static ref AP_UINT_PRIMES: Vec<APUInt> = [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
    47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
    151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
    257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
    373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479,
    487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607,
    613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733,
    739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859,
    863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]
    .iter().map(|x| APUInt::from(*x)).collect();
}

pub fn find_prime_range(low: &APUInt, high: &APUInt,
                        num_prime_tests: u64, num_workers: usize) -> APUInt {
    let (sender, receiver) = channel();
    let finished = Arc::new(AtomicBool::new(false));
    let three = ap_uint!(3);
    let _workers = (0..num_workers)
        .map(|_| {
            let low = low.clone();
            let high = high.clone();
            let three = three.clone();
            let finished = finished.clone();
            let sender = sender.clone();
            thread::spawn(move || {
                let between = Uniform::from(low..=high.clone());
                let num_prime_tests = APUInt::from(num_prime_tests);
                let mut rng = rand::thread_rng();
                'outer: while !finished.load(Ordering::Relaxed) {
                    let mut n = between.sample(&mut rng);
                    if match n.cmp(&three) {
                        std::cmp::Ordering::Less | std::cmp::Ordering::Equal =>
                            !n.is_one() && !n.is_zero(),
                        std::cmp::Ordering::Greater => {
                            if !n.get(0) {
                                n += APUInt::one();
                                if n > high {
                                    continue;
                                }
                            }
                            for i in AP_UINT_PRIMES.iter() {
                                if (&n % i).is_zero() {
                                    println!("{:?}", i);
                                    continue 'outer;
                                }
                            }
                            let times = std::cmp::min(&n - &three, num_prime_tests.clone()).into();
                            n.is_prime_miller_rabin(times)
                        }
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

impl PrivateKey<APUInt> {
    pub fn generate(num_bits: usize, num_prime_tests: u64,
                    num_workers: usize, comment: String) -> Self {
        let p = find_prime_range(
            &APUInt::min_bits(num_bits / 2),
            &APUInt::max_bits(num_bits / 2),
            num_prime_tests,
            num_workers,
        );
        let q = find_prime_range(
            &(&APUInt::min_bits(num_bits) / &p),
            &(&APUInt::max_bits(num_bits) / &p),
            num_prime_tests,
            num_workers,
        );
        let n = &p * &q;
        let lambda = &(&p - APUInt::one()) * &(&q - APUInt::one());
        let e = APUInt::from(65537u64);
        let d = e.modular_inverse(&lambda).1;
        let iqmp = q.modular_inverse(&p).1;
        Self { p, q, n, e, d, iqmp, comment }
    }
}

#[derive(Debug, Clone)]
pub struct PublicKey<T> {
    pub(crate) n: T,
    pub(crate) e: T,
    pub(crate) comment: String,
}

impl<T> PublicKey<T> {
    pub fn get_comment(&self) -> &String { &self.comment }
}

impl PublicKey<APUInt> {
    pub fn parse(input: &[u8], comment: String) -> Result<PublicKey<APUInt>, nom::Err<nom::error::Error<&[u8]>>> {
        all_consuming(preceded(
            verify(parse_string, |x: &[u8]| x == b"ssh-rsa"),
            map(tuple((
                parse_ap_uint, // e
                parse_ap_uint, // n
            )), move |(e, n)| Self { n, e, comment: comment.clone() }),
        ))(input)
            .map(|x| x.1)
    }

    pub fn to_buffer(&self) -> Vec<u8> {
        let mut public_key = Vec::new();
        public_key.extend(to_buffer_string(b"ssh-rsa")); // key type
        public_key.extend(to_buffer_ap_uint(&self.e));
        public_key.extend(to_buffer_ap_uint(&self.n));
        public_key
    }
}

#[derive(Debug, Clone)]
pub struct PublicTransformContext {
    n_recip: APUFloat,
}

impl PublicKey<APUInt> {
    pub fn encrypt(&self, input: &[u8],
                   context: Option<PublicTransformContext>)
                   -> (Vec<u8>, PublicTransformContext) {
        assert!(self.n.n_bits >= 9);
        let context = context.unwrap_or_else(|| PublicTransformContext {
            n_recip: self.n.recip(),
        });
        let input = (input.len() as u64).to_le_bytes().iter()
            .chain(input.iter())
            .copied()
            .collect::<Vec<_>>();
        let result = input.chunks((self.n.n_bits - 1) / 8)
            .flat_map(|x|
                APUInt::from(x.chunks(8)
                    .map(|x| {
                        let mut num = [0u8; 8];
                        for (i, v) in x.iter().enumerate() {
                            num[i] = *v;
                        }
                        u64::from_le_bytes(num)
                    })
                    .collect::<Vec<_>>()
                )
                    .fast_exponent_with_recip(&self.e, &self.n, &context.n_recip)
                    .bits.iter()
                    .flat_map(|x| x.to_le_bytes().to_vec())
                    .chain(repeat(0u8))
                    .take((self.n.n_bits + 7) / 8)
                    .collect::<Vec<_>>()
            )
            .collect::<Vec<u8>>();
        (result, context)
    }
}

#[derive(Debug, Clone)]
pub struct PrivateTransformContext {
    p_recip: APUFloat,
    q_recip: APUFloat,
    ipmq: APUInt,
}

impl PrivateKey<APUInt> {
    pub fn decrypt(&self, input: &[u8],
                   context: Option<PrivateTransformContext>)
                   -> (Vec<u8>, PrivateTransformContext) {
        assert!(self.n.n_bits >= 9);
        let context = context.unwrap_or_else(|| PrivateTransformContext {
            p_recip: self.p.recip(),
            q_recip: self.q.recip(),
            ipmq: &self.q - (&self.iqmp * &self.q - APUInt::one()) / &self.p % &self.q,
        });
        let mut result = input.chunks((self.n.n_bits + 7) / 8)
            .flat_map(|x| {
                let n = APUInt::from(x.chunks(8)
                    .map(|x| {
                        let mut num = [0u8; 8];
                        for (i, v) in x.iter().enumerate() {
                            num[i] = *v;
                        }
                        u64::from_le_bytes(num)
                    })
                    .collect::<Vec<_>>()
                );
                let a = n.fast_exponent_with_recip(&self.d, &self.p, &context.p_recip);
                let b = n.fast_exponent_with_recip(&self.d, &self.q, &context.q_recip);
                let d = (a * &self.q * &self.iqmp + b * &self.p * &context.ipmq) % &self.n;
                d.bits.iter()
                    .flat_map(|x| x.to_le_bytes().to_vec())
                    .chain(repeat(0u8))
                    .take((self.n.n_bits - 1) / 8)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<u8>>();
        let mut final_result = result.split_off(8);
        let mut size = [0u8; 8];
        for (i, v) in result.iter().enumerate() {
            size[i] = *v;
        }
        let size = u64::from_le_bytes(size) as usize;
        final_result.truncate(size);
        (final_result, context)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ap_uint_to_buffer() {
        let mut rng = rand::thread_rng();
        assert_eq!(parse_ap_uint(&to_buffer_ap_uint(&APUInt::zero())).unwrap().1, APUInt::zero());
        for i in 1..=128 {
            let between = Uniform::from(APUInt::min_bits(i)..=APUInt::max_bits(i));
            for _ in 0..10 {
                let number = between.sample(&mut rng);
                assert_eq!(parse_ap_uint(&to_buffer_ap_uint(&number)).unwrap().1, number);
            }
        }
    }

    #[test]
    fn test_transform() {
        let private_key = PrivateKey::<APUInt>::generate(
            128,
            32,
            num_cpus::get(),
            "".into(),
        );
        let public_key = private_key.get_public_key();
        for i in 0..64 {
            let text: Vec<u8> = (0..(96 + i)).map(|_| { rand::random::<u8>() }).collect();
            let encrypted = public_key.encrypt(&text, None).0;
            let decrypted = private_key.decrypt(&encrypted, None).0;
            assert_eq!(text, decrypted);
        }
    }
}