use crate::traits::{One, TrailingZeros, FastExponentWithRecip};
use std::ops::{Sub, Shr, Add};
use std::collections::HashSet;
use rand::distributions::uniform::SampleUniform;
use rand::distributions::{Uniform, Distribution};
use std::hash::Hash;

pub trait IsPrimeMillerRabin where Self: SampleUniform {
    fn is_prime_miller_rabin(&self, times: usize) -> bool;
}

impl<T> IsPrimeMillerRabin for T
    where
        T: One + TrailingZeros + SampleUniform + Clone + Hash + Eq + FastExponentWithRecip,
        for<'a> &'a T: Add<&'a T, Output=T> + Sub<&'a T, Output=T> +
                       Shr<usize, Output=T>
{
    fn is_prime_miller_rabin(&self, times: usize) -> bool {
        // assert times <= self - 3
        let one = T::one();
        let two = &one + &one;
        let n_minus_1 = self - &one;
        let mut rng = rand::thread_rng();
        let between = Uniform::from(two.clone()..=(&n_minus_1 - &one));
        let r = n_minus_1.trailing_zeros();
        let d = &n_minus_1 >> r;
        let recip = self.recip();
        let mut checked = HashSet::new();
        'outer: for _ in 0..times {
            let mut a;
            loop {
                a = between.sample(&mut rng);
                if checked.insert(a.clone()) { break }
            }
            let mut x = a.fast_exponent_with_recip(&d, self, &recip);
            if x == one || x == n_minus_1 { continue; }
            for _ in 0..r {
                x = x.fast_exponent_with_recip(&two, self, &recip);
                if x == n_minus_1 { continue 'outer; }
            }
            return false
        }
        true
    }
}