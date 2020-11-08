use crate::traits::{One, Zero, DivRem};
use std::ops::{Mul, Add, Sub, Rem};

pub trait ModularInverse {
    fn modular_inverse(&self, n: &Self) -> (bool, Self);
}

impl<T> ModularInverse for T
    where
        T: One + Zero + Clone,
        for<'a> &'a T: Mul<&'a T, Output=T> + Add<&'a T, Output=T> + Sub<&'a T, Output=T> +
        Rem<&'a T, Output=T> + DivRem<&'a T, DivOutput=T, RemOutput=T> {
    fn modular_inverse(&self, n: &Self) -> (bool, Self) {
        let mut a = self.clone();
        let mut b = n.clone();
        let mut u = T::one();
        let mut e = T::zero();
        while !b.is_zero() {
            let (q, r) = a.div_rem(&b);
            a = b;
            b = r;
            let temp_e = &(&u + &(&q * &(n - &e))) % n;
            u = e;
            e = temp_e;
        }
        (a.is_one(), u)
    }
}