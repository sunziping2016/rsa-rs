use crate::traits::{Recip, DivRemWithRecip, Zero, One, Bits, CountBits};
use std::cmp::Ordering;
use std::ops::Mul;

pub trait FastExponentWithRecip where Self: Recip {
    fn fast_exponent_with_recip(&self, exponent: &Self, divider: &Self,
                                recip: &<Self as Recip>::Recip) -> Self;
}

impl<T> FastExponentWithRecip for T
    where
        T: Recip + Ord + Zero + One + Bits + Clone + CountBits + DivRemWithRecip,
        for<'a> &'a T: Mul<&'a T, Output=T> {
    fn fast_exponent_with_recip(&self, exponent: &Self, divider: &Self,
                                recip: &<Self as Recip>::Recip) -> Self {
        let mut basis = match self.cmp(divider) {
            Ordering::Less => self.clone(),
            Ordering::Equal => return Zero::zero(),
            Ordering::Greater => self.div_rem_with_recip(divider, recip).1,
        };
        let mut result = <T as One>::one();
        let count_bits = exponent.count_bits();
        for i in 0..count_bits {
            if exponent.get(i) {
                result = (&basis * &result).div_rem_with_recip(divider, recip).1;
            }
            basis = (&basis * &basis).div_rem_with_recip(divider, recip).1;
        }
        result
    }
}
