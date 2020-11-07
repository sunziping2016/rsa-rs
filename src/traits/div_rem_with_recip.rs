use std::ops::{Mul, Sub, SubAssign, AddAssign};
use crate::traits::{Recip, One, ShiftFloor};

pub trait DivRemWithRecip where Self: Recip + Sized {
    fn div_rem_with_recip(&self, rhs: &Self, recip: &<Self as Recip>::Recip) -> (Self, Self);
}

impl<Integer, Float> DivRemWithRecip for Integer
    where
            Integer: Recip<Recip=Float> + One + Ord,
            for<'a> Integer: AddAssign<&'a Integer> + SubAssign<&'a Integer>,
            for<'a> &'a Integer: Mul<&'a Float, Output=Float> + Mul<&'a Integer, Output=Integer> +
                                 Sub<&'a Integer, Output=Integer>,
            for<'a> &'a Float: ShiftFloor<Output=Integer> {
    fn div_rem_with_recip(&self, rhs: &Self, recip: &Float) -> (Self, Self) {
        let mut div = (self * recip).floor();
        let mut rem = self - &(rhs * &div);
        while rem >= *rhs {
            rem -= rhs;
            div += &One::one();
        }
        (div, rem)
    }
}