use std::ops::{Mul, Sub, SubAssign, AddAssign};

pub trait Recip {
    type Recip;

    fn recip(&self) -> Self::Recip;
}

pub trait Zero: Sized {
    fn zero() -> Self;
}

pub trait One: Sized {
    fn one() -> Self;
}

pub trait RemWithRecip
    where
        for<'a> Self: Sized + Ord + Recip + SubAssign<&'a Self>,
        for<'a> &'a Self: Mul<&'a <Self as Recip>::Recip, Output=Self> +
            Mul<&'a Self, Output=Self> + Sub<&'a Self, Output=Self>  {

    fn rem_with_recip(&self, rhs: &Self, recip: &<Self as Recip>::Recip) -> Self {
        let mut rem = self - &(&(self * recip) * rhs);
        while rem >= *rhs {
            rem -= rhs;
        }
        rem
    }
}

pub trait DivRemWithRecip: RemWithRecip
    where
            for<'a> Self: One + AddAssign<&'a Self>,
            for<'a> &'a Self: Mul<&'a <Self as Recip>::Recip, Output=Self> +
            Mul<&'a Self, Output=Self> + Sub<&'a Self, Output=Self> {
    fn div_rem_with_recip(&self, rhs: &Self, recip: &<Self as Recip>::Recip) -> (Self, Self) {
        let mut div = self * recip;
        let mut rem = self - &(&div * rhs);
        while rem >= *rhs {
            rem -= rhs;
            div += &One::one();
        }
        (div, rem)
    }
}