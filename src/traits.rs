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

pub trait RemWithRecip where Self: Recip {
    fn rem_with_recip(&self, rhs: &Self, recip: &<Self as Recip>::Recip) -> Self;
}

impl<T> RemWithRecip for T
    where
            for<'a> T: Ord + Recip + SubAssign<&'a T>,
            for<'a> &'a T: Mul<&'a <T as Recip>::Recip, Output=T> +
            Mul<&'a T, Output=T> + Sub<&'a T, Output=T> {
    fn rem_with_recip(&self, rhs: &Self, recip: &<Self as Recip>::Recip) -> Self {
        let mut rem = self - &(&(self * recip) * rhs);
        while rem >= *rhs {
            rem -= rhs;
        }
        rem
    }
}

pub trait DivRemWithRecip where Self: Recip + Sized {
    fn div_rem_with_recip(&self, rhs: &Self, recip: &<Self as Recip>::Recip) -> (Self, Self);
}

impl<T> DivRemWithRecip for T
    where
            for<'a> T: Ord + Recip + SubAssign<&'a T> + One + AddAssign<&'a T>,
            for<'a> &'a T: Mul<&'a <T as Recip>::Recip, Output=T> +
            Mul<&'a T, Output=T> + Sub<&'a T, Output=T> {
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
