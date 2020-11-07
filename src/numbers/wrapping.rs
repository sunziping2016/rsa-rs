use crate::traits::{One, Zero, MinBits, MaxBits, Bits, DivRem, CountBits, TotalBits};
use std::cmp::Ordering;
use std::ops::{AddAssign, Add, SubAssign, Sub, MulAssign, Mul, Shl, ShlAssign, Shr, ShrAssign, Div, DivAssign, Rem, RemAssign};
use crate::forward_ref_op_binary;
use crate::forward_ref_op_assign_and_binary;

#[derive(Debug)]
pub struct Wrapping<T>(pub T);

impl<T> Ord for Wrapping<T> where T: Ord {
    fn cmp(&self, other: &Self) -> Ordering { self.0.cmp(&other.0) }
}

impl<T> PartialOrd for Wrapping<T> where T: PartialOrd {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { self.0.partial_cmp(&other.0) }
}

impl<T> PartialEq for Wrapping<T> where T: PartialEq {
    fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) }
}

impl<T> Eq for Wrapping<T> where T: Eq {}

impl<T> Zero for Wrapping<T> where T: Zero {
    fn zero() -> Self {
        Wrapping(T::zero())
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<T> One for Wrapping<T> where T: One {
    fn one() -> Self {
        Wrapping(T::one())
    }

    fn is_one(&self) -> bool {
        self.0.is_one()
    }
}

impl<T> MinBits for Wrapping<T> where T: MinBits {
    fn min_bits(n_bits: usize) -> Self {
        Wrapping(T::min_bits(n_bits))
    }
}

impl<T> MaxBits for Wrapping<T> where T: MaxBits {
    fn max_bits(n_bits: usize) -> Self {
        Wrapping(T::max_bits(n_bits))
    }
}

impl<T> Bits for Wrapping<T> where T: Bits {
    fn set(&mut self, bit: usize, value: bool) {
        self.0.set(bit, value)
    }

    fn get(&self, bit: usize) -> bool {
        self.0.get(bit)
    }
}

macro_rules! forward_wrapping_op_assign_and_binary {
    ($binary_imp: ident, $binary_method: ident,
    $assign_imp: ident, $assign_method: ident) => {
        impl<T, Rhs> $binary_imp<&Wrapping<Rhs>> for &Wrapping<T>
            where
                T: $binary_imp<Rhs> + Copy,
                Rhs: Copy {
            type Output = Wrapping<<T as $binary_imp<Rhs>>::Output>;

            fn $binary_method(self, rhs: &Wrapping<Rhs>) -> Self::Output {
                Wrapping(self.0.$binary_method(rhs.0))
            }
        }
        forward_ref_op_assign_and_binary! {
           impl<T, Rhs> $binary_imp, $binary_method, impl $assign_imp, $assign_method
           for Wrapping<T>, Wrapping<Rhs>, Wrapping<T>
           where [T: $binary_imp<Rhs, Output=T> + Copy, Rhs: Copy]
        }
    };
}

forward_wrapping_op_assign_and_binary! { Add, add, AddAssign, add_assign }
forward_wrapping_op_assign_and_binary! { Sub, sub, SubAssign, sub_assign }
forward_wrapping_op_assign_and_binary! { Mul, mul, MulAssign, mul_assign }
forward_wrapping_op_assign_and_binary! { Shl, shl, ShlAssign, shl_assign }
forward_wrapping_op_assign_and_binary! { Shr, shr, ShrAssign, shr_assign }
forward_wrapping_op_assign_and_binary! { Div, div, DivAssign, div_assign }
forward_wrapping_op_assign_and_binary! { Rem, rem, RemAssign, rem_assign }

impl<T, Rhs, DivOutput, RemOutput> DivRem<Wrapping<Rhs>> for Wrapping<T>
    where
        T: Copy + Div<Rhs, Output=DivOutput> + Rem<Rhs, Output=RemOutput>,
        Rhs: Copy {
    type DivOutput = Wrapping<DivOutput>;
    type RemOutput = Wrapping<RemOutput>;

    fn div_rem(self, rhs: Wrapping<Rhs>) -> (Self::DivOutput, Self::RemOutput) {
        (Wrapping(self.0.div(rhs.0)), Wrapping(self.0.rem(rhs.0)))
    }
}
impl<T> TotalBits for Wrapping<T> where T: TotalBits {
    fn total_bits() -> usize {
        T::total_bits()
    }
}

impl<T> CountBits for Wrapping<T> where T: CountBits {
    fn count_bits(&self) -> usize {
        self.0.count_bits()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_div_rem() {
        assert_eq!(Wrapping(5i32).div_rem(Wrapping(2i32)),
                   (Wrapping(2i32), Wrapping(1i32)));
    }
}