use crate::numbers::{UFloat, APUInt};
use std::ops::{Mul, MulAssign};
use crate::traits::{Zero, ShiftFloor, CountBits};
use crate::forward_ref_op_binary;
use crate::forward_ref_op_assign_and_binary;
use std::cmp::Ordering;

pub type APUFloat = UFloat<APUInt, isize>;

#[cfg(target_arch = "x86_64")]
impl Mul<&APUInt> for &APUFloat {
    type Output = APUFloat;

    fn mul(self, rhs: &APUInt) -> Self::Output {
        if rhs.is_zero() {
            return APUFloat::zero();
        }
        let base = &self.base * rhs;
        let exp = self.exp + base.count_bits() as isize - self.base.count_bits() as isize;
        APUFloat { base, exp }
    }
}

forward_ref_op_assign_and_binary! {
    #[cfg(target_arch = "x86_64")]
    impl Mul, mul, impl MulAssign, mul_assign for APUFloat, APUInt, APUFloat
}

impl ShiftFloor for &APUFloat {
    type Output = APUInt;

    fn shift_floor(self, shift: isize) -> Self::Output {
        let real_shift = self.base.n_bits as isize + shift - self.exp as isize;
        match real_shift.cmp(&0isize) {
            Ordering::Greater => &self.base >> real_shift as usize,
            Ordering::Equal => self.base.clone(),
            Ordering::Less => &self.base << (-real_shift) as usize,
        }
    }
}

#[cfg(target_arch = "x86_64")]
impl Mul<&APUFloat> for &APUInt {
    type Output = APUFloat;

    fn mul(self, rhs: &APUFloat) -> Self::Output {
        rhs.mul(self)
    }
}

forward_ref_op_binary! {
    #[cfg(target_arch = "x86_64")]
    impl Mul, mul for APUInt, APUFloat, APUFloat
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ap_uint;

    #[test]
    fn test_shift_round() {
        assert_eq!(APUFloat { base: ap_uint!(0b1001), exp: -3isize }.shift_floor(-6),
                   ap_uint!(0b100));
        assert_eq!(APUFloat { base: ap_uint!(0b1001), exp: -3isize }.shift_floor(-7),
                   ap_uint!(0b1001));
        assert_eq!(APUFloat { base: ap_uint!(0b1001), exp: -3isize }.shift_floor(-8),
                   ap_uint!(0b10010));
    }
}