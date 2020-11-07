use std::ops::{Mul, MulAssign};
use crate::traits::{CountBits, TotalBits, Bits, Zero, One};
use crate::forward_ref_op_binary;
use crate::forward_ref_op_assign_and_binary;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct UFloat<BaseT, ExpT> {
    pub(crate) base: BaseT,
    pub(crate) exp: ExpT,
}

impl<BaseT, ExpT> Zero for UFloat<BaseT, ExpT>
    where
        BaseT: Zero, ExpT: Zero {
    fn zero() -> Self {
        Self {
            base: BaseT::zero(),
            exp: ExpT::zero(),
        }
    }

    fn is_zero(&self) -> bool {
        self.base.is_zero()
    }
}

impl<BaseT, ExpT> One for UFloat<BaseT, ExpT>
    where
        BaseT: One, ExpT: One {
    fn one() -> Self {
        Self {
            base: BaseT::one(),
            exp: ExpT::one(),
        }
    }

    fn is_one(&self) -> bool {
        self.base.is_one() && self.exp.is_one()
    }
}


macro_rules! impl_mul_for_small_primitive_ufloat {
    ($small:ty, $large:ty) => {
        impl Mul<&$small> for &UFloat<$small, isize> {
            type Output = UFloat<$small, isize>;

            fn mul(self, rhs: &$small) -> Self::Output {
                if *rhs == 0 {
                    return Self::Output { base: 0, exp: 0 };
                }
                let mut base = (self.base as $large) * (*rhs as $large);
                let exp = self.exp + base.count_bits() as isize - self.base.count_bits() as isize;
                loop {
                    base >>= base.trailing_zeros();
                    let bits = base.count_bits();
                    if bits <= <$small as TotalBits>::total_bits() { break; }
                    let extra_bits = bits - <$small as TotalBits>::total_bits();
                    let carry = base.get(extra_bits - 1);
                    base >>= extra_bits;
                    if carry { base += 1; }
                }
                UFloat{
                    base: base as $small,
                    exp,
                }
            }
        }
        forward_ref_op_assign_and_binary! {
            impl Mul, mul, impl MulAssign, mul_assign
            for UFloat<$small, isize>, $small, UFloat<$small, isize>
        }
    };
}

impl_mul_for_small_primitive_ufloat!(u8, u32);
impl_mul_for_small_primitive_ufloat!(u16, u32);
impl_mul_for_small_primitive_ufloat!(u32, u64);
impl_mul_for_small_primitive_ufloat!(u64, u128);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_small_mul() {
        // assert_eq!(UFloat { base: 1u32, exp: 1isize } * 0u32, UFloat { base: 0u32, exp: 0isize });
        // assert_eq!(UFloat { base: 5u32, exp: -1isize } * 11u32,
        //            UFloat { base: 55u32, exp: 2isize });
        // assert_eq!(UFloat { base: u32::MAX, exp: -1isize } * u32::MAX,
        //            UFloat { base: u32::MAX >> 1, exp: 31isize });
        assert_eq!(UFloat { base: 0b11111011u8, exp: 8isize } * 0b111u8,
                   UFloat { base: 0b110111u8, exp: 11isize });
    }
}
