pub trait Zero: Sized {
    fn zero() -> Self;
    fn is_zero(&self) -> bool;
}

pub trait One: Sized {
    fn one() -> Self;
    fn is_one(&self) -> bool;
}

macro_rules! impl_value_for_primitive {
    ($v:literal, impl $value:ident, $is_value:ident for $u:ty, $($t:ty),*) => {
        $(impl $u for $t {
            fn $value() -> Self {
                $v
            }
            fn $is_value(&self) -> bool {
                *self == $v
            }
        })*
    };
}

impl_value_for_primitive!{
    0, impl zero, is_zero for Zero, i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, usize, isize
}
impl_value_for_primitive!{
    0.0, impl zero, is_zero for Zero, f32, f64
}

impl_value_for_primitive!{
    1, impl one, is_one for One, i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, usize, isize
}
impl_value_for_primitive!{
    1.0, impl one, is_one for One, f32, f64
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero() {
        assert_eq!(<i32 as Zero>::zero(), 0i32);
    }

    #[test]
    fn test_one() {
        assert_eq!(<i32 as One>::one(), 1i32);
    }

    #[test]
    fn test_is_zero() {
        assert!(0.is_zero());
        assert!(!1.is_zero());
    }

    #[test]
    fn test_is_one() {
        assert!(!0.is_one());
        assert!(1.is_one());
    }
}