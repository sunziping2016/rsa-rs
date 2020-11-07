pub trait TrailingZeros {
    fn trailing_zeros(&self) -> usize;
}

macro_rules! impl_trailing_zeros_for_primitive {
    ($($t:ty),*) => {
        $(impl TrailingZeros for $t {
            fn trailing_zeros(&self) -> usize {
                <$t>::trailing_zeros(*self) as usize
            }
        })*
    };
}

impl_trailing_zeros_for_primitive! {
    i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, isize, usize
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trailing_zeros() {
        assert_eq!(TrailingZeros::trailing_zeros(&0b100), 2usize);
        assert_eq!(TrailingZeros::trailing_zeros(&0b0), 32usize);
    }
}