pub trait MinBits {
    fn min_bits(n_bits: usize) -> Self;
}

pub trait MaxBits {
    fn max_bits(n_bits: usize) -> Self;
}

macro_rules! impl_min_for_primitive {
    ($($t:ty),*) => {
        $(impl MinBits for $t {
            fn min_bits(n_bits: usize) -> Self {
                if n_bits == 0 { 0 } else { (1 as $t) << (n_bits - 1) }
            }
        })*
    };
}

impl_min_for_primitive!{
    i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, usize, isize
}

macro_rules! impl_max_for_primitive {
    ($($t:ty),*) => {
        $(impl MaxBits for $t {
            fn max_bits(n_bits: usize) -> Self {
                if n_bits == 0 { 0 } else { !(!(0 as $t) << n_bits) }
            }
        })*
    };
}

impl_max_for_primitive!{
    i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, usize, isize
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_min_bits() {
        assert_eq!(<i32 as MinBits>::min_bits(0), 0i32);
        assert_eq!(<i32 as MinBits>::min_bits(1), 1i32);
        assert_eq!(<i32 as MinBits>::min_bits(2), 0b10i32);
        assert_eq!(<i32 as MinBits>::min_bits(10), 0b1000_000_000i32);
    }

    #[test]
    fn test_max_bits() {
        assert_eq!(<i32 as MaxBits>::max_bits(0), 0i32);
        assert_eq!(<i32 as MaxBits>::max_bits(1), 1i32);
        assert_eq!(<i32 as MaxBits>::max_bits(2), 0b11i32);
        assert_eq!(<i32 as MaxBits>::max_bits(10), 0b1111_111_111i32);
    }
}