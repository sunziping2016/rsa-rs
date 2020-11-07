pub trait CountBits {
    fn total_bits() -> usize;
    fn count_bits(&self) -> usize;
}

macro_rules! impl_count_bits_for_primitive {
    ($v:literal, $($t:ty),*) => {
        $(impl CountBits for $t {
            fn total_bits() -> usize {
                $v
            }
            fn count_bits(&self) -> usize {
                $v - self.leading_zeros() as usize
            }
        })*
    };
}

impl_count_bits_for_primitive!{ 8, u8 }
impl_count_bits_for_primitive!{ 16, u16 }
impl_count_bits_for_primitive!{ 32, u32 }
impl_count_bits_for_primitive!{ 64, u64 }
impl_count_bits_for_primitive!{ 128, u128 }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_total_bits() {
        assert_eq!(<u32 as CountBits>::total_bits(), 32usize);
    }

    #[test]
    fn test_count_bits() {
        assert_eq!(0u32.count_bits(), 0usize);
        assert_eq!(1u32.count_bits(), 1usize);
        assert_eq!(0b100u32.count_bits(), 3usize);
        assert_eq!(u32::MAX.count_bits(), 32usize);
    }
}