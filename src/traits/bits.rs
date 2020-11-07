pub trait Bits {
    fn set(&mut self, bit: usize, value: bool);
    fn get(&self, bit: usize) -> bool;

    fn flip(&mut self, bit: usize) {
        self.set(bit, !self.get(bit));
    }
}

macro_rules! impl_bits_for_primitive {
    ($($t:ty),*) => {
        $(impl Bits for $t {
            fn set(&mut self, bit: usize, value: bool) {
                if value {
                    *self |= (1 as Self) << bit;
                } else {
                    *self &= !((1 as Self) << bit);
                }
            }
            fn get(&self, bit: usize) -> bool {
                ((self >> bit) & 1) == 1
            }
        })*
    };
}

impl_bits_for_primitive!{
    i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, usize, isize
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bits() {
        let mut a = 0b1011i32;
        a.set(1, true);
        assert_eq!(a, 0b1011i32);
        let mut a = 0b1011i32;
        a.set(2, true);
        assert_eq!(a, 0b1111i32);
        let mut a = 0b1011i32;
        a.set(1, false);
        assert_eq!(a, 0b1001i32);
        let mut a = 0b1011i32;
        a.set(2, false);
        assert_eq!(a, 0b1011i32);
        assert!(0b1011i32.get(1));
        assert!(!0b1011i32.get(2));
        let mut a = 0b1011i32;
        a.flip(1);
        assert_eq!(a, 0b1001i32);
        let mut a = 0b1011i32;
        a.flip(2);
        assert_eq!(a, 0b1111i32);
    }
}