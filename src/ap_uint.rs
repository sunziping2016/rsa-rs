use std::ops::{AddAssign, Add, SubAssign, Sub, MulAssign, Mul};
use std::cmp::Ordering;
use std::iter::repeat;

// implements "T op= &U", "T op= U", "&T op U", "T op &U", "T op U"
// based on "&T op &U"
macro_rules! forward_ref_op_assign_and_binary {
    (impl $binary_imp:ident, $binary_method:ident,
     impl $assign_imp:ident, $assign_method:ident for $t:ty, $u:ty, $v:ty,
     $( #[$attr:meta] )*) => {
        $(#[$attr])*
        impl $assign_imp<&$u> for $t {
            #[inline]
            fn $assign_method(&mut self, rhs: &$u) {
                *self = $binary_imp::$binary_method(&*self, rhs);
            }
        }
        $(#[$attr])*
        impl $assign_imp<$u> for $t {
            #[inline]
            fn $assign_method(&mut self, rhs: $u) {
                $assign_imp::$assign_method(self, &rhs);
            }
        }

        $(#[$attr])*
        impl $binary_imp<$u> for &$t {
            type Output = $v;
            #[inline]
            fn $binary_method(self, other: $u) -> $v {
                $binary_imp::$binary_method(self, &other)
            }
        }
        $(#[$attr])*
        impl $binary_imp<&$u> for $t {
            type Output = $v;
            #[inline]
            fn $binary_method(self, other: &$u) -> $v {
                $binary_imp::$binary_method(&self, other)
            }
        }

        $(#[$attr])*
        impl $binary_imp<$u> for $t {
            type Output = $v;
            #[inline]
            fn $binary_method(self, other: $u) -> $v {
                $binary_imp::$binary_method(&self, &other)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct APUint {
    n_bits: usize,
    bits: Vec<u64>,
}

impl APUint {
    pub fn max(n_bits: usize) -> Self {
        let mut bits = vec![u64::MAX; n_bits / 64];
        let extra_n_bits = n_bits % 64;
        if extra_n_bits > 0 {
            bits.push((1u64 << extra_n_bits) - 1);
        }
        Self {
            n_bits,
            bits,
        }
    }

    pub fn min(n_bits: usize) -> Self {
        if n_bits == 0 {
            return Self::default();
        }
        let mut bits = vec![0; (n_bits - 1) / 64];
        bits.push(1u64 << (n_bits - 1) % 64);
        Self {
            n_bits,
            bits,
        }
    }
}

impl Default for APUint {
    fn default() -> Self {
        Self {
            n_bits: 0,
            bits: Vec::new(),
        }
    }
}

impl Ord for APUint {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.n_bits.cmp(&other.n_bits) {
            Ordering::Equal => self.bits.iter().rev()
                .zip(other.bits.iter().rev())
                .map(|(x, y)| x.cmp(y))
                .find(|x| !matches!(x, Ordering::Equal))
                .unwrap_or(Ordering::Equal),
            order => order,
        }
    }
}

impl PartialOrd for APUint {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for APUint {
    fn eq(&self, other: &Self) -> bool {
        matches!(self.cmp(other), Ordering::Equal)
    }
}

impl Eq for APUint {}

impl From<Vec<u64>> for APUint {
    fn from(mut bits: Vec<u64>) -> Self {
        while let Some(0u64) = bits.last() {
            bits.pop();
        }
        let n_bits = match bits.last() {
            Some(n) => 64 * bits.len() - n.leading_zeros() as usize,
            None => 0usize,
        };
        return Self {
            n_bits,
            bits,
        }
    }
}

#[macro_export]
macro_rules! ap_uint {
    ( $($x: expr),* ) => {APUint::from(vec![$($x),*])};
}

impl Add<&APUint> for &APUint {
    type Output = APUint;

    fn add(self, rhs: &APUint) -> Self::Output {
        #[cfg(target_arch = "x86")]
        use core::arch::x86::_addcarry_u64;
        #[cfg(target_arch = "x86_64")]
        use core::arch::x86_64::_addcarry_u64;
        let mut carry = 0u8;
        let mut bits = vec![0; self.bits.len().max(rhs.bits.len()) + 1];
        for ((left, right), out) in self.bits.iter().chain(repeat(&0u64))
            .zip(rhs.bits.iter().chain(repeat(&0u64)))
            .zip(bits.iter_mut()) {
            unsafe { carry = _addcarry_u64(carry, left.clone(), right.clone(), out); }
        }
        APUint::from(bits)
    }
}

forward_ref_op_assign_and_binary! {
    impl Add, add, impl AddAssign, add_assign for APUint, APUint, APUint,
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
}

#[cfg(target_arch = "x86_64")]
impl Sub<&APUint> for &APUint {
    type Output = APUint;

    fn sub(self, rhs: &APUint) -> Self::Output {
        use core::arch::x86_64::_subborrow_u64;
        assert!(self.bits.len() >= rhs.bits.len(), "unsigned integer subtraction underflow");
        let mut borrow = 0u8;
        let mut bits = vec![0; self.bits.len()];
        for ((left, right), out) in self.bits.iter()
            .zip(rhs.bits.iter().chain(repeat(&0u64)))
            .zip(bits.iter_mut()) {
            unsafe { borrow = _subborrow_u64(borrow, left.clone(), right.clone(), out); }
        }
        assert_eq!(borrow, 0, "unsigned integer subtraction underflow");
        APUint::from(bits)
    }
}

forward_ref_op_assign_and_binary! {
    impl Sub, sub, impl SubAssign, sub_assign for APUint, APUint, APUint,
    #[cfg(target_arch = "x86_64")]
}

#[cfg(target_arch = "x86_64")]
impl Mul<&APUint> for &APUint {
    type Output = APUint;

    fn mul(self, rhs: &APUint) -> Self::Output {
        use core::arch::x86_64::_addcarry_u64;
        use core::arch::x86_64::_mulx_u64;
        let mut bits = vec![0; self.bits.len() + rhs.bits.len()];
        for (offset, b) in rhs.bits.iter().enumerate() {
            let mut temp = vec![0; self.bits.len() + 1];
            let mut carry = 0u8;
            let mut high = 0u64;
            for (a, out) in self.bits.iter().chain(repeat(&0u64))
                .zip(temp.iter_mut()) {
                unsafe {
                    let old_high = high;
                    let low = _mulx_u64(a.clone(), b.clone(), &mut high);
                    carry = _addcarry_u64(carry, old_high, low, out);
                }
            }
            for (c, out) in temp.iter()
                .zip(bits.iter_mut().skip(offset)) {
                unsafe { carry = _addcarry_u64(carry, out.clone(), c.clone(), out); }
            }
        }
        APUint::from(bits)
    }
}

forward_ref_op_assign_and_binary! {
    impl Mul, mul, impl MulAssign, mul_assign for APUint, APUint, APUint,
    #[cfg(target_arch = "x86_64")]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default() {
        let default = APUint::default();
        assert_eq!(default.n_bits, 0);
        assert_eq!(default.bits, Vec::new());
    }

    #[test]
    fn test_from() {
        let number1 = APUint::from(Vec::new());
        assert_eq!(number1.n_bits, 0);
        assert_eq!(number1.bits, Vec::new());
        let number2 = ap_uint![0b100u64, 0b1000u64, 0, 0];
        assert_eq!(number2.n_bits, 64 + 4);
        assert_eq!(number2.bits, vec![0b100u64, 0b1000u64]);
    }

    #[test]
    fn test_equal() {
        assert_eq!(APUint::default(), ap_uint![0]);
        assert_eq!(ap_uint![1, 1], ap_uint![1, 1]);
        assert_ne!(APUint::default(), ap_uint![0, 1]);
        assert_ne!(ap_uint![0, 1], APUint::default());
        assert_ne!(ap_uint![1], ap_uint![1, 1]);
        assert_ne!(ap_uint![1, 1], ap_uint![1]);
        assert_ne!(ap_uint![1, 2], ap_uint![1, 1]);
    }

    #[test]
    fn test_less() {
        assert!(!(APUint::default() < APUint::default()));
        assert!(APUint::default() <= APUint::default());
        assert!(APUint::default() < ap_uint![1]);
        assert!(APUint::default() <= ap_uint![1]);
        assert!(ap_uint![1] < ap_uint![0, 1]);
        assert!(!(ap_uint![1, 1] < ap_uint![0, 1]));
        assert!(!(ap_uint![0, 0, 1] < ap_uint![0, 1]));
        assert!(ap_uint![0, 0, 1] < ap_uint![0, 1, 1]);
        assert!(ap_uint![0, 1, 1] < ap_uint![1, 1, 1]);
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[test]
    fn test_add() {
        assert_eq!(APUint::default() + APUint::default(), APUint::default());
        assert_eq!(APUint::default() + ap_uint![100, 20], ap_uint![100, 20]);
        assert_eq!(ap_uint![100] + ap_uint![100, 20], ap_uint![200, 20]);
        assert_eq!(ap_uint![1u64 << 63] + ap_uint![1u64 << 63], ap_uint![0, 1]);
        assert_eq!(ap_uint![1u64 << 63, 20] + ap_uint![1u64 << 63, 20], ap_uint![0, 41]);
    }

    #[test]
    fn test_max() {
        assert_eq!(APUint::max(0), APUint::default());
        assert_eq!(APUint::max(3), ap_uint![0b111]);
        assert_eq!(APUint::max(64), ap_uint![u64::MAX]);
        assert_eq!(APUint::max(129), ap_uint![u64::MAX, u64::MAX, 1]);
    }

    #[test]
    fn test_min() {
        assert_eq!(APUint::min(0), APUint::default());
        assert_eq!(APUint::min(3), ap_uint![0b100]);
        assert_eq!(APUint::min(64), ap_uint![1u64 << 63]);
        assert_eq!(APUint::min(129), ap_uint![0, 0, 1]);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_sub() {
        assert_eq!(APUint::default() - APUint::default(), APUint::default());
        assert_eq!(ap_uint![20, 100] - APUint::default(), ap_uint![20, 100]);
        assert_eq!(ap_uint![20, 100] - ap_uint![20, 100], APUint::default());
        assert_eq!(ap_uint![20, 100] -  ap_uint![19], ap_uint![1, 100]);
        assert_eq!(ap_uint![20, 100] -  ap_uint![21], ap_uint![u64::MAX, 99]);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    #[should_panic(expected = "unsigned integer subtraction underflow")]
    fn test_sub_panic1() {
        let mut a = ap_uint![0b100];
        a -= ap_uint![0b1001];
        println!("{:?}", a);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    #[should_panic(expected = "unsigned integer subtraction underflow")]
    fn test_sub_panic2() {
        let mut a = ap_uint![0b100];
        a -= ap_uint![0b101];
    }

    #[test]
    fn test_mul() {
        assert_eq!(APUint::default() * APUint::default(), APUint::default());
        assert_eq!(APUint::default() * ap_uint![123], APUint::default());
        assert_eq!(ap_uint![123] * APUint::default(), APUint::default());
        assert_eq!(ap_uint![5, 6] * ap_uint![7, 8], ap_uint![5 * 7, 5 * 8 + 6 * 7, 6 * 8]);
        assert_eq!(APUint::max(128) * APUint::max(64),
                   APUint::min(129) * APUint::min(65)
                       - APUint::min(129) - APUint::min(65) + ap_uint![1]);
    }
}
