use std::ops::{AddAssign, Add, SubAssign, Sub, MulAssign, Mul, Shl, ShlAssign, Shr, ShrAssign, Div, DivAssign, Rem, RemAssign};
use std::cmp::Ordering;
use std::iter::{repeat, once};
use crate::traits::{Recip, One, Zero, MinBits, MaxBits, Bits, DivRem, RecipWithPrecision, TrailingZeros, CountBits};
use crate::forward_ref_op_binary;
use crate::forward_ref_op_assign_and_binary;
use crate::numbers::APUFloat;
use rand::Rng;
use rand::distributions::uniform::{UniformSampler, SampleUniform, SampleBorrow};
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone)]
pub struct APUInt {
    pub(crate) n_bits: usize,
    pub(crate) bits: Vec<u64>,
}

impl Hash for APUInt {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bits.hash(state)
    }
}

impl CountBits for APUInt {
    fn count_bits(&self) -> usize { self.n_bits }
}

impl TrailingZeros for APUInt {
    fn trailing_zeros(&self) -> usize {
        let mut count = 0usize;
        for chunk in self.bits.iter() {
            match chunk {
                0u64 => count += 64usize,
                x => {
                    count += x.trailing_zeros() as usize;
                    break;
                }
            }
        }
        count
    }
}

impl From<Vec<u64>> for APUInt {
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

impl From<u64> for APUInt {
    fn from(value: u64) -> Self {
        Self::from(vec![value])
    }
}

impl From<APUInt> for u64 {
    fn from(value: APUInt) -> Self {
        value.bits.first().unwrap_or(&0u64).clone()
    }
}

#[macro_export]
macro_rules! ap_uint {
    ( $($x: expr),* ) => {APUInt::from(vec![$($x),*])};
}

impl Ord for APUInt {
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

impl PartialOrd for APUInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for APUInt {
    fn eq(&self, other: &Self) -> bool {
        matches!(self.cmp(other), Ordering::Equal)
    }
}

impl Eq for APUInt {}

impl Zero for APUInt {
    fn zero() -> Self {
        Self {
            n_bits: 0,
            bits: Vec::new(),
        }
    }

    fn is_zero(&self) -> bool {
        self.n_bits == 0
    }
}

impl One for APUInt {
    fn one() -> Self {
        ap_uint!(1)
    }

    fn is_one(&self) -> bool {
        self.n_bits == 1
    }
}

impl MinBits for APUInt {
    fn min_bits(n_bits: usize) -> Self {
        if n_bits == 0 {
            return Self::zero();
        }
        let mut bits = vec![0; (n_bits - 1) / 64];
        bits.push(1u64 << (n_bits - 1) % 64);
        Self {
            n_bits,
            bits,
        }
    }
}

impl MaxBits for APUInt {
    fn max_bits(n_bits: usize) -> Self {
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
}

impl Bits for APUInt {
    fn set(&mut self, bit: usize, value: bool) {
        let pos = bit / 64;
        if value {
            if pos >= self.bits.len() {
                self.bits.resize(pos + 1, 0u64);
            }
            self.bits[pos] |= 1 << (bit % 64);
        } else if bit < self.n_bits {
            self.bits[pos] &= !(1 << (bit % 64));
        }
        while let Some(0u64) = self.bits.last() {
            self.bits.pop();
        }
        self.n_bits = match self.bits.last() {
            Some(n) => 64 * self.bits.len() - n.leading_zeros() as usize,
            None => 0usize,
        };
    }

    fn get(&self, bit: usize) -> bool {
        if bit < self.n_bits {
            ((self.bits[bit / 64] >> (bit % 64)) & 1) == 1
        } else {
            false
        }
    }
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
impl Add<&APUInt> for &APUInt {
    type Output = APUInt;

    fn add(self, rhs: &APUInt) -> Self::Output {
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
        APUInt::from(bits)
    }
}

forward_ref_op_assign_and_binary! {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    impl Add, add, impl AddAssign, add_assign for APUInt, APUInt, APUInt
}

#[cfg(target_arch = "x86_64")]
impl Sub<&APUInt> for &APUInt {
    type Output = APUInt;

    fn sub(self, rhs: &APUInt) -> Self::Output {
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
        APUInt::from(bits)
    }
}

forward_ref_op_assign_and_binary! {
    #[cfg(target_arch = "x86_64")]
    impl Sub, sub, impl SubAssign, sub_assign for APUInt, APUInt, APUInt
}

#[cfg(target_arch = "x86_64")]
impl Mul<&APUInt> for &APUInt {
    type Output = APUInt;

    fn mul(self, rhs: &APUInt) -> Self::Output {
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
        APUInt::from(bits)
    }
}

forward_ref_op_assign_and_binary! {
    #[cfg(target_arch = "x86_64")]
    impl Mul, mul, impl MulAssign, mul_assign for APUInt, APUInt, APUInt
}

impl Shl<&usize> for &APUInt {
    type Output = APUInt;

    fn shl(self, rhs: &usize) -> Self::Output {
        if self.is_zero() {
            return APUInt::zero();
        }
        let left_shift = rhs % 64;
        let bits = if left_shift == 0 {
            repeat(0u64).take(rhs / 64).chain(
                self.bits.iter().map(u64::clone)
            ).collect::<Vec<_>>()
        } else {
            let right_shift = 64 - left_shift;
            repeat(0u64).take(rhs / 64).chain(
                once(&0u64).chain(self.bits.iter())
                    .zip(self.bits.iter().chain(once(&0u64)))
                    .map(|(x, y)| (x >> right_shift) | y << left_shift)
            ).collect()
        };
        APUInt::from(bits)
    }
}

forward_ref_op_assign_and_binary! {
    impl Shl, shl, impl ShlAssign, shl_assign for APUInt, usize, APUInt
}

impl Shr<&usize> for &APUInt {
    type Output = APUInt;

    fn shr(self, rhs: &usize) -> Self::Output {
        if self.n_bits <= *rhs {
            return APUInt::zero();
        }
        let right_shift = rhs % 64;
        let bits = if right_shift == 0 {
            self.bits.iter().skip(rhs / 64)
                .map(u64::clone)
                .collect::<Vec<_>>()
        } else {
            let left_shift = 64 - right_shift;
            self.bits.iter().skip(rhs / 64)
                .zip(self.bits.iter().skip(rhs / 64 + 1).chain(once(&0u64)))
                .map(|(x, y)| (x >> right_shift) | (y << left_shift))
                .collect()
        };
        APUInt::from(bits)
    }
}

forward_ref_op_assign_and_binary! {
    impl Shr, shr, impl ShrAssign, shr_assign for APUInt, usize, APUInt
}

#[cfg(target_arch = "x86_64")]
impl DivRem for &APUInt {
    type DivOutput = APUInt;
    type RemOutput = APUInt;

    fn div_rem(self, rhs: &APUInt) -> (APUInt, APUInt) {
        assert!(!rhs.is_zero(), "division by zero");
        let mut q = APUInt::zero();
        let mut r = APUInt::zero();
        for i in (0..self.n_bits).rev() {
            r <<= 1;
            r.set(0, self.get(i));
            if r >= *rhs {
                r -= rhs;
                q.set(i, true);
            }
        }
        (q, r)
    }
}

forward_ref_op_binary! {
    impl DivRem, div_rem for APUInt, APUInt, (APUInt, APUInt) {
        type DivOutput = APUInt;
        type RemOutput = APUInt;
    }
}

#[cfg(target_arch = "x86_64")]
impl Div<&APUInt> for &APUInt {
    type Output = APUInt;

    fn div(self, rhs: &APUInt) -> Self::Output {
        self.div_rem(rhs).0
    }
}

#[cfg(target_arch = "x86_64")]
impl Rem<&APUInt> for &APUInt {
    type Output = APUInt;

    fn rem(self, rhs: &APUInt) -> Self::Output {
        self.div_rem(rhs).1
    }
}

forward_ref_op_assign_and_binary! {
    #[cfg(target_arch = "x86_64")]
    impl Div, div, impl DivAssign, div_assign for APUInt, APUInt, APUInt
}

forward_ref_op_assign_and_binary! {
    #[cfg(target_arch = "x86_64")]
    impl Rem, rem, impl RemAssign, rem_assign for APUInt, APUInt, APUInt
}

#[cfg(target_arch = "x86_64")]
impl RecipWithPrecision for APUInt {
    type Recip = APUFloat;

    fn recip_with_precision(&self, precision: usize) -> Self::Recip {
        // Newton-Raphson Division
        assert!(!self.is_zero(), "division by zero");
        let total_bits = self.n_bits + precision;
        let one = APUInt::min_bits(total_bits + 1);
        let mut x = APUInt::min_bits(precision + 1);
        loop {
            let mul = self * &x;
            let origin_delta = &x * (&one - mul);
            let delta_x = &origin_delta >> total_bits;
            if delta_x.is_zero() { break; }
            x += delta_x
        }
        let exp = x.count_bits() as isize - total_bits as isize;
        x >>= x.trailing_zeros();
        Self::Recip {
            base: x,
            exp,
        }
    }
}

#[cfg(target_arch = "x86_64")]
impl Recip for APUInt {
    type Recip = APUFloat;

    fn recip(&self) -> Self::Recip {
        self.recip_with_precision(self.n_bits)
    }
}

pub trait RandAPUInt {
    fn gen_ap_uint(&mut self, bit_size: usize) -> APUInt;
    fn gen_ap_uint_below(&mut self, bound: &APUInt) -> APUInt;
    fn gen_ap_uint_range(&mut self, lbound: &APUInt, ubound: &APUInt) -> APUInt;
}

impl<R: Rng + ?Sized> RandAPUInt for R {
    fn gen_ap_uint(&mut self, bit_size: usize) -> APUInt {
        if bit_size == 0 {
            return APUInt::zero();
        }
        let mut bits = vec![0; (bit_size - 1) / 64 + 1];
        self.fill(&mut bits[..]);
        let rem = (bit_size % 64) as u64;
        if rem > 0 {
            *bits.last_mut().unwrap() >>= 64 - rem;
        }
        APUInt::from(bits)
    }

    fn gen_ap_uint_below(&mut self, bound: &APUInt) -> APUInt {
        assert!(!bound.is_zero(), "cannot generate number smaller than 0");
        let bits = bound.count_bits();
        loop {
            let n = self.gen_ap_uint(bits);
            if n < *bound {
                return n;
            }
        }
    }

    fn gen_ap_uint_range(&mut self, lbound: &APUInt, ubound: &APUInt) -> APUInt {
        assert!(*lbound < *ubound);
        if lbound.is_zero() {
            self.gen_ap_uint_below(ubound)
        } else {
            lbound + self.gen_ap_uint_below(&(ubound - lbound))
        }
    }
}

#[derive(Clone, Debug)]
pub struct UniformAPUInt {
    base: APUInt,
    len: APUInt,
}

impl UniformSampler for UniformAPUInt {
    type X = APUInt;

    fn new<B1, B2>(low_b: B1, high_b: B2) -> Self
        where
            B1: SampleBorrow<Self::X> + Sized,
            B2: SampleBorrow<Self::X> + Sized {
        let low = low_b.borrow();
        let high = high_b.borrow();
        assert!(low < high);
        UniformAPUInt {
            len: high - low,
            base: low.clone(),
        }
    }

    fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Self
        where
            B1: SampleBorrow<Self::X> + Sized,
            B2: SampleBorrow<Self::X> + Sized {
        let low = low_b.borrow();
        let high = high_b.borrow();
        assert!(low <= high);
        Self::new(low, high + APUInt::one())
    }

    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        &self.base + rng.gen_ap_uint_below(&self.len)
    }

    fn sample_single<R: Rng + ?Sized, B1, B2>(low: B1, high: B2, rng: &mut R) -> Self::X
        where
            B1: SampleBorrow<Self::X> + Sized,
            B2: SampleBorrow<Self::X> + Sized {
        rng.gen_ap_uint_range(low.borrow(), high.borrow())
    }
}

impl SampleUniform for APUInt {
    type Sampler = UniformAPUInt;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::traits::{DivRemWithRecip, FastExponentWithRecip, IsPrimeMillerRabin};
    use rand::distributions::{Distribution, Uniform};

    #[test]
    fn test_default() {
        let default = APUInt::zero();
        assert_eq!(default.n_bits, 0);
        assert_eq!(default.bits, Vec::new());
    }

    #[test]
    fn test_from() {
        let number1 = APUInt::from(Vec::new());
        assert_eq!(number1.n_bits, 0);
        assert_eq!(number1.bits, Vec::new());
        let number2 = ap_uint![0b100u64, 0b1000u64, 0, 0];
        assert_eq!(number2.n_bits, 64 + 4);
        assert_eq!(number2.bits, vec![0b100u64, 0b1000u64]);
    }

    #[test]
    fn test_equal() {
        assert_eq!(APUInt::zero(), ap_uint![0]);
        assert_eq!(ap_uint![1, 1], ap_uint![1, 1]);
        assert_ne!(APUInt::zero(), ap_uint![0, 1]);
        assert_ne!(ap_uint![0, 1], APUInt::zero());
        assert_ne!(ap_uint![1], ap_uint![1, 1]);
        assert_ne!(ap_uint![1, 1], ap_uint![1]);
        assert_ne!(ap_uint![1, 2], ap_uint![1, 1]);
    }

    #[test]
    fn test_less() {
        assert!(!(APUInt::zero() < APUInt::zero()));
        assert!(APUInt::zero() <= APUInt::zero());
        assert!(APUInt::zero() < ap_uint![1]);
        assert!(APUInt::zero() <= ap_uint![1]);
        assert!(ap_uint![1] < ap_uint![0, 1]);
        assert!(!(ap_uint![1, 1] < ap_uint![0, 1]));
        assert!(!(ap_uint![0, 0, 1] < ap_uint![0, 1]));
        assert!(ap_uint![0, 0, 1] < ap_uint![0, 1, 1]);
        assert!(ap_uint![0, 1, 1] < ap_uint![1, 1, 1]);
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[test]
    fn test_add() {
        assert_eq!(APUInt::zero() + APUInt::zero(), APUInt::zero());
        assert_eq!(APUInt::zero() + ap_uint![100, 20], ap_uint![100, 20]);
        assert_eq!(ap_uint![100] + ap_uint![100, 20], ap_uint![200, 20]);
        assert_eq!(ap_uint![1u64 << 63] + ap_uint![1u64 << 63], ap_uint![0, 1]);
        assert_eq!(ap_uint![1u64 << 63, 20] + ap_uint![1u64 << 63, 20], ap_uint![0, 41]);
    }

    #[test]
    fn test_max_bits() {
        assert_eq!(APUInt::max_bits(0), APUInt::zero());
        assert_eq!(APUInt::max_bits(3), ap_uint![0b111]);
        assert_eq!(APUInt::max_bits(64), ap_uint![u64::MAX]);
        assert_eq!(APUInt::max_bits(129), ap_uint![u64::MAX, u64::MAX, 1]);
    }

    #[test]
    fn test_min_bits() {
        assert_eq!(APUInt::min_bits(0), APUInt::zero());
        assert_eq!(APUInt::min_bits(3), ap_uint![0b100]);
        assert_eq!(APUInt::min_bits(64), ap_uint![1u64 << 63]);
        assert_eq!(APUInt::min_bits(129), ap_uint![0, 0, 1]);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_sub() {
        assert_eq!(APUInt::zero() - APUInt::zero(), APUInt::zero());
        assert_eq!(ap_uint![20, 100] - APUInt::zero(), ap_uint![20, 100]);
        assert_eq!(ap_uint![20, 100] - ap_uint![20, 100], APUInt::zero());
        assert_eq!(ap_uint![20, 100] -  ap_uint![19], ap_uint![1, 100]);
        assert_eq!(ap_uint![20, 100] -  ap_uint![21], ap_uint![u64::MAX, 99]);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_mul() {
        assert_eq!(APUInt::zero() * APUInt::zero(), APUInt::zero());
        assert_eq!(APUInt::zero() * ap_uint![123], APUInt::zero());
        assert_eq!(ap_uint![123] * APUInt::zero(), APUInt::zero());
        assert_eq!(ap_uint![5, 6] * ap_uint![7, 8], ap_uint![5 * 7, 5 * 8 + 6 * 7, 6 * 8]);
        assert_eq!(APUInt::max_bits(128) * APUInt::max_bits(64),
                   APUInt::min_bits(129) * APUInt::min_bits(65)
                       - APUInt::min_bits(129) - APUInt::min_bits(65) + ap_uint![1]);
    }

    #[test]
    fn test_shl() {
        assert_eq!(APUInt::zero() << 10, APUInt::zero());
        assert_eq!(APUInt::max_bits(64) << 0, APUInt::max_bits(64));
        assert_eq!(APUInt::max_bits(64) << 128, APUInt::max_bits(64) * ap_uint![0, 0, 1]);
        assert_eq!(APUInt::max_bits(64) << 10, APUInt::max_bits(64) * ap_uint![1024]);
        assert_eq!(APUInt::max_bits(500) << 500,
                   APUInt::max_bits(500) * ap_uint![0, 0, 0, 0, 0, 0, 0, 4503599627370496]);
    }

    #[test]
    fn test_shr() {
        assert_eq!(APUInt::max_bits(500) >> 500, APUInt::zero());
        assert_eq!(APUInt::max_bits(600) >> 500, APUInt::max_bits(100));
        assert_eq!(ap_uint![1792] >> 8, ap_uint![7]);
    }

    #[test]
    fn test_get() {
        assert_eq!(ap_uint![2, 1].get(64), true);
        assert_eq!(ap_uint![2, 1].get(65), false);
        assert_eq!(ap_uint![2, 1].get(63), false);
    }

    #[test]
    fn test_set() {
        let mut a = ap_uint![2, 1];
        a.set(128, true);
        assert_eq!(a, ap_uint![2, 1, 1]);
        let mut a = ap_uint![2, 1];
        a.set(64, false);
        assert_eq!(a, ap_uint![2]);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_div() {
        assert_eq!(APUInt::zero().div_rem(&ap_uint![1]), (APUInt::zero(), APUInt::zero()));
        assert_eq!(ap_uint![18, 50].div_rem(&ap_uint!(30)),
                   (ap_uint![12297829382473034411, 1], ap_uint![8]));
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_div_rem_with_recip() {
        let a = ap_uint!(1);
        let recip = a.recip();
        assert_eq!(ap_uint!(0).div_rem_with_recip(&a, &recip), (ap_uint!(0), ap_uint!(0)));
        assert_eq!(ap_uint!(1).div_rem_with_recip(&a, &recip), (ap_uint!(1), ap_uint!(0)));
        assert_eq!(ap_uint!(2).div_rem_with_recip(&a, &recip), (ap_uint!(2), ap_uint!(0)));
        for a in vec![
            ap_uint!(5),
            APUInt::min_bits(100),
            APUInt::max_bits(100),
        ].into_iter() {
            let recip = a.recip();
            assert_eq!(ap_uint!(0).div_rem_with_recip(&a, &recip), (ap_uint!(0), ap_uint!(0)));
            assert_eq!(ap_uint!(1).div_rem_with_recip(&a, &recip), (ap_uint!(0), ap_uint!(1)));
            for i in 1..5 {
                assert_eq!((&a * ap_uint!(i) - ap_uint!(1)).div_rem_with_recip(&a, &recip),
                           (ap_uint!(i - 1), &a - ap_uint!(1)));
                assert_eq!((&a * ap_uint!(i)).div_rem_with_recip(&a, &recip),
                           (ap_uint!(i), ap_uint!(0)));
                assert_eq!((&a * ap_uint!(i) + ap_uint!(1)).div_rem_with_recip(&a, &recip),
                           (ap_uint!(i), ap_uint!(1)));
            }
        }
    }

    #[test]
    fn test_rand() {
        let low = ap_uint![100, 100];
        let high = ap_uint![200, 100];
        let between = Uniform::from(low.clone()..high.clone());
        let mut rng = rand::thread_rng();
        for _ in 0..500 {
            let num = between.sample(&mut rng);
            assert!(num >= low && num < high);
        }
    }

    #[test]
    fn test_fast_exponent_with_recip() {
        let x = ap_uint!(1111) << 128;
        let y = (ap_uint!(1) << 100) + (ap_uint!(1) << 31) + ap_uint!(1);
        let z = (ap_uint!(1) << 100) - ap_uint!(1);
        let recip = z.recip();
        assert_eq!(x.fast_exponent_with_recip(&y, &z, &recip),
                   ap_uint![17937718758987677654, 8285789267]);
    }

    #[test]
    fn test_is_prime_miller_rabin() {
        let primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
            41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97].to_vec();
        let times = 10;
        let calculated_primes = (4..100)
            .filter(|i| {
                let i = i.clone();
                let ap = ap_uint!(i as u64);
                let times = if i < times + 3 { i - 3 } else { times } as u64;
                ap.is_prime_miller_rabin(times)
            })
            .collect::<Vec<_>>();
        assert_eq!(primes, calculated_primes);
    }
}
