//! This module contains the `Field` abstraction that allows us to write
//! code that generalizes over a pair of fields.

use core::mem::size_of;
use static_assertions::const_assert;
use std::assert;
use std::convert::TryInto;
use subtle::{Choice, ConstantTimeEq, CtOption};

use super::Group;

const_assert!(size_of::<usize>() >= 4);

/// This trait is a common interface for dealing with elements of a finite
/// field.
pub trait FieldExt:
    ff::PrimeField + From<bool> + Ord + ConstantTimeEq + Group<Scalar = Self>
{
    /// Generator of the $2^S$ multiplicative subgroup
    const ROOT_OF_UNITY: Self;

    /// Inverse of `ROOT_OF_UNITY`
    const ROOT_OF_UNITY_INV: Self;

    /// The value $(2^S)^{-1} \mod t$.
    const UNROLL_T_EXPONENT: [u64; 4];

    /// Represents $t$ where $2^S \cdot t = p - 1$ with $t$ odd.
    const T_EXPONENT: [u64; 4];

    /// The value $(t-1)/2$.
    const T_EXPONENT_MINUS1_OVER2: [u64; 4];

    /// The value $t^{-1} \mod 2^S$.
    const UNROLL_S_EXPONENT: u64;

    /// Generator of the $t-order$ multiplicative subgroup
    const DELTA: Self;

    /// Inverse of $2$ in the field.
    const TWO_INV: Self;

    /// Ideally the smallest prime $\alpha$ such that gcd($p - 1$, $\alpha$) = $1$
    const RESCUE_ALPHA: u64;

    /// $RESCUE_INVALPHA \cdot RESCUE_ALPHA = 1 \mod p - 1$ such that
    /// `(a^RESCUE_ALPHA)^RESCUE_INVALPHA = a`.
    const RESCUE_INVALPHA: [u64; 4];

    /// Element of multiplicative order $3$.
    const ZETA: Self;

    /// XOR parameter of the perfect hash function used for SqrtTables.
    const HASH_XOR: u32;

    /// Modulus of the perfect hash function used for SqrtTables.
    const HASH_MOD: usize;

    /// Tables for square root computation.
    fn get_tables() -> &'static SqrtTables<Self>;

    /// This computes a random element of the field using system randomness.
    fn rand() -> Self {
        Self::random(rand::rngs::OsRng)
    }

    /// Returns whether or not this element is zero.
    fn ct_is_zero(&self) -> Choice;

    /// Obtains a field element congruent to the integer `v`.
    fn from_u64(v: u64) -> Self;

    /// Obtains a field element congruent to the integer `v`.
    fn from_u128(v: u128) -> Self;

    /// Converts this field element to its normalized, little endian byte
    /// representation.
    fn to_bytes(&self) -> [u8; 32];

    /// Attempts to obtain a field element from its normalized, little endian
    /// byte representation.
    fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self>;

    /// Obtains a field element that is congruent to the provided little endian
    /// byte representation of an integer.
    fn from_bytes_wide(bytes: &[u8; 64]) -> Self;

    /// Returns a square root of this element, if it exists and this element is
    /// nonzero. Always returns the same square root, and it is efficient to
    /// check that it has done so using `extract_radix2_vartime`.
    fn deterministic_sqrt(&self) -> Option<Self> {
        let sqrt = self.sqrt();
        if bool::from(sqrt.is_none()) {
            return None;
        }
        let sqrt = sqrt.unwrap();
        let extracted = sqrt.extract_radix2_vartime()?;

        if extracted.1 >> (Self::S - 1) == 1 {
            Some(-sqrt)
        } else {
            Some(sqrt)
        }
    }

    /// Computes:
    ///
    /// * (true,  sqrt(num/div)),                 if num and div are nonzero and num/div is a square in the field;
    /// * (true,  0),                             if num is zero;
    /// * (false, 0),                             if num is nonzero and div is zero;
    /// * (false, sqrt(ROOT_OF_UNITY * num/div)), if num and div are nonzero and num/div is a nonsquare in the field;
    ///
    /// where ROOT_OF_UNITY is a generator of the order 2^n subgroup (and therefore a nonsquare).
    ///
    /// The choice of root from sqrt is unspecified.
    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        // Based on:
        // * [Sarkar2020](https://eprint.iacr.org/2020/1407)
        // * [BDLSY2012](https://cr.yp.to/papers.html#ed25519)
        //
        // We need to calculate uv and v, where v = u^((m-1)/2), u = num/div, and p-1 = T * 2^S.
        // We can rewrite as follows:
        //
        //      v = (num/div)^((T-1)/2)
        //        = num^((T-1)/2) * div^(p-1 - (T-1)/2)    [Fermat's Little Theorem]
        //        =       "       * div^(T * 2^S - (T-1)/2)
        //        =       "       * div^((2^(S+1) - 1)*(T-1)/2 + 2^S)
        //        = (num * div^(2^(S+1) - 1))^((T-1)/2) * div^(2^S)
        //
        // Let  w = (num * div^(2^(S+1) - 1))^((T-1)/2) * div^(2^S - 1).
        // Then v = w * div, and uv = num * v / div = num * w.
        //
        // We calculate:
        //
        //      s = div^(2^S - 1) using an addition chain
        //      t = div^(2^(S+1) - 1) = s^2 * div
        //      w = (num * t)^((T-1)/2) * s using another addition chain
        //
        // then u and uv as above. The addition chains are given in
        // https://github.com/zcash/pasta/blob/master/addchain_sqrt.py .
        // The overall cost of this part is similar to a single full-width exponentiation,
        // regardless of S.

        let sqr = |x: Self, i: u32| (0..i).fold(x, |x, _| x.square());

        // s = div^(2^S - 1)
        let s = (0..5).fold(*div, |d: Self, i| sqr(d, 1 << i) * d);

        // t == div^(2^(S+1) - 1)
        let t = s.square() * div;

        // TODO: replace this with an addition chain.
        let w = ff::Field::pow_vartime(&(t * num), &Self::T_EXPONENT_MINUS1_OVER2) * s;

        // v == u^((T-1)/2)
        let v = w * div;

        // uv = u * v
        let uv = w * num;

        Self::sqrt_common(num, div, &uv, &v)
    }

    /// Same as sqrt_ratio but given num, div, v = u^((T-1)/2), and uv = u * v as input.
    ///
    /// The choice of root from sqrt is unspecified.
    fn sqrt_common(num: &Self, div: &Self, uv: &Self, v: &Self) -> (Choice, Self) {
        let tab = Self::get_tables();
        let sqr = |x: Self, i: u32| (0..i).fold(x, |x, _| x.square());

        let x3 = *uv * v;
        let x2 = sqr(x3, 8);
        let x1 = sqr(x2, 8);
        let x0 = sqr(x1, 8);

        // i = 0, 1
        let mut t_: usize = tab.inv[x0.hash()] as usize; // = t >> 16
                                                         // 1 == x0 * ROOT_OF_UNITY^(t_ << 24)
        assert!(t_ < 0x100);
        let alpha = x1 * tab.g2[t_];

        // i = 2
        t_ += (tab.inv[alpha.hash()] as usize) << 8; // = t >> 8
                                                     // 1 == x1 * ROOT_OF_UNITY^(t_ << 16)
        assert!(t_ < 0x10000);
        let alpha = x2 * tab.g1[t_ & 0xFF] * tab.g2[t_ >> 8];

        // i = 3
        t_ += (tab.inv[alpha.hash()] as usize) << 16; // = t
                                                      // 1 == x2 * ROOT_OF_UNITY^(t_ << 8)
        assert!(t_ < 0x1000000);
        let alpha = x3 * tab.g0[t_ & 0xFF] * tab.g1[(t_ >> 8) & 0xFF] * tab.g2[t_ >> 16];

        t_ += (tab.inv[alpha.hash()] as usize) << 24; // = t << 1
                                                      // 1 == x3 * ROOT_OF_UNITY^t_
        t_ = (t_ + 1) >> 1;
        assert!(t_ <= 0x80000000);
        let res = *uv
            * tab.g0[t_ & 0xFF]
            * tab.g1[(t_ >> 8) & 0xFF]
            * tab.g2[(t_ >> 16) & 0xFF]
            * tab.g3[t_ >> 24];

        let sqdiv = res.square() * div;
        let is_square = (sqdiv - num).ct_is_zero();
        let is_nonsquare = (sqdiv - Self::ROOT_OF_UNITY * num).ct_is_zero();
        assert!(bool::from(
            num.ct_is_zero() | div.ct_is_zero() | (is_square ^ is_nonsquare)
        ));

        (is_square, res)
    }

    /// Returns a perfect hash of this element for use with inv.
    fn hash(&self) -> usize {
        ((self.get_lower_32() ^ Self::HASH_XOR) as usize) % Self::HASH_MOD
    }

    /// Returns an element $a$ of multiplicative order $t$ together with an
    /// integer `s` such that `self` is the square of $a \cdot \omega^{s}$ if
    /// indeed `self` is a square.
    fn extract_radix2_vartime(&self) -> Option<(Self, u64)> {
        if bool::from(self.ct_is_zero()) {
            return None;
        }

        // TODO: these can probably be simplified
        let t = self.pow_vartime(&[1 << Self::S, 0, 0, 0]);
        let t = t.pow_vartime(&Self::UNROLL_T_EXPONENT);
        let t = t.pow_vartime(&Self::UNROLL_T_EXPONENT);
        let s = self.pow_vartime(&Self::T_EXPONENT);
        let mut s = s.pow_vartime(&[Self::UNROLL_S_EXPONENT, 0, 0, 0]);

        let mut m = Self::S;
        let mut c = Self::ROOT_OF_UNITY_INV;

        let mut extract: u64 = 0;

        let mut cur = 1;
        while s != Self::one() {
            let mut i = 1;
            {
                let mut s2i = s;
                s2i = s2i.square();
                while s2i != Self::one() {
                    i += 1;
                    s2i = s2i.square();
                }
            }

            for _ in 0..(m - i) {
                c = c.square();
                cur <<= 1;
            }
            extract |= cur;
            s *= c;
            m = i;
        }

        Some((t, extract))
    }

    /// Exponentiates `self` by `by`, where `by` is a little-endian order
    /// integer exponent.
    fn pow(&self, by: &[u64; 4]) -> Self {
        let mut res = Self::one();
        for e in by.iter().rev() {
            for i in (0..64).rev() {
                res = res.square();
                let mut tmp = res;
                tmp *= self;
                res.conditional_assign(&tmp, (((*e >> i) & 0x1) as u8).into());
            }
        }
        res
    }

    /// Gets the lower 128 bits of this field element when expressed
    /// canonically.
    fn get_lower_128(&self) -> u128;

    /// Gets the lower 32 bits of this field element when expressed
    /// canonically.
    fn get_lower_32(&self) -> u32;

    /// Performs a batch inversion using Montgomery's trick, returns the product
    /// of every inverse. Zero inputs are ignored.
    fn batch_invert(v: &mut [Self]) -> Self {
        let mut tmp = Vec::with_capacity(v.len());

        let mut acc = Self::one();
        for p in v.iter() {
            tmp.push(acc);
            acc = Self::conditional_select(&(acc * p), &acc, p.ct_is_zero());
        }

        acc = acc.invert().unwrap();
        let allinv = acc;

        for (p, tmp) in v.iter_mut().rev().zip(tmp.into_iter().rev()) {
            let skip = p.ct_is_zero();

            let tmp = tmp * acc;
            acc = Self::conditional_select(&(acc * *p), &acc, skip);
            *p = Self::conditional_select(&tmp, p, skip);
        }

        allinv
    }
}

/// Tables used for square root computation.
#[derive(Debug)]
pub struct SqrtTables<F: FieldExt> {
    inv: Vec<u8>,
    g0: [F; 256],
    g1: [F; 256],
    g2: [F; 256],
    g3: [F; 129],
}

impl<F: FieldExt> SqrtTables<F> {
    /// Build tables given parameters for the perfect hash.
    pub fn init() -> Self {
        let gtab: Vec<Vec<F>> = (0..4)
            .scan(F::ROOT_OF_UNITY, |gi, _| {
                // gi == ROOT_OF_UNITY^(256^i)
                let gtab_i: Vec<F> = (0..256)
                    .scan(F::one(), |acc, _| {
                        let res = *acc;
                        *acc *= *gi;
                        Some(res)
                    })
                    .collect();
                *gi = gtab_i[255] * *gi;
                Some(gtab_i)
            })
            .collect();

        // Now invert gtab[3].
        let mut inv: Vec<u8> = vec![1; F::HASH_MOD];
        for j in 0..256 {
            let hash = gtab[3][j].hash();
            // 1 is the last value to be assigned, so this ensures there are no collisions.
            assert!(inv[hash] == 1);
            inv[hash] = ((256 - j) & 0xFF) as u8;
        }

        SqrtTables::<F> {
            inv,
            g0: gtab[0][..].try_into().unwrap(),
            g1: gtab[1][..].try_into().unwrap(),
            g2: gtab[2][..].try_into().unwrap(),
            g3: gtab[3][0..129].try_into().unwrap(),
        }
    }
}

/// Compute a + b + carry, returning the result and the new carry over.
#[inline(always)]
pub(crate) const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let ret = (a as u128) + (b as u128) + (carry as u128);
    (ret as u64, (ret >> 64) as u64)
}

/// Compute a - (b + borrow), returning the result and the new borrow.
#[inline(always)]
pub(crate) const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let ret = (a as u128).wrapping_sub((b as u128) + ((borrow >> 63) as u128));
    (ret as u64, (ret >> 64) as u64)
}

/// Compute a + (b * c) + carry, returning the result and the new carry over.
#[inline(always)]
pub(crate) const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let ret = (a as u128) + ((b as u128) * (c as u128)) + (carry as u128);
    (ret as u64, (ret >> 64) as u64)
}
