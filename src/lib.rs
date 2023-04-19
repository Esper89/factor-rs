//! List the prime factors of a number or fraction using the [`Fraction`] type. Uses the
//! [`prime_factorization`](https://crates.io/crates/prime_factorization) library.
//!
//! # Examples
//!
//! Basic usage:
//!
//! ```
//! # use factor_rs::*;
//! let frac = Fraction::whole(84);
//! let factors: Vec<Factor> = frac.factorize().collect();
//!
//! assert_eq!(factors, [
//!     Factor::Prime(2, 2),
//!     Factor::Prime(3, 1),
//!     Factor::Prime(7, 1),
//! ]);
//! ```
//!
//! Factorize a fraction:
//!
//! ```
//! # use factor_rs::*;
//! let frac = Fraction::new(-1370, 56);
//! let factors: Vec<Factor> = frac.factorize().collect();
//!
//! assert_eq!(factors, [
//!     Factor::NegativeOne,
//!     Factor::Prime(2, -2),
//!     Factor::Prime(5, 1),
//!     Factor::Prime(7, -1),
//!     Factor::Prime(137, 1),
//! ]);
//! ```
//!
//! Reduce a fraction:
//!
//! ```
//! # use factor_rs::*;
//! let frac = Fraction::new(1200, 362);
//! let reduced: Fraction = frac.factorize().product();
//!
//! assert_eq!(reduced, Fraction::new(600, 181));
//! ```

#![warn(missing_docs)]

use std::{cmp::Ordering, fmt, iter, ops};
use either::Either;
use prime_factorization::Factorization;

/// A fraction that can be factorized.
#[derive(Debug, Copy, Clone, Eq)]
pub struct Fraction
{
    /// The sign, where false is positive and true is negative. Fractions with a numerator of 0
    /// ignore the sign when checking equality.
    pub sign: bool,
    /// The numerator.
    pub num: u128,
    /// The denominator.
    pub denom: u128,
}

impl PartialEq for Fraction
{
    fn eq(&self, other: &Self) -> bool
    {
        if self.num == 0 { (self.num, self.denom) == (other.num, other.denom) }
        else { (self.sign, self.num, self.denom) == (other.sign, other.num, other.denom) }
    }
}

impl Fraction
{
    /// The multiplicative base fraction, 1/1.
    pub const ONE: Self = Fraction { sign: false, num: 1, denom: 1 };

    /// The additive base fraction, 0/1.
    pub const ZERO: Self = Fraction { sign: false, num: 0, denom: 0 };

    /// The negative multiplicative base fraction, -1/1.
    pub const NEG_ONE: Self = Fraction { sign: true, num: 1, denom: 1 };

    /// The fraction that represents positive infinity, 1/0.
    pub const ONE_OVER_ZERO: Self = Fraction { sign: false, num: 1, denom: 0 };

    /// The fraction that represents an undefined value, 0/0.
    pub const ZERO_OVER_ZERO: Self = Fraction { sign: false, num: 0, denom: 0 };

    /// The fraction that represents negative infinity, -1/0.
    pub const NEG_ONE_OVER_ZERO: Self = Fraction { sign: true, num: 1, denom: 0 };

    /// Creates a new fraciton from a numerator and denominator.
    ///
    /// # Examples:
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use factor_rs::*;
    /// let frac = Fraction::new(2, -5);
    ///
    /// assert_eq!(frac.sign, true);
    /// assert_eq!(frac.num, 2);
    /// assert_eq!(frac.denom, 5);
    /// ```
    pub fn new(num: impl Into<Fraction>, denom: impl Into<Fraction>) -> Self
    {
        num.into() / denom.into()
    }

    /// Creates a new fraction from a numerator.
    ///
    /// # Examples:
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use factor_rs::*;
    /// let frac = Fraction::whole(36);
    ///
    /// assert_eq!(frac.sign, false);
    /// assert_eq!(frac.num, 36);
    /// assert_eq!(frac.denom, 1);
    /// ```
    pub fn whole(num: impl Into<Fraction>) -> Self { num.into() }

    /// The multiplicative reciprocal of this fraction, created by swapping the numerator and the
    /// denominator.
    pub const fn recip(&self) -> Self
    {
        Fraction { sign: self.sign, num: self.denom, denom: self.num }
    }

    /// Breaks this fraction down into it's prime factors. The factors are always yielded in order
    /// from lowest to highest, and no two factors with the same base will appear.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use factor_rs::*;
    /// let frac = Fraction::new(-120, 130);
    /// let factors: Vec<Factor> = frac.factorize().collect();
    ///
    /// assert_eq!(factors, [
    ///     Factor::NegativeOne,
    ///     Factor::Prime(2, 2),
    ///     Factor::Prime(3, 1),
    ///     Factor::Prime(13, -1),
    /// ]);
    /// ```
    pub fn factorize(&self) -> impl Iterator<Item = Factor>
    {
        match self
        {
            Fraction { num: 0, denom: 0, ..} => Either::Left(iter::once(Factor::ZeroOverZero)),
            Fraction { num: 0, .. } => Either::Left(iter::once(Factor::Zero)),
            Fraction { sign: false, num, denom } if num == denom =>
                Either::Left(iter::once(Factor::One)),
            Fraction { sign: true, num, denom } if num == denom =>
                Either::Left(iter::once(Factor::NegativeOne)),
            Fraction { .. } => Either::Right(
                (if self.sign { Some(Factor::NegativeOne) } else { None })
                .into_iter()
                .chain(self.prime_factors().map(|(val, exp)| Factor::Prime(val, exp)))
                .chain(if self.denom == 0 { Some(Factor::OneOverZero) } else { None })
            ),
        }
    }

    fn prime_factors(&self) -> impl Iterator<Item = (u128, i8)>
    {
        let mut num = Factorization::run(self.num)
            .prime_factor_repr()
            .into_iter()
            .map(|(val, exp)| (val, exp as i8));

        let mut denom = Factorization::run(self.denom)
            .prime_factor_repr()
            .into_iter()
            .map(|(val, exp)| (val, -(exp as i8)));

        let mut num_curr = num.next();
        let mut denom_curr = denom.next();

        iter::from_fn(move ||
        {
            let Some((num_val, num_exp)) = num_curr else
            {
                let res = denom_curr;
                denom_curr = denom.next();
                return res
            };

            let Some((denom_val, denom_exp)) = denom_curr else
            {
                let res = num_curr;
                num_curr = num.next();
                return res
            };

            match num_val.cmp(&denom_val)
            {
                Ordering::Less =>
                {
                    num_curr = num.next();
                    Some((num_val, num_exp))
                },
                Ordering::Equal =>
                {
                    num_curr = num.next();
                    denom_curr = denom.next();
                    Some((num_val, num_exp + denom_exp))
                },
                Ordering::Greater =>
                {
                    denom_curr = denom.next();
                    Some((denom_val, denom_exp))
                },
            }
        })
        .filter(|(val, exp)| *exp != 0 && *val != 1 && *val != 0)
    }
}

/// A prime factor of a fraction.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Factor
{
    /// The negative multiplicative base, -1. Only a factor of negative fractions.
    NegativeOne,
    /// The additive base, 0. Only a factor if the fraction evaluates to 0.
    Zero,
    /// The multiplicative base, 1. Only a factor if the fraction evaluates to 1.
    One,
    /// A prime number with an exponent. Appears in most fractions.
    Prime(
        /// The base, which is always prime.
        u128,
        /// The exponent.
        i8,
    ),
    /// Positive infinity, 1/0. Only a factor if the fraction involves a division by zero.
    OneOverZero,
    /// An undefined value, 0/0. Only a factor if the fraction evaluates to 0/0.
    ZeroOverZero,
}

impl Factor
{
    /// Determines if this factor would be displayed with an exponent or not. For primes, returns
    /// false if the exponent is 1 and true otherwise. Always returns false for other variants.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use factor_rs::*;
    /// assert!(!Factor::NegativeOne.has_exponent());
    /// assert!(Factor::Prime(2, 2).has_exponent());
    /// assert!(!Factor::OneOverZero.has_exponent());
    /// ```
    pub const fn has_exponent(&self) -> bool { matches!(self, Factor::Prime(_, ..=0 | 2..)) }
}

impl From<Factor> for Fraction
{
    fn from(fac: Factor) -> Self
    {
        match fac
        {
            Factor::NegativeOne => Fraction::NEG_ONE,
            Factor::Zero => Fraction::ZERO,
            Factor::One => Fraction::ONE,
            Factor::Prime(val, exp @ 1..) => Fraction
            {
                sign: false,
                num: num::pow(val, exp as usize),
                denom: 1,
            },
            Factor::Prime(val, exp @ ..=-1) => Fraction
            {
                sign: false,
                num: 1,
                denom: num::pow(val, exp.unsigned_abs() as usize),
            },
            Factor::Prime(1.., 0) => Fraction::ONE,
            Factor::Prime(0, 0) => Fraction::ZERO_OVER_ZERO,
            Factor::OneOverZero => Fraction::ONE_OVER_ZERO,
            Factor::ZeroOverZero => Fraction::ZERO_OVER_ZERO,
        }
    }
}

impl fmt::Display for Factor
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result
    {
        match self
        {
            Factor::NegativeOne => write!(f, "-1"),
            Factor::Zero => write!(f, "0"),
            Factor::One => write!(f, "1"),
            Factor::Prime(val, exp) => if *exp == 1 { write!(f, "{val}") }
                else { write!(f, "{val}^{exp}") },
            Factor::OneOverZero => write!(f, "1/0"),
            Factor::ZeroOverZero => write!(f, "0/0"),
        }
    }
}

impl fmt::Display for Fraction
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result
    {
        match self
        {
            Fraction { num: 0, denom: 0, .. } => write!(f, "0/0"),
            Fraction { num: 0, .. } => write!(f, "0"),
            Fraction { sign: false, denom: 0, .. } => write!(f, "1/0"),
            Fraction { sign: true, denom: 0, .. } => write!(f, "-1/0"),
            Fraction { sign: false, num, denom: 1 } => write!(f, "{num}"),
            Fraction { sign: true, num, denom: 1 } => write!(f, "-{num}"),
            Fraction { sign: false, num, denom } => write!(f, "{num}/{denom}"),
            Fraction { sign: true, num, denom } => write!(f, "-{num}/{denom}"),
        }
    }
}

macro_rules! impl_from_ints
{
    ($int:ident + $uint:ident) =>
    {
        impl From<$int> for Fraction
        {
            fn from(num: $int) -> Self
            {
                Fraction { sign: num.is_negative(), num: num.unsigned_abs() as u128, denom: 1 }
            }
        }

        impl From<$uint> for Fraction
        {
            fn from(num: $uint) -> Self
            {
                Fraction { sign: false, num: num as u128, denom: 1 }
            }
        }
    };
}

impl_from_ints!(i8 + u8);
impl_from_ints!(i16 + u16);
impl_from_ints!(i32 + u32);
impl_from_ints!(i64 + u64);
impl_from_ints!(i128 + u128);

impl ops::Neg for Fraction
{
    type Output = Fraction;
    fn neg(self) -> Fraction { Fraction { sign: !self.sign, num: self.num, denom: self.denom } }
}

impl ops::Neg for &Fraction
{
    type Output = Fraction;
    fn neg(self) -> Fraction { Fraction { sign: !self.sign, num: self.num, denom: self.denom } }
}

impl ops::Mul for Fraction
{
    type Output = Fraction;

    fn mul(self, other: Self) -> Fraction
    {
        Fraction
        {
            sign: self.sign ^ other.sign,
            num: self.num * other.num,
            denom: self.denom * other.denom,
        }
    }
}

impl ops::Mul for &Fraction
{
    type Output = Fraction;

    fn mul(self, other: Self) -> Fraction
    {
        Fraction
        {
            sign: self.sign ^ other.sign,
            num: self.num * other.num,
            denom: self.denom * other.denom,
        }
    }
}

impl ops::Div for Fraction
{
    type Output = Fraction;

    fn div(self, other: Self) -> Fraction
    {
        Fraction
        {
            sign: self.sign ^ other.sign,
            num: self.num * other.denom,
            denom: self.denom * other.num,
        }
    }
}

impl ops::Div for &Fraction
{
    type Output = Fraction;

    fn div(self, other: Self) -> Fraction
    {
        Fraction
        {
            sign: self.sign ^ other.sign,
            num: self.num * other.denom,
            denom: self.denom * other.num,
        }
    }
}

impl ops::MulAssign for Fraction
{
    fn mul_assign(&mut self, other: Self)
    {
        self.sign ^= other.sign;
        self.num *= other.num;
        self.denom *= other.denom;
    }
}

impl ops::MulAssign<&Fraction> for Fraction
{
    fn mul_assign(&mut self, other: &Self)
    {
        self.sign ^= other.sign;
        self.num *= other.num;
        self.denom *= other.denom;
    }
}

impl ops::DivAssign for Fraction
{
    fn div_assign(&mut self, other: Self)
    {
        self.sign ^= other.sign;
        self.num *= other.denom;
        self.denom *= other.num;
    }
}

impl ops::DivAssign<&Fraction> for Fraction
{
    fn div_assign(&mut self, other: &Self)
    {
        self.sign ^= other.sign;
        self.num *= other.denom;
        self.denom *= other.num;
    }
}

impl iter::Product for Fraction
{
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self
    {
        iter.reduce(ops::Mul::mul).unwrap_or(Fraction::ONE)
    }
}

impl iter::Product<Factor> for Fraction
{
    fn product<I: Iterator<Item = Factor>>(iter: I) -> Self
    {
        iter.map(Into::<Fraction>::into).product()
    }
}
