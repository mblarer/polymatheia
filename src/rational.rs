//! Rational numbers.

use crate::{euclid, traits::Zero};
use std::{
    cmp::Ordering,
    ops::{DivAssign, Mul, SubAssign},
};

/// A ratio of two numbers, `n / d`, where `n` is called the numerator and `d` the denominator.
#[derive(PartialEq, Eq, Clone)]
pub struct Ratio<T> {
    numer: T,
    denom: T,
}

// Public methods.
impl<T> Ratio<T>
where
    T: Clone + Zero + Ord + for<'a> SubAssign<&'a T> + for<'b> DivAssign<&'b T>,
{
    /// Creates a new `Ratio` from a numerator and a denominator.
    ///
    /// Returns `None` if, and only if, the denominator is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use polymatheia::rational::Ratio;
    ///
    /// let some_ratio: Option<Ratio<u8>> = Ratio::new(2, 4);
    /// let none_ratio: Option<Ratio<u8>> = Ratio::new(2, 0);
    ///
    /// assert!(some_ratio.is_some());
    /// assert!(none_ratio.is_none());
    /// ```
    pub fn new(numer: T, denom: T) -> Option<Self> {
        if denom.is_zero() {
            return None;
        }

        let mut ratio = Ratio { numer, denom };
        ratio.reduce();

        Some(ratio)
    }
}

impl<T> Ratio<T> {
    /// Returns an immutable reference to the numerator.
    ///
    /// # Examples
    ///
    /// ```
    /// use polymatheia::rational::Ratio;
    ///
    /// let ratio: Option<Ratio<u8>> = Ratio::new(1, 2);
    ///
    /// assert_eq!(ratio.map(|r| *r.numer()), Some(1));
    /// ```
    pub fn numer(&self) -> &T {
        &self.numer
    }

    /// Returns an immutable reference to the denominator.
    ///
    /// # Examples
    ///
    /// ```
    /// use polymatheia::rational::Ratio;
    ///
    /// let ratio: Option<Ratio<u8>> = Ratio::new(1, 2);
    ///
    /// assert_eq!(ratio.map(|r| *r.denom()), Some(2));
    /// ```
    pub fn denom(&self) -> &T {
        &self.denom
    }
}

// Trait impls.
impl<T> PartialOrd for Ratio<T>
where
    T: PartialOrd,
    for<'a> &'a T: Mul<Output = T>,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let ref lhs = self.numer() * other.denom();
        let ref rhs = self.denom() * other.numer();
        PartialOrd::partial_cmp(lhs, rhs)
    }
}

impl<T> Ord for Ratio<T>
where
    T: Ord,
    for<'a> &'a T: Mul<Output = T>,
{
    fn cmp(&self, other: &Self) -> Ordering {
        let ref lhs = self.numer() * other.denom();
        let ref rhs = self.denom() * other.numer();
        Ord::cmp(lhs, rhs)
    }
}

// Private methods.
impl<T> Ratio<T>
where
    T: Clone + Zero + Ord + for<'a> SubAssign<&'a T> + for<'b> DivAssign<&'b T>,
{
    // Reduces the ratio.
    fn reduce(&mut self) {
        let numer = self.numer.clone();
        let denom = self.denom.clone();

        // It is guaranteed by the `Ratio` type that `denom` is never zero, therefore the `gcd()`
        // function will always return `Some(...)`.
        let gcd = euclid::gcd(numer, denom).unwrap();

        self.numer /= &gcd;
        self.denom /= &gcd;
    }
}
