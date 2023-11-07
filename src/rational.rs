//! Rational numbers.

use crate::{
    euclid,
    traits::{CheckedNeg, DivEuclid, Zero},
};
use std::{
    cmp::Ordering,
    ops::{DivAssign, Mul, RemAssign},
};

/// A ratio of two numbers, `n / d`, where `n` is called the numerator and `d` the denominator.
#[derive(PartialEq, Eq, Clone)]
pub struct Ratio<T> {
    numer: T,
    denom: T,
}

// Public methods (checked).
impl<T> Ratio<T>
where
    T: Ord
        + Clone
        + Zero
        + for<'a> RemAssign<&'a T>
        + for<'b> DivAssign<&'b T>
        + CheckedNeg<Output = T>,
{
    /// Creates a new `Ratio` from a numerator and a denominator, without panicking.
    ///
    /// Returns `None` if the denominator is zero or if the generic type cannot represent the
    /// reduced form.
    ///
    /// # Examples
    ///
    /// ```
    /// use polymatheia::rational::Ratio;
    ///
    /// let some_ratio: Option<Ratio<u8>> = Ratio::checked_new(2, 4);
    /// let none_ratio: Option<Ratio<u8>> = Ratio::checked_new(2, 0);
    ///
    /// assert!(some_ratio.is_some());
    /// assert!(none_ratio.is_none());
    /// ```
    pub fn checked_new(numer: T, denom: T) -> Option<Self> {
        if denom.is_zero() {
            return None;
        }

        let ratio = Ratio { numer, denom };

        ratio.checked_reduced()
    }
}

// Public methods.
impl<T> Ratio<T>
where
    T: Ord
        + Clone
        + Zero
        + for<'a> RemAssign<&'a T>
        + for<'b> DivAssign<&'b T>
        + CheckedNeg<Output = T>
        + DivEuclid<Output = T>,
{
    /// Creates a new `Ratio` from a numerator and a denominator.
    ///
    /// Panics if the denominator is zero or if the generic type cannot represent the reduced form.
    ///
    /// # Examples
    ///
    /// ```
    /// use polymatheia::rational::Ratio;
    ///
    /// let ratio: Ratio<i8> = Ratio::new(2, -4);
    ///
    /// assert_eq!(*ratio.numer(), -1);
    /// assert_eq!(*ratio.denom(), 2);
    /// ```
    pub fn new(numer: T, denom: T) -> Self {
        assert!(!denom.is_zero());

        let ratio = Ratio { numer, denom };

        ratio.reduced()
    }

    /// Creates an iterator over the coefficients of `self` as continued fraction.
    ///
    /// # Examples
    ///
    /// ```
    /// use polymatheia::rational::Ratio;
    ///
    /// let ratio: Ratio<u8> = Ratio::new(9, 4);
    /// let mut cont_frac = ratio.iter_cont_frac();
    ///
    /// assert_eq!(cont_frac.next(), Some(2));
    /// assert_eq!(cont_frac.next(), Some(4));
    /// assert_eq!(cont_frac.next(), None);
    /// ```
    pub fn iter_cont_frac(&self) -> IterContFrac<T> {
        IterContFrac {
            a: self.numer().clone(),
            b: self.denom().clone(),
        }
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
    /// let ratio: Ratio<u8> = Ratio::new(1, 2);
    ///
    /// assert_eq!(*ratio.numer(), 1);
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
    /// let ratio: Ratio<u8> = Ratio::new(1, 2);
    ///
    /// assert_eq!(*ratio.denom(), 2);
    /// ```
    pub fn denom(&self) -> &T {
        &self.denom
    }
}

/// An iterator over the coefficients of a `Ratio` as continued fraction.
pub struct IterContFrac<T> {
    a: T,
    b: T,
}

impl<T> Iterator for IterContFrac<T>
where
    T: Zero + Clone + DivEuclid<Output = T> + for<'a> RemAssign<&'a T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let ref mut a = self.a;
        let ref mut b = self.b;

        if b.is_zero() {
            return None;
        }

        let coeff = a.div_euclid(b);

        // Note: this is the same step as in the GCD algorithm.
        *a %= b;
        std::mem::swap(a, b);

        Some(coeff)
    }
}

// Trait impls.
impl<T> PartialOrd for Ratio<T>
where
    T: PartialOrd
        + Ord
        + Clone
        + Zero
        + for<'a> RemAssign<&'a T>
        + for<'b> DivAssign<&'b T>
        + CheckedNeg<Output = T>
        + DivEuclid<Output = T>,
    for<'a> &'a T: Mul<Output = T>,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // We use the continued fraction representation of a rational for the comparison since the
        // "multiplication method" may overflow, whereas this method does not.
        let mut k = 0;
        let mut cont_frac_s = self.iter_cont_frac();
        let mut cont_frac_o = other.iter_cont_frac();
        loop {
            match (cont_frac_s.next(), cont_frac_o.next(), k % 2) {
                (None, None, _) => return Some(Ordering::Equal),
                (None, Some(_), 0) => return Some(Ordering::Greater),
                (None, Some(_), _) => return Some(Ordering::Less),
                (Some(_), None, 0) => return Some(Ordering::Less),
                (Some(_), None, _) => return Some(Ordering::Greater),
                (Some(ref c_s), Some(ref c_o), 0) => match c_s.partial_cmp(c_o)? {
                    Ordering::Greater => return Some(Ordering::Greater),
                    Ordering::Less => return Some(Ordering::Less),
                    Ordering::Equal => k += 1,
                },
                (Some(ref c_s), Some(ref c_o), _) => match c_s.partial_cmp(c_o)? {
                    Ordering::Greater => return Some(Ordering::Less),
                    Ordering::Less => return Some(Ordering::Greater),
                    Ordering::Equal => k += 1,
                },
            }
        }
    }
}

impl<T> Ord for Ratio<T>
where
    T: Ord,
    for<'a> &'a T: Mul<Output = T>,
    Ratio<T>: PartialOrd,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

// Private methods (checked).
impl<T> Ratio<T>
where
    T: Ord
        + Clone
        + Zero
        + for<'a> RemAssign<&'a T>
        + for<'b> DivAssign<&'b T>
        + CheckedNeg<Output = T>,
{
    // Reduces the ratio without panicking.
    //
    // This item is private because the ratio should, from an external point of view, always be in
    // reduced form.
    //
    // Returns `None` if the GCD cannot be represented by the generic type.
    fn checked_reduced(mut self) -> Option<Self> {
        let numer = self.numer.clone();
        let denom = self.denom.clone();

        let gcd = euclid::checked_gcd(numer, denom)?;

        self.numer /= &gcd;
        self.denom /= &gcd;

        if self.denom < Zero::zero() {
            self.numer = self.numer.checked_neg()?;
            self.denom = self.denom.checked_neg()?;
        }

        Some(self)
    }
}

// Private methods.
impl<T> Ratio<T>
where
    T: Ord
        + Clone
        + Zero
        + for<'a> RemAssign<&'a T>
        + for<'b> DivAssign<&'b T>
        + CheckedNeg<Output = T>,
{
    // Reduces the ratio.
    //
    // This item is private because the ratio should, from an external point of view, always be in
    // reduced form.
    //
    // # Panics
    //
    // Panics if the GCD cannot be represented by the generic type.
    fn reduced(mut self) -> Self {
        let numer = self.numer.clone();
        let denom = self.denom.clone();

        let gcd = euclid::gcd(numer, denom);

        self.numer /= &gcd;
        self.denom /= &gcd;

        if self.denom < Zero::zero() {
            self.numer = self.numer.checked_neg().unwrap();
            self.denom = self.denom.checked_neg().unwrap();
        }

        self
    }
}
