//! Euclidean algorithms.

use crate::traits::{CheckedNeg, Zero};
use std::ops::RemAssign;

/// Computes the greatest common divisor (GCD) of two integers.
///
/// Returns `None` if both integers are zero or if the result cannot be represented by the generic type.
///
/// # Examples
///
/// ```
/// use polymatheia::euclid;
///
/// assert_eq!(euclid::checked_gcd::<u8>(4, 6), Some(2));
/// assert_eq!(euclid::checked_gcd::<u8>(100, 99), Some(1));
/// assert_eq!(euclid::checked_gcd::<u8>(255, 255), Some(255));
/// assert_eq!(euclid::checked_gcd::<u8>(0, 42), Some(42));
/// assert_eq!(euclid::checked_gcd::<u8>(13, 0), Some(13));
/// assert_eq!(euclid::checked_gcd::<u8>(0, 0), None);
/// assert_eq!(euclid::checked_gcd::<i8>(i8::MIN + 1, i8::MIN + 1), Some(i8::MAX));
/// assert_eq!(euclid::checked_gcd::<i8>(i8::MIN, i8::MIN), None);
/// ```
pub fn checked_gcd<T>(mut a: T, mut b: T) -> Option<T>
where
    T: Ord + Zero + for<'a> RemAssign<&'a T> + CheckedNeg<Output = T>,
{
    if a.is_zero() && b.is_zero() {
        return None;
    }

    while !b.is_zero() {
        a %= &b;
        (a, b) = (b, a);
    }

    if a < Zero::zero() {
        a.checked_neg()
    } else {
        Some(a)
    }
}

/// Computes the greatest common divisor (GCD) of two integers.
///
/// # Panics
///
/// Panics if both integers are zero or if the result cannot be represented by the generic type.
///
/// # Examples
///
/// ```
/// use polymatheia::euclid;
///
/// assert_eq!(euclid::gcd::<u8>(4, 6), 2);
/// assert_eq!(euclid::gcd::<u8>(100, 99), 1);
/// assert_eq!(euclid::gcd::<u8>(255, 255), 255);
/// assert_eq!(euclid::gcd::<u8>(0, 42), 42);
/// assert_eq!(euclid::gcd::<u8>(13, 0), 13);
/// assert_eq!(euclid::gcd::<i8>(-4, 6), 2);
/// ```
pub fn gcd<T>(mut a: T, mut b: T) -> T
where
    T: Ord + Zero + for<'a> RemAssign<&'a T> + CheckedNeg<Output = T>,
{
    assert!(!a.is_zero() || !b.is_zero());

    while !b.is_zero() {
        a %= &b;
        (a, b) = (b, a);
    }

    if a < Zero::zero() {
        a.checked_neg().unwrap()
    } else {
        a
    }
}
