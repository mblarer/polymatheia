//! Euclidean algorithms.

use crate::traits::Zero;
use std::ops::RemAssign;

/// Computes the greatest common divisor (GCD) of two integers.
///
/// Returns `None` if, and only if, both integers are zero.
///
/// # Examples
///
/// ```
/// use polymatheia::euclid;
///
/// assert_eq!(euclid::gcd::<u8>(4, 6), Some(2));
/// assert_eq!(euclid::gcd::<u8>(100, 99), Some(1));
/// assert_eq!(euclid::gcd::<u8>(255, 255), Some(255));
/// assert_eq!(euclid::gcd::<u8>(0, 42), Some(42));
/// assert_eq!(euclid::gcd::<u8>(13, 0), Some(13));
/// assert_eq!(euclid::gcd::<u8>(0, 0), None);
/// ```
pub fn gcd<T>(mut a: T, mut b: T) -> Option<T>
where
    T: Zero + for<'a> RemAssign<&'a T>,
{
    if a.is_zero() && b.is_zero() {
        return None;
    }

    while !b.is_zero() {
        a %= &b;
        (a, b) = (b, a);
    }

    Some(a)
}
