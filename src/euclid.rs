//! Euclidean algorithms.

use crate::traits::Zero;
use std::{cmp::Ordering, ops::SubAssign};

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
    T: Zero + Ord + for<'a> SubAssign<&'a T>,
{
    if a.is_zero() && b.is_zero() {
        return None;
    } else if a.is_zero() {
        return Some(b);
    } else if b.is_zero() {
        return Some(a);
    }

    loop {
        match Ord::cmp(&a, &b) {
            Ordering::Equal => return Some(a),
            Ordering::Greater => a -= &b,
            Ordering::Less => b -= &a,
        };
    }
}
