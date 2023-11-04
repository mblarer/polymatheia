//! Functions related to the Fibonacci sequence.

use crate::traits::{CheckedAdd, One, Zero};

/// Creates an iterator over all Fibonacci numbers that are representable by the generic type.
///
/// # Examples
///
/// ```
/// use polymatheia::fibonacci;
///
/// let mut fib = fibonacci::sequence::<u8>();
///
/// assert_eq!(fib.next(), Some(0));
/// assert_eq!(fib.next(), Some(1));
/// assert_eq!(fib.next(), Some(1));
/// assert_eq!(fib.last(), Some(233));
/// ```
pub fn sequence<T: Zero + One>() -> Sequence<T> {
    Sequence {
        curr: Some(Zero::zero()),
        next: Some(One::one()),
    }
}

/// An iterator over all Fibonacci numbers that are representable by the generic type.
///
/// This `struct` is created by the [`sequence()`] function. See its documentation for more.
pub struct Sequence<T> {
    curr: Option<T>,
    next: Option<T>,
}

impl<T> Iterator for Sequence<T>
where
    Option<T>: CheckedAdd<Output = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let prev = self.curr.take();
        let curr = self.next.take();
        let next = prev.checked_add(&curr);

        self.next = next;
        self.curr = curr;

        prev
    }
}
