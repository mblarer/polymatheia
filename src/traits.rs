//! Numeric traits.

macro_rules! checked_impl {
    ($trait:ident, $method:ident, $type:ty) => {
        impl $trait for $type {
            type Output = $type;

            fn $method(&self, other: &$type) -> Option<$type> {
                <$type>::$method(*self, *other)
            }
        }
    };
}

/// Addition that returns `None` instead of overflowing.
pub trait CheckedAdd {
    type Output;

    /// Adds two numbers and returns `None` instead of overflowing.
    fn checked_add(&self, other: &Self) -> Option<Self::Output>;
}

checked_impl!(CheckedAdd, checked_add, u8);
checked_impl!(CheckedAdd, checked_add, u16);
checked_impl!(CheckedAdd, checked_add, u32);
checked_impl!(CheckedAdd, checked_add, u64);
checked_impl!(CheckedAdd, checked_add, u128);
checked_impl!(CheckedAdd, checked_add, usize);

checked_impl!(CheckedAdd, checked_add, i8);
checked_impl!(CheckedAdd, checked_add, i16);
checked_impl!(CheckedAdd, checked_add, i32);
checked_impl!(CheckedAdd, checked_add, i64);
checked_impl!(CheckedAdd, checked_add, i128);
checked_impl!(CheckedAdd, checked_add, isize);

impl<T: CheckedAdd<Output = T>> CheckedAdd for Option<T> {
    type Output = T;

    fn checked_add(&self, other: &Self) -> Option<Self::Output> {
        self.as_ref()?.checked_add(other.as_ref()?)
    }
}

/// The additive identity, `0`.
pub trait Zero {
    /// Returns the additive identity, `0`.
    fn zero() -> Self;

    /// Returns `true` if `self` is the additive identity, `0`.
    fn is_zero(&self) -> bool;
}

macro_rules! zero_impl {
    ($type:ty, $value:expr) => {
        impl Zero for $type {
            fn zero() -> Self {
                $value
            }

            fn is_zero(&self) -> bool {
                *self == $value
            }
        }
    };
}

zero_impl!(u8, 0);
zero_impl!(u16, 0);
zero_impl!(u32, 0);
zero_impl!(u64, 0);
zero_impl!(u128, 0);
zero_impl!(usize, 0);

zero_impl!(i8, 0);
zero_impl!(i16, 0);
zero_impl!(i32, 0);
zero_impl!(i64, 0);
zero_impl!(i128, 0);
zero_impl!(isize, 0);

zero_impl!(f32, 0.0);
zero_impl!(f64, 0.0);

/// The multiplicative identity, `1`.
pub trait One {
    /// Returns the multiplicative identity, `1`.
    fn one() -> Self;

    /// Returns `true` if `self` is the multiplicative identity, `1`.
    fn is_one(&self) -> bool;
}

macro_rules! one_impl {
    ($type:ty, $value:expr) => {
        impl One for $type {
            fn one() -> Self {
                $value
            }

            fn is_one(&self) -> bool {
                *self == $value
            }
        }
    };
}

one_impl!(u8, 1);
one_impl!(u16, 1);
one_impl!(u32, 1);
one_impl!(u64, 1);
one_impl!(u128, 1);
one_impl!(usize, 1);

one_impl!(i8, 1);
one_impl!(i16, 1);
one_impl!(i32, 1);
one_impl!(i64, 1);
one_impl!(i128, 1);
one_impl!(isize, 1);

one_impl!(f32, 1.0);
one_impl!(f64, 1.0);
