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

macro_rules! identity_impl {
    ($trait:ident, $method:ident, $type:ty, $value:expr) => {
        impl $trait for $type {
            fn $method() -> Self {
                $value
            }
        }
    };
}

/// The additive identity, `0`.
pub trait Zero {
    /// Returns the additive identity, `0`.
    fn zero() -> Self;
}

identity_impl!(Zero, zero, u8, 0);
identity_impl!(Zero, zero, u16, 0);
identity_impl!(Zero, zero, u32, 0);
identity_impl!(Zero, zero, u64, 0);
identity_impl!(Zero, zero, u128, 0);
identity_impl!(Zero, zero, usize, 0);

identity_impl!(Zero, zero, i8, 0);
identity_impl!(Zero, zero, i16, 0);
identity_impl!(Zero, zero, i32, 0);
identity_impl!(Zero, zero, i64, 0);
identity_impl!(Zero, zero, i128, 0);
identity_impl!(Zero, zero, isize, 0);

identity_impl!(Zero, zero, f32, 0.0);
identity_impl!(Zero, zero, f64, 0.0);

/// The multiplicative identity, `1`.
pub trait One {
    /// Returns the additive identity, `1`.
    fn one() -> Self;
}

identity_impl!(One, one, u8, 1);
identity_impl!(One, one, u16, 1);
identity_impl!(One, one, u32, 1);
identity_impl!(One, one, u64, 1);
identity_impl!(One, one, u128, 1);
identity_impl!(One, one, usize, 1);

identity_impl!(One, one, i8, 1);
identity_impl!(One, one, i16, 1);
identity_impl!(One, one, i32, 1);
identity_impl!(One, one, i64, 1);
identity_impl!(One, one, i128, 1);
identity_impl!(One, one, isize, 1);

identity_impl!(One, one, f32, 1.0);
identity_impl!(One, one, f64, 1.0);
