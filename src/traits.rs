//! Numeric traits.

macro_rules! checked_unary_impl {
    ($trait:ident, $method:ident, $type:ty) => {
        impl $trait for $type {
            type Output = $type;

            fn $method(&self) -> Option<Self::Output> {
                <$type>::$method(*self)
            }
        }
    };
}

macro_rules! checked_binary_impl {
    ($trait:ident, $method:ident, $type:ty) => {
        impl $trait for $type {
            type Output = $type;

            fn $method(&self, other: &$type) -> Option<Self::Output> {
                <$type>::$method(*self, *other)
            }
        }
    };
}

macro_rules! binary_impl {
    ($trait:ident, $method:ident, $type:ty) => {
        impl $trait for $type {
            type Output = $type;

            fn $method(&self, other: &$type) -> Self::Output {
                <$type>::$method(*self, *other)
            }
        }
    };
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

/// Negation that returns `None` instead of overflowing.
pub trait CheckedNeg<Output = Self> {
    type Output;

    /// Negates a number and returns `None` instead of overflowing.
    fn checked_neg(&self) -> Option<Self::Output>;
}

checked_unary_impl!(CheckedNeg, checked_neg, u8);
checked_unary_impl!(CheckedNeg, checked_neg, u16);
checked_unary_impl!(CheckedNeg, checked_neg, u32);
checked_unary_impl!(CheckedNeg, checked_neg, u64);
checked_unary_impl!(CheckedNeg, checked_neg, u128);
checked_unary_impl!(CheckedNeg, checked_neg, usize);

checked_unary_impl!(CheckedNeg, checked_neg, i8);
checked_unary_impl!(CheckedNeg, checked_neg, i16);
checked_unary_impl!(CheckedNeg, checked_neg, i32);
checked_unary_impl!(CheckedNeg, checked_neg, i64);
checked_unary_impl!(CheckedNeg, checked_neg, i128);
checked_unary_impl!(CheckedNeg, checked_neg, isize);

/// Addition that returns `None` instead of overflowing.
pub trait CheckedAdd<Output = Self> {
    type Output;

    /// Adds two numbers and returns `None` instead of overflowing.
    fn checked_add(&self, other: &Self) -> Option<Self::Output>;
}

checked_binary_impl!(CheckedAdd, checked_add, u8);
checked_binary_impl!(CheckedAdd, checked_add, u16);
checked_binary_impl!(CheckedAdd, checked_add, u32);
checked_binary_impl!(CheckedAdd, checked_add, u64);
checked_binary_impl!(CheckedAdd, checked_add, u128);
checked_binary_impl!(CheckedAdd, checked_add, usize);

checked_binary_impl!(CheckedAdd, checked_add, i8);
checked_binary_impl!(CheckedAdd, checked_add, i16);
checked_binary_impl!(CheckedAdd, checked_add, i32);
checked_binary_impl!(CheckedAdd, checked_add, i64);
checked_binary_impl!(CheckedAdd, checked_add, i128);
checked_binary_impl!(CheckedAdd, checked_add, isize);

/// Euclidean division.
pub trait DivEuclid<Output = Self> {
    type Output;

    /// Divides two numbers with Euclidean division.
    fn div_euclid(&self, other: &Self) -> Self::Output;
}

binary_impl!(DivEuclid, div_euclid, u8);
binary_impl!(DivEuclid, div_euclid, u16);
binary_impl!(DivEuclid, div_euclid, u32);
binary_impl!(DivEuclid, div_euclid, u64);
binary_impl!(DivEuclid, div_euclid, u128);
binary_impl!(DivEuclid, div_euclid, usize);

binary_impl!(DivEuclid, div_euclid, i8);
binary_impl!(DivEuclid, div_euclid, i16);
binary_impl!(DivEuclid, div_euclid, i32);
binary_impl!(DivEuclid, div_euclid, i64);
binary_impl!(DivEuclid, div_euclid, i128);
binary_impl!(DivEuclid, div_euclid, isize);

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
