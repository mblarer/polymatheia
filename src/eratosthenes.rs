//! Prime generation and factorization using the Sieve of Eratosthenes.

use std::collections::BTreeMap;

/// Creates a prime sieve for primes up to the given `limit`.
pub fn sieve(limit: usize) -> Sieve {
    let primes = Vec::new();
    let mut is_composite = vec![false; limit + 1];

    // 0 and 1 are not prime.
    is_composite[0] = true;
    is_composite[1] = true;

    Sieve {
        primes,
        is_composite,
    }
}

/// Sieve of Eratosthenes.
pub struct Sieve {
    // List of all primes found so far.
    primes: Vec<usize>,
    // The sieve itself.
    is_composite: Vec<bool>,
}

// Public methods.
impl Sieve {
    /// Creates an iterator over all primes up to the sieve's limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use polymatheia::eratosthenes;
    ///
    /// let mut sieve = eratosthenes::sieve(5);
    /// let mut primes = sieve.primes();
    ///
    /// assert_eq!(primes.next(), Some(2));
    /// assert_eq!(primes.next(), Some(3));
    /// assert_eq!(primes.next(), Some(5));
    /// assert_eq!(primes.next(), None);
    /// ```
    pub fn primes<'a>(&'a mut self) -> Primes<'a> {
        Primes {
            idx_next_prime: 0,
            sieve: self,
        }
    }

    /// Computes the prime factorization of `n`.
    ///
    /// # Panics
    ///
    /// Panics if `n` is zero or larger than the sieve's limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use polymatheia::eratosthenes;
    ///
    /// let mut sieve = eratosthenes::sieve(24);
    ///
    /// assert_eq!(sieve.prime_factorization(1), vec![]);
    /// assert_eq!(sieve.prime_factorization(17), vec![(17, 1)]);
    /// assert_eq!(sieve.prime_factorization(24), vec![(2, 3), (3, 1)]);
    /// ```
    pub fn prime_factorization(&mut self, mut n: usize) -> Vec<(usize, usize)> {
        let limit = self.is_composite.len() - 1;
        assert!(0 < n && n <= limit);

        let mut factorization: BTreeMap<usize, usize> = BTreeMap::new();
        for p in self.primes() {
            if n == 1 {
                break;
            }

            while n % p == 0 {
                n /= p;

                *factorization.entry(p).or_insert(0) += 1;
            }
        }

        factorization.into_iter().collect()
    }

    /// Counts the number of divisors of `n`.
    ///
    /// # Panics
    ///
    /// Panics if `n` is zero or larger than the sieve's limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use polymatheia::eratosthenes;
    ///
    /// let mut sieve = eratosthenes::sieve(24);
    ///
    /// assert_eq!(sieve.count_divisors(1), 1);
    /// assert_eq!(sieve.count_divisors(17), 2);
    /// assert_eq!(sieve.count_divisors(24), 8);
    /// ```
    pub fn count_divisors(&mut self, n: usize) -> usize {
        self.prime_factorization(n)
            .into_iter()
            .map(|(_, exp)| exp + 1)
            .product()
    }
}

/// An iterator over all primes up to the sieve's limit.
pub struct Primes<'a> {
    idx_next_prime: usize,
    sieve: &'a mut Sieve,
}

impl Iterator for Primes<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx_next_prime >= self.sieve.primes.len() {
            self.sieve.next_prime()?;
        }

        let next_prime = self.sieve.primes.get(self.idx_next_prime).copied();
        self.idx_next_prime += 1;

        next_prime
    }
}

// Private methods.
impl Sieve {
    fn next_prime(&mut self) -> Option<usize> {
        let limit = self.is_composite.len() - 1;
        let start = self.primes.last().unwrap_or(&1) + 1;
        let next_prime = (start..=limit).find(|i| !self.is_composite[*i]);

        if let Some(p) = next_prime {
            self.primes.push(p);
            if let Some(p_square) = p.checked_mul(p) {
                for i in (p_square..=limit).step_by(p) {
                    self.is_composite[i] = true;
                }
            }
        }

        next_prime
    }
}
