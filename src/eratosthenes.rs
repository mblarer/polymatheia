//! Prime generation and factorization using the Sieve of Eratosthenes.

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
        let mut factorization: Vec<(usize, usize)> = Vec::new();

        for p in self.prime_factors(n) {
            let mut e = 0;
            while n % p == 0 {
                n /= p;
                e += 1;
            }
            factorization.push((p, e));
        }

        factorization
    }

    /// Creates an iterator over the unique prime factors of `n`.
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
    /// let mut sieve = eratosthenes::sieve(550);
    ///
    /// assert_eq!(sieve.prime_factors(1).collect::<Vec<_>>(), vec![]);
    /// assert_eq!(sieve.prime_factors(14).collect::<Vec<_>>(), vec![2, 7]);
    /// assert_eq!(sieve.prime_factors(17).collect::<Vec<_>>(), vec![17]);
    /// assert_eq!(sieve.prime_factors(550).collect::<Vec<_>>(), vec![2, 5, 11]);
    /// ```
    pub fn prime_factors<'a>(&'a mut self, n: usize) -> PrimeFactors<'a> {
        let limit = self.is_composite.len() - 1;
        assert!(0 < n && n <= limit);

        let primes = self.primes();

        PrimeFactors { n, primes }
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

    /// Euler's totient function. Counts how many natural numbers up to `n` are coprime to `n`.
    ///
    /// # Panics
    ///
    /// Panics if `n` is larger than the sieve's limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use polymatheia::eratosthenes;
    ///
    /// let mut sieve = eratosthenes::sieve(20);
    ///
    /// assert_eq!(sieve.euler_totient(0), 0);
    /// assert_eq!(sieve.euler_totient(1), 1);
    /// assert_eq!(sieve.euler_totient(14), 6);
    /// assert_eq!(sieve.euler_totient(17), 16);
    /// assert_eq!(sieve.euler_totient(20), 8);
    /// ```
    pub fn euler_totient(&mut self, n: usize) -> usize {
        if n > 0 {
            self.prime_factors(n).fold(n, |m, p| m / p * (p - 1))
        } else {
            0
        }
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

/// An iterator over all primes factors of `n`.
pub struct PrimeFactors<'a> {
    n: usize,
    primes: Primes<'a>,
}

impl Iterator for PrimeFactors<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let p = self.primes.next()?;

            if p > self.n {
                return None;
            } else if self.n % p == 0 {
                return Some(p);
            }
        }
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
