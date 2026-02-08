# Erdős Problem 1094

## Problem Statement

For all n ≥ 2k, the least prime factor of C(n,k) (the binomial coefficient "n choose k") is at most max(n/k, k), with only finitely many exceptions.

In other words, the set of pairs (n, k) where 0 < k, 2k ≤ n, and the smallest prime factor of C(n,k) exceeds max(n/k, k) is finite.

Reference: [erdosproblems.com/1094](https://www.erdosproblems.com/1094)

## Lean 4 Formal Theorem

From [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures):

```lean
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite
```

**THIS THEOREM STATEMENT IS IMMUTABLE. DO NOT MODIFY IT.**

## Goal

Produce both a natural language proof and a Lean 4 formalization.

Success criteria:
1. The theorem statement matches the one above exactly — no additional assumptions
2. `lake build` succeeds
3. No sorrys in the codebase (citation sorrys for well-established theorems not in Mathlib are acceptable with full citation — see workflow docs)

ALL THREE MUST BE SATISFIED FOR SUCCESS.

## Background

The binomial coefficient C(n,k) = n! / (k!(n-k)!) has a rich prime factorization structure. Key tools that may be relevant:

- **Kummer's theorem**: The p-adic valuation of C(n,k) equals the number of carries when adding k and n-k in base p
- **Legendre's formula**: v_p(n!) = Σ ⌊n/p^i⌋
- **Bertrand's postulate**: There is always a prime between n and 2n (in Mathlib)
- The least prime factor of C(n,k) relates to which small primes divide the numerator but not the denominator

The claim is a finiteness result: only finitely many "bad" pairs exist. This suggests either:
1. An explicit bound beyond which all pairs satisfy the inequality, or
2. A structural argument about prime factors of binomial coefficients
