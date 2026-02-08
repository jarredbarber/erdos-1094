import Mathlib

open scoped Nat

namespace Erdos1094

/--
For all n ≥ 2k the least prime factor of C(n,k) is ≤ max(n/k, k), with only
finitely many exceptions.

Reference: https://www.erdosproblems.com/1094
-/
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  sorry

end Erdos1094
