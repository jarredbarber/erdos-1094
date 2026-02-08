/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Erdos.KGe29

/-!
# No Exceptions for k ≤ 28 Beyond n = 284

This file formalizes the proof that all exceptions to the Erdős 1094 conjecture
with k ≤ 28 satisfy n ≤ 284. That is, for k ≤ 28 and n > 284 with 2k ≤ n:
  `(n.choose k).minFac ≤ max (n / k) k`

## Proof Structure

The proof splits into three ranges of k:

**k = 1:** `C(n, 1) = n`, so `minFac(n) ≤ n = n/1 = max(n/1, 1)`.

**k ∈ [2, 16]:** Since k ≤ 16 implies k² ≤ 256 < 284 < n, we always have n > k².
By `large_n_minFac_bound` (from `Erdos.KGe29`), `minFac(C(n,k)) ≤ n/k ≤ max(n/k, k)`.

**k ∈ [17, 28]:** Split on whether n > k² or 284 < n ≤ k²:
- If n > k²: use `large_n_minFac_bound` as above.
- If 284 < n ≤ k²: exhaustive finite verification via `native_decide`.

## Dependencies

* `Erdos.KGe29` — provides `large_n_minFac_bound` for the n > k² case
* proofs/bound-n-for-small-k.md — Verified natural language proof

## References

* proofs/bound-n-for-small-k.md — Exhaustive verification for Case B
-/

open Nat

namespace Erdos1094

/-! ### Finite verification: k ∈ [17, 28], n ∈ [285, k²]

For each k ∈ {17, ..., 28} and each n ∈ {285, ..., k²}, the minimum prime factor
of C(n, k) is at most max(n/k, k). This is verified by direct computation.

By the NL proof (proofs/bound-n-for-small-k.md, Section 5), for every such (n, k),
at least one prime p ≤ k divides C(n, k), because digit domination k ≼_p n
fails for some prime p ≤ k. -/

set_option maxHeartbeats 2000000 in
-- Exhaustive verification of 2810 cases (k ∈ [17,28], n ∈ [285, k²]).
-- For each (n, k), C(n, k) has a small prime factor ≤ k (typically 2 or 3),
-- so native_decide computes minFac quickly via trial division.
set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
private lemma case_b_finite :
    ∀ k ∈ Finset.Icc 17 28, ∀ n ∈ Finset.Icc 285 (k * k),
    (n.choose k).minFac ≤ max (n / k) k := by native_decide

/-! ### Main theorem -/

/-- **No exceptions for k ≤ 28 beyond n = 284** (proofs/bound-n-for-small-k.md):
For all n, k with 0 < k, k ≤ 28, 2k ≤ n, and n > 284,
  `(n.choose k).minFac ≤ max (n / k) k`.

Combined with `no_exception_k_ge_29` from `Erdos.KGe29`, this shows the exceptional
set for Erdős 1094 is finite (contained in `{(n, k) : k ≤ 28, n ≤ 284}`). -/
theorem bound_n_for_small_k (n k : ℕ) (hk : 0 < k) (hn : 2 * k ≤ n)
    (hk28 : k ≤ 28) (hn284 : 284 < n) :
    (n.choose k).minFac ≤ max (n / k) k := by
  -- Case split: k = 1 vs k ≥ 2
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · -- k = 1: C(n, 1) = n, minFac(n) ≤ n = max(n/1, 1)
    rw [Nat.choose_one_right, Nat.div_one]
    exact le_trans (Nat.minFac_le (by omega)) (le_max_left _ _)
  · -- k ≥ 2: split on n > k² vs n ≤ k²
    by_cases hkk : k * k < n
    · -- Case A: n > k²
      -- By large_n_minFac_bound: minFac(C(n,k)) ≤ n/k
      exact le_trans (large_n_minFac_bound n k (by omega) hkk (by omega)) (le_max_left _ _)
    · -- Case B: 284 < n ≤ k²
      push_neg at hkk
      -- Since k ≤ 16 → k² ≤ 256 < 284 < n, contradiction. So k ≥ 17.
      have hk17 : 17 ≤ k := by nlinarith
      -- Apply the finite verification
      exact case_b_finite k (Finset.mem_Icc.mpr ⟨hk17, hk28⟩)
              n (Finset.mem_Icc.mpr ⟨by omega, hkk⟩)

end Erdos1094
