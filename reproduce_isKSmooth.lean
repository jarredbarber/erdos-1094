import Erdos.KLe28

open Nat

namespace Erdos1094

lemma isKSmooth_of_all_factors_le (m k : ℕ) (hm : m > 0)
    (h : ∀ p, p.Prime → p ∣ m → p ≤ k) : isKSmooth m k = true := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [isKSmooth]
    simp only [hm, ite_false] -- m > 0 => m != 0
    split_ifs with h1 h2 h3
    · -- m = 1
      rfl
    · -- m <= k
      rfl
    · -- m > k
      -- h3: m.minFac > k
      exfalso
      have p_prime : m.minFac.Prime := Nat.minFac_prime (ne_of_gt (lt_of_le_of_lt (zero_le k) (lt_of_not_le h2)))
      have p_dvd : m.minFac ∣ m := Nat.minFac_dvd m
      have p_le_k := h m.minFac p_prime p_dvd
      linarith
    · -- Recursive step
      -- h3: ¬(m.minFac > k) => m.minFac <= k
      apply ih (m / m.minFac)
      · apply Nat.div_lt_self hm
        exact Nat.minFac_prime (ne_of_gt (lt_of_le_of_lt (zero_le k) (lt_of_not_le h2))).one_lt
      · exact Nat.div_pos (Nat.minFac_le m) (Nat.pos_of_ne_zero (ne_of_gt hm))
      · intro p hp hp_dvd
        apply h p hp (dvd_trans hp_dvd (Nat.div_dvd_of_dvd (Nat.minFac_dvd m)))


end Erdos1094
