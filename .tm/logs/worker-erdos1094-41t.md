# timtam Task: Formalize large prime divisibility criterion (erdos1094-41t)

Role: formalize
Agent: formalize (anthropic/claude-opus-4-6:high)
Start Time: 2026-02-08T10:00:16.514Z

## Agent Interaction





> **Thinking:**
> Let me start by understanding the task. I need to formalize a theorem about large prime divisibility of binomial coefficients. Let me first read the relevant proof file and understand the current state of the project.


```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-41t --status "Reading NL proof and exploring project structure"
```

🛠️ **Executing tool: read**

```bash
$ cd /home/jarred/code/erdos-1094 && find . -name "*.lean" | head -20
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat lakefile.lean
```

```bash
$ cd /home/jarred/code/erdos-1094 && ls lakefile* lean-toolchain 2>/dev/null
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**


> **Thinking:**
> Now I understand the project structure. I need to create `Erdos/LargePrime.lean` with the theorem `large_prime_dvd_choose`. The NL proof is verified.
> 
> The key approach from the NL proof is:
> - When p > k, the single base-p digit of k is k itself
> - So the digit-domination criterion reduces to: p ∣ C(n,k) ↔ n % p < k
> 
> Let me think about the proof strategy in Lean. I can use the `kummer_criterion_core` from `Erdos/Kummer.lean` which says:
> 
> 
> p ∣ n.choose k ↔ ∃ i, k / p ^ i % p > n / p ^ i % p
> 
> Since p > k, for i = 0 we get k % p = k and n % p, while for i ≥ 1 the quotient k / p^i becomes 0. This means the existential condition simplifies to just checking whether k > n % p.
> 
> Now I need to look at what's available in Mathlib and construct the formal proof.


```bash
$ cd /home/jarred/code/erdos-1094 && cat lakefile.toml
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat lean-toolchain
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-41t --status "Exploring Mathlib API for needed lemmas"
```


> **Thinking:**
> My strategy: use `kummer_criterion_core` from `Erdos/Kummer.lean`. It says:
> 
> ```
> p ∣ n.choose k ↔ ∃ i, k / p ^ i % p > n / p ^ i % p
> ```
> 
> When k < p:
> - For i = 0: k / 1 % p = k % p = k, and n / 1 % p = n % p. So the condition is k > n % p, i.e., n % p < k.
> - For i ≥ 1: k / p^i = 0 (since k < p ≤ p^i), so 0 % p = 0, which is never > anything non-negative.
> 
> 
> So the existential reduces to just the i=0 case. But I'm realizing `kummer_criterion_core` is private, and while `kummer_criterion` is public, it uses `Nat.digits` and `getD` which might complicate things. I could either make the core lemma non-private, prove it directly from scratch, or work with the public version—let me think through which approach makes sense here.
> 
> Actually, the task suggests proving it directly is simpler than relying on Kummer's criterion. Looking at the natural language proof, the key insight is that p divides C(n,k) exactly when ⌊n/p⌋ > ⌊(n-k)/p⌋, which is equivalent to n % p < k. I should explore what's available in Mathlib—either translating the digit condition from the public `kummer_criterion`, or proving directly using `prime_dvd_choose_small` and the structure of binomial coefficients.
> 
> Let me try a self-contained approach using Lucas' theorem instead. Since k < p, the base-p representation of k is just the single digit k, so by Lucas' theorem modulo p, C(n,k) ≡ C(n % p, k) · C(⌊n/p⌋, 0) ≡ C(n % p, k) (mod p), which means p divides C(n,k) if and only if p divides C(n % p, k), and that happens exactly when n % p < k.
> 
> The challenge is that the relevant lemmas in Mathlib are private, so I need to either find what's publicly available or prove the necessary pieces from scratch.


```bash
$ cd /home/jarred/code/erdos-1094 && grep -r "choose_modEq_choose_mod_mul_choose_div" .lake/packages/mathlib/Mathlib/ --include="*.lean" -l | head -5
```

```bash
$ cd /home/jarred/code/erdos-1094 && grep -r "factorization_choose_eq_zero_of_lt" .lake/packages/mathlib/Mathlib/ --include="*.lean" -l | head -5
```

```bash
$ cd /home/jarred/code/erdos-1094 && grep -rn "choose_modEq_choose_mod_mul_choose_div" .lake/packages/mathlib/Mathlib/ --include="*.lean" | head -10
```

🛠️ **Executing tool: read**


> **Thinking:**
> Good. Now let me plan the proof:
> 
> 1. Use Lucas' theorem: `choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [MOD p]`
> 2. Since k < p, k % p = k and k / p = 0
> 3. So `choose n k ≡ choose (n % p) k * choose (n / p) 0 ≡ choose (n % p) k * 1 ≡ choose (n % p) k [MOD p]`
> 
> 
> 4. Now I need to show that p divides choose (n%p) k exactly when n%p < k. The lemma I need is private, so I'll reconstruct it using the factorization properties and the fact that choose equals zero when the first argument is smaller than the second.
> 
> Let me check what's available in the library first.


```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_check.lean << 'EOF'
import Mathlib

-- Check key lemmas
#check @Choose.choose_modEq_choose_mod_mul_choose_div_nat
#check Nat.factorization_choose_eq_zero_of_lt
#check Nat.choose_eq_zero_of_lt
#check Nat.choose_pos
#check Nat.Prime.dvd_iff_one_le_factorization
#check Nat.Modeq.dvd_iff
#check Nat.ModEq
#check Nat.choose_self
#check Nat.choose_zero_right
#check Nat.div_eq_of_lt
#check Nat.mod_eq_of_lt

variable (n p k : ℕ) (hp : p.Prime) (hpk : k < p)
#check @Nat.mod_eq_of_lt k p hpk
#check @Nat.div_eq_of_lt k p hpk
EOF
lake env lean /tmp/api_check.lean 2>&1 | head -30
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_check2.lean << 'EOF'
import Mathlib

-- Check ModEq dvd interaction
#check Nat.ModEq.dvd_iff'
#check @Nat.modEq_iff_dvd'

-- Check how to go from modEq to dvd
example (a b p : ℕ) (h : a ≡ b [MOD p]) (hb : p ∣ b) : p ∣ a := by
  exact?
EOF
lake env lean /tmp/api_check2.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-1094 && grep -rn "ModEq.*dvd" .lake/packages/mathlib/Mathlib/Data/Nat/Defs.lean --include="*.lean" 2>/dev/null | head -10
grep -rn "def.*ModEq" .lake/packages/mathlib/Mathlib/Data/Nat/Mods/ --include="*.lean" 2>/dev/null | head -10
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_check3.lean << 'EOF'
import Mathlib

-- The modEq_nat approach
example (a b p : ℕ) (h : a ≡ b [MOD p]) : p ∣ a ↔ p ∣ b := by
  exact (Nat.ModEq.comm.mp h).dvd_iff

-- Key fact: since k < p, choose (n%p) k is what matters
-- We need: for a < p prime, p ∣ choose a k ↔ a < k
-- When a < k: choose a k = 0 which is divisible
-- When k ≤ a < p: choose a k > 0 and factorization = 0

example (p n k : ℕ) (hp : p.Prime) (hpk : k < p) (hn : n % p < k) :
    p ∣ (n % p).choose k := by
  rw [Nat.choose_eq_zero_of_lt hn]

example (p n k : ℕ) (hp : p.Prime) (hpk : k < p) (hn : ¬ n % p < k) (hkn : k ≤ n) :
    ¬ p ∣ (n % p).choose k := by
  push_neg at hn
  have hpos : 0 < (n % p).choose k := Nat.choose_pos hn
  have hfact : ((n % p).choose k).factorization p = 0 :=
    Nat.factorization_choose_eq_zero_of_lt (Nat.mod_lt n hp.pos)
  intro hdvd
  have := (hp.dvd_iff_one_le_factorization hpos.ne').mp hdvd
  omega
EOF
lake env lean /tmp/api_check3.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_check4.lean << 'EOF'
import Mathlib

-- Fix the dvd_zero and modEq.dvd approach
example (a b p : ℕ) (h : a ≡ b [MOD p]) : p ∣ a ↔ p ∣ b := by
  unfold Nat.ModEq at h
  constructor <;> intro hd
  · rwa [← Nat.mod_eq_zero_iff_dvd, ← h, Nat.mod_eq_zero_iff_dvd]
  · rwa [← Nat.mod_eq_zero_iff_dvd, h, Nat.mod_eq_zero_iff_dvd]

#check @Nat.ModEq
-- Nat.ModEq n a b = (a % n = b % n)
EOF
lake env lean /tmp/api_check4.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_check5.lean << 'EOF'
import Mathlib

-- ModEq is a % n = b % n
-- dvd: n ∣ a ↔ a % n = 0

example (a b p : ℕ) (hp : 0 < p) (h : a ≡ b [MOD p]) : p ∣ a ↔ p ∣ b := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  unfold Nat.ModEq at h
  rw [h]

-- Good! Now let's figure out the full approach
-- Lucas: choose n k ≡ choose (n%p) (k%p) * choose (n/p) (k/p) [MOD p]
-- k < p  →  k%p = k, k/p = 0
-- choose (n/p) 0 = 1
-- So choose n k ≡ choose (n%p) k * 1 = choose (n%p) k [MOD p]
-- Then p ∣ choose n k ↔ p ∣ choose (n%p) k
-- And n%p < p, so:
--   If n%p < k: choose (n%p) k = 0, so p ∣ 0  ✓
--   If k ≤ n%p: choose (n%p) k has factorization p = 0, so p ∤ choose (n%p) k

-- Let's also check dvd_zero
example (p : ℕ) : p ∣ 0 := dvd_zero p
EOF
lake env lean /tmp/api_check5.lean 2>&1 | head -20
```
Good, the approach works. Now let me write the full proof:
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-41t --status "Writing LargePrime.lean proof"
```

🛠️ **Executing tool: write**

```bash
$ cd /home/jarred/code/erdos-1094 && lake env lean Erdos/LargePrime.lean 2>&1
```
It

> **Thinking:**
>  compiles with just an unused variable warning for `hkn`. The `hkn : k ≤ n` is part of the required signature but isn't needed in the proof (since the divisibility condition handles both cases). I should keep it in the signature as required but suppress the warning.
> 
> Actually, let me think: is `hkn` really not needed? The statement says `p ∣ n.choose k ↔ n % p < k`. If k > n, then C(n,k) = 0, so p ∣ 0 is always true. And we'd need n % p < k, which... well if k > n ≥ n%p then it would be true too. 
> 
> The task requires the signature with `hkn`, so I'll keep it and just rename it with an underscore prefix to suppress the warning.

The file compiles. The warning is about ` onlyhkn` being unused — this is because the proof works even without the `k ≤ n` hypothesis, but the task specifies it in the signature. Let me clean up the unused variable:
🛠️ **Executing tool: edit**


> **Thinking:**
> Wait, the task says the required statement has `hkn`. Let me check if changing it to `_hkn` is acceptable. The external API is the same - the parameter name in the signature doesn't change the theorem's type. Let me verify it compiles cleanly.


```bash
$ cd /home/jarred/code/erdos-1094 && lake env lean Erdos/LargePrime.lean 2>&1
```
Clean compile, no warnings. Now let me add the import to the main file and do a full `lake build`:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-1094 && lake build 2>&1
```
`lake build` succeeds. The only warning is the pre-existing `sorry` in `Erdos/Basic.lean` (the main theorem). `Erdos/LargePrime.lean` compiles clean with no sorries.

Let me verify the final file:
🛠️ **Executing tool: read**
Now let me update the task status:
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-41t --status "Complete - lake build succeeds, no sorry"
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm close erdos1094-41t
```
```json
{
  "status": "completed",
  "summary": "Closed all goals in large_prime_dvd_choose. lake build succeeds with no sorry in LargePrime.lean.",
  "details": "Created Erdos/LargePrime.lean with the theorem:\n\n  theorem large_prime_dvd_choose (p n k : ℕ) (hp : p.Prime) (hpk : k < p) (_hkn : k ≤ n) :\n    p ∣ n.choose k ↔ n % p < k\n\nProof approach (following the verified NL proof's alternative method via Lucas):\n1. Applied Mathlib's `Choose.choose_modEq_choose_mod_mul_choose_div_nat` (Lucas' theorem): C(n,k) ≡ C(n%p, k%p) * C(n/p, k/p) [MOD p]\n2. Since k < p: simplified k%p = k, k/p = 0, giving C(n,k) ≡ C(n%p, k) [MOD p]\n3. Transferred divisibility across the ModEq\n4. Resolved using a helper lemma `prime_dvd_choose_of_lt`: for a < p prime, p ∣ C(a,b) ↔ a < b, proved via `Nat.factorization_choose_eq_zero_of_lt` (for the ← direction) and `Nat.choose_eq_zero_of_lt` (for the → direction)\n\nNo new sorry holes introduced. Total proof is ~25 lines of tactic code across 3 lemmas."
}
```

## Final Result

```json
{
  "status": "completed",
  "summary": "Closed all goals in large_prime_dvd_choose. lake build succeeds with no sorry in LargePrime.lean.",
  "details": "Created Erdos/LargePrime.lean with the theorem:\n\n  theorem large_prime_dvd_choose (p n k : ℕ) (hp : p.Prime) (hpk : k < p) (_hkn : k ≤ n) :\n    p ∣ n.choose k ↔ n % p < k\n\nProof approach (following the verified NL proof's alternative method via Lucas):\n1. Applied Mathlib's `Choose.choose_modEq_choose_mod_mul_choose_div_nat` (Lucas' theorem): C(n,k) ≡ C(n%p, k%p) * C(n/p, k/p) [MOD p]\n2. Since k < p: simplified k%p = k, k/p = 0, giving C(n,k) ≡ C(n%p, k) [MOD p]\n3. Transferred divisibility across the ModEq\n4. Resolved using a helper lemma `prime_dvd_choose_of_lt`: for a < p prime, p ∣ C(a,b) ↔ a < b, proved via `Nat.factorization_choose_eq_zero_of_lt` (for the ← direction) and `Nat.choose_eq_zero_of_lt` (for the → direction)\n\nNo new sorry holes introduced. Total proof is ~25 lines of tactic code across 3 lemmas."
}
```

End Time: 2026-02-08T10:04:30.199Z
