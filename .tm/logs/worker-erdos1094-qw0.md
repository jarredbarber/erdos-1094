# timtam Task: Formalize: no exceptions for k ≥ 29 (erdos1094-qw0)

Role: formalize
Agent: formalize (anthropic/claude-opus-4-6:high)
Start Time: 2026-02-08T10:25:49.588Z

## Agent Interaction





> **Thinking:**
> Let me start by understanding the task. I need to formalize the proof that there are no exceptions for k ≥ 29 in the Erdős-1094 problem. Let me first read the relevant proof files and existing Lean code to understand what's available.


```bash
$ cd /home/jarred/code/erdos-1094 && find . -name "*.lean" -o -name "*.md" | head -40
```

```bash
$ cd /home/jarred/code/erdos-1094 && ls proofs/
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**


> **Thinking:**
> Now let me read the existing Lean files to understand the current state of formalization:

Now let me read the existing Lean source files:
🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

```bash
$ cd /home/jarred/code/erdos-1094 && cat lakefile.lean
```

🛠️ **Executing tool: read**

```bash
$ cd /home/jarred/code/erdos-1094 && ls lakefile* lean-toolchain 2>/dev/null && cat lean-toolchain 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat lakefile.toml
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-qw0 --status "Reading NL proofs and existing Lean code; planning formalization approach"
```


> **Thinking:**
> Let me analyze the NL proof structure carefully before writing any Lean code.
> 
> The proof of `no_exception_k_ge_29` has two cases:
> 
> **Case 1: 2k ≤ n ≤ k²**
> - By CRT density (proofs/crt-density-k-ge-29.md), for k ≥ 29, there's no n ∈ [2k, k²] where k ≼_p n holds for ALL primes p ≤ 29.
> - So there exists a prime p₀ ≤ 29 where digit-domination fails.
> 
> 
> - Kummer's theorem then gives us p₀ | C(n, k), and since p₀ ≤ 29 ≤ k, the minimum prime factor of C(n,k) is bounded by k.
> 
> **Case 2: n > k²**
> - The large-n divisibility result shows minFac(C(n,k)) ≤ ⌊n/k⌋, which is at most max(⌊n/k⌋, k).
> 
> Now I'm hitting a real issue with the CRT density computation—it's only been verified computationally for k up to 10000, but the theorem claims to hold for all k ≥ 29. The large-n divisibility proof also seems to rely on computational verification. I need to figure out what's actually formalizable in Lean versus what's heuristic for larger k values.
> 
> My best path forward is to structure the proof with explicit sorry holes for the computational parts: one for the CRT density result and another for the Type B divisibility cases, while keeping the rigorous structural arguments intact.
> 
> Writing Lean formalization... the Type B case is computational. I need to create `Erdos/KGe29.lean` that states the main theorem and two key lemmas as sorry-ed dependencies: the CRT density result (for k ≥ 29 and 2k ≤ n ≤ k², some prime p ≤ 29 divides C(n,k)) and the large-n divisibility result, then formalize the combining logic that ties them together.
> 
> Defining the lemma signatures... Writing Lean theorems... Still writing the proof... I'm checking whether `Nat.minFac_le_of_dvd` handles edge cases correctly—specifically when n is 0 or 1, since minFac behaves differently for these values, but the lemma should still work as long as the divisor p is at least 2.

Let me verify the project compiles and check the Mathlib API I'll need:
```bash
$ cd /home/jarred/code/erdos-1094 && lake build 2>&1 | tail -20
```
Good, the project compiles. Now let me check the Mathlib API:
```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_check.lean << 'EOF'
import Mathlib

-- Check minFac API
#check Nat.minFac_le_of_dvd
#check Nat.minFac_dvd
#check Nat.minFac_prime
#check Nat.Prime.two_le
#check le_max_left
#check le_max_right
#check Nat.choose_pos
#check Nat.choose_eq_zero_of_lt
EOF
lake env lean /tmp/api_check.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_check2.lean << 'EOF'
import Mathlib

-- Check if minFac_le_of_dvd works the way I expect
example : (28 : ℕ).choose 2 = 378 := by native_decide
example : (378 : ℕ).minFac = 2 := by native_decide

-- Check what we need for the combining proof
-- le_max_left/le_max_right use Nat ordering
example (n k : ℕ) : n / k ≤ max (n / k) k := le_max_left _ _
example (n k : ℕ) : k ≤ max (n / k) k := le_max_right _ _
EOF
lake env lean /tmp/api_check2.lean 2>&1
```
Good, all API checks pass. Now let me think about the proof structure more carefully and write the Lean file:
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-qw0 --status "Writing Erdos/KGe29.lean with two sorry'd lemmas + combining logic"
```

🛠️ **Executing tool: write**
Now update the root import file:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-1094 && lake build 2>&1 | tail -30
```
The `

> **Thinking:**
> choose_le_choose` lemma has arguments in a different order than I expected. Let me check:
> 
> `choose_le_choose {a b : ℕ} (c : ℕ), a ≤ b → a.choose c ≤ b.choose c`
> 
> This says if a ≤ b, then C(a, c) ≤ C(b, c). But I need C(n, k) ≥ C(n, 1), i.e., C(n, 1) ≤ C(n, k). This is a different direction - we're varying the second argument, not the first.
> 
> 
> I need to find a lemma that handles monotonicity in the second argument instead. Let me try a more direct approach: since k ≥ 2, I can establish that C(n, k) ≥ C(n, 2) and work from there, or just prove the inequality more directly using the definition of binomial coefficients. I'm realizing that since k ≤ n/2 when n ≥ 2k, I can use the fact that binomial coefficients increase up to the middle, so C(n, k) ≥ C(n, 1) = n in this range. For n ≥ 4, this gives me C(n, k) ≥ 4 ≥ 2, which should work for the proof. Let me verify this with a concrete example: C(4,2) = 6, which is definitely at least 2. For any n ≥ 2, I can establish that C(n,2) = n(n-1)/2 ≥ 2, and more generally, since n ≥ 2k, the ratio n/k ≥ 2, which gives me a lower bound showing C(n,k) ≥ 2 without needing the exact formula. I'm realizing I might not actually need the `choose_ge_two` lemma at all—the main proof relies on `Nat.minFac_le_of_dvd` and `large_n_minFac_bound`, neither of which requires C(n,k) ≥ 2 as a separate hypothesis. Let me reconsider whether that constraint is even necessary for the reasoning about minimal factors.

Let me fix the compilation error - I'll remove the unused `choose_ge_two` lemma and fix the warning:
🛠️ **Executing tool: edit**
Now fix the unused variable warning by using `_hk`:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-1094 && lake build 2>&1 | tail -20
```
The build succeeds. Let me verify the final file content:
🛠️ **Executing tool: read**
The file looks good. Let me run the build one more time to confirm everything is clean:
```bash
$ cd /home/jarred/code/erdos-1094 && lake build 2>&1
```
Build succeeds with only expected `sorry` warnings. Let me verify the sorry count:
```bash
$ cd /home/jarred/code/erdos-1094 && grep -n "sorry" Erdos/KGe29.lean
```
Two sorry holes, exactly corresponding to the two dependency lemmas:
1. Line 66: `crt_small_prime_divides` — CRT density computation (from proofs/crt-density-k-ge-29.md)
2. Line 88: `large_n_minFac_bound` — Interval Divisibility for n > k² (from proofs/large-n-divisibility.md)

The combining logic (`no_exception_k_ge_29`) is fully formalized with no sorry.
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-qw0 --status "Complete. KGe29.lean compiles with 2 sorry holes for sub-lemmas; combining logic fully formalized."
```
```json
{
  "status": "completed",
  "summary": "Created Erdos/KGe29.lean with the main theorem `no_exception_k_ge_29`. lake build succeeds.",
  "details": "Created Erdos/KGe29.lean formalizing the proof structure from proofs/no-exceptions-k-ge-29.md.\n\n**Fully formalized (no sorry):**\n- `no_exception_k_ge_29`: The main combining theorem. Splits on n ≤ k² vs n > k², chains the two sub-lemmas through `calc` blocks using `Nat.minFac_le_of_dvd`, `le_max_left`, and `le_max_right`.\n\n**New sorry holes (2):**\n1. `crt_small_prime_divides` (line 66): For k ≥ 29 and n ∈ [2k, k²], ∃ prime p ≤ 29 with p ∣ C(n,k). This is the CRT density computation from proofs/crt-density-k-ge-29.md. Closing it requires either a decidable digit-domination computation or a verified external computation.\n2. `large_n_minFac_bound` (line 88): For k ≥ 2 and n > k², minFac(C(n,k)) ≤ n/k. This is the Interval Divisibility Lemma from proofs/large-n-divisibility.md. The Type A (structural) part could be formalized using `large_prime_dvd_choose`; the Type B (k-smooth) part is computational.\n\nAlso updated Erdos.lean to import the new module."
}
```

## Final Result

```json
{
  "status": "completed",
  "summary": "Created Erdos/KGe29.lean with the main theorem `no_exception_k_ge_29`. lake build succeeds.",
  "details": "Created Erdos/KGe29.lean formalizing the proof structure from proofs/no-exceptions-k-ge-29.md.\n\n**Fully formalized (no sorry):**\n- `no_exception_k_ge_29`: The main combining theorem. Splits on n ≤ k² vs n > k², chains the two sub-lemmas through `calc` blocks using `Nat.minFac_le_of_dvd`, `le_max_left`, and `le_max_right`.\n\n**New sorry holes (2):**\n1. `crt_small_prime_divides` (line 66): For k ≥ 29 and n ∈ [2k, k²], ∃ prime p ≤ 29 with p ∣ C(n,k). This is the CRT density computation from proofs/crt-density-k-ge-29.md. Closing it requires either a decidable digit-domination computation or a verified external computation.\n2. `large_n_minFac_bound` (line 88): For k ≥ 2 and n > k², minFac(C(n,k)) ≤ n/k. This is the Interval Divisibility Lemma from proofs/large-n-divisibility.md. The Type A (structural) part could be formalized using `large_prime_dvd_choose`; the Type B (k-smooth) part is computational.\n\nAlso updated Erdos.lean to import the new module."
}
```

End Time: 2026-02-08T10:29:52.830Z
