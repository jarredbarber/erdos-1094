# timtam Task: Formalize: exceptions with k ≤ 28 have n ≤ 284 (erdos1094-7tg)

Role: formalize
Agent: formalize (anthropic/claude-opus-4-6:high)
Start Time: 2026-02-08T10:45:28.878Z

## Agent Interaction





> **Thinking:**
> Let me start by understanding the task. I need to formalize a theorem about binomial coefficients where for k ≤ 28 and n > 284, the minimum prime factor of C(n,k) is at most max(n/k, k).
> 
> Let me first read the relevant proof file and understand the existing codebase.


```bash
$ cd /home/jarred/code/erdos-1094 && find . -name "*.lean" | head -30
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat proofs/bound-n-for-small-k.md 2>/dev/null || echo "File not found"
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat CLAUDE.md 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat Erdos.lean
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**


> **Thinking:**
> Now I have a clear picture of the project. Let me understand what I need to do:
> 
> 1. Create a new file `Erdos/KLe28.lean` with the theorem `bound_n_for_small_k`
> 2. The theorem states that for k ≤ 28, n > 284, 0 < k, 2*k ≤ n, we have `(n.choose k).minFac ≤ max (n/k) k`
> 
> The NL proof strategy:
> - Case 0: k ∈ {1, 2} - direct
> 
> 
> - Case 1: k ∈ {3, ..., 16} - since k² ≤ 256 < 284 < n, we have n > k², so Case A applies
> - Case 2: k ∈ {17, ..., 28} - split further:
>   - n > k²: Case A applies (large_n_minFac_bound)
>   - 284 < n ≤ k²: exhaustive verification shows no exceptions
> 
> The exhaustive verification for the remaining cases is computationally intensive, so I need to figure out the most practical approach for formalizing this.
> 
> For the Lean proof, I'll structure it by splitting on k ranges: direct proofs for k ∈ {1, 2}, then leverage the large_n_minFac_bound result for k ∈ {3, ..., 16} since n exceeds k² in those cases. For k ∈ {17, ..., 28}, I'll split between the cases where n > k² (using the bound again) and the remaining range 284 < n ≤ k², which requires verifying computationally that every such pair has a prime p ≤ k dividing the binomial coefficient.
> 
> Since this exhaustive check is a finite decidable problem over bounded natural numbers, I could potentially use native_decide to handle the computation directly, though the universal quantification and binomial coefficient calculations might require some careful formulation to make it work with Lean's decision procedures. choose k).minFac ≤ max (n / k) k universally over all n and k. Since n is unbounded, I need a structural argument: for n > k², use the existing bound, and for k ≤ 16 where n > 284 > k², we're always in the large case. For k between 17 and 28 where n might fall in the range (284, k²], I could reformulate this as a finite verification problem over roughly 2800 total cases—checking the bound on n.choose k.minFac for each combination of k and n in that range.
> 
> The key insight is that this comparison is decidable since we're comparing natural numbers, and the quantification is over finite sets, so I can leverage Lean's `Decidable` instances and potentially use `native_decide` for the computational verification.
> 
> Now I'm structuring the proof by cases: either n > k² or n ≤ k². For the first case, I can apply the `large_n_minFac_bound` lemma to show the bound holds. For the second case where n ≤ k², I need to establish that k must be at least 17 since 284 < n.
> 
> Handling the finite case with interval_cases...
> 
> For k ∈ [17, 28], that's 12 cases, and for each one n ranges up to k² ≤ 784, which could generate thousands of goals total. Instead, I should express this as a decidable proposition and use native_decide to handle the finite check directly. The core insight is that for any n in the range (284, k²] with k in that interval, there's always a prime p ≤ k dividing C(n,k).
> 
> Let me formalize this with a lemma that quantifies over the finite sets directly—using Finset.Icc for k and Finset.Ioc for n—and then apply native_decide to verify the property holds across all these cases at once. I'm realizing that `native_decide` might struggle with the computational complexity here—computing `Nat.choose 784 28` produces an astronomically large number, and while `Nat.minFac` should find small prime factors quickly, the sheer size of these binomial coefficients could make this approach impractical. C(784, 28) has roughly 28 * log10(784/14) ≈ 28 * 1.75 ≈ 49 digits. That's a big number but GMP handles it fine. And checking if 2 divides it is trivial.
> 
> For each (n, k) pair, we compute C(n, k) and then check minFac. Since there are ~2810 pairs and each check is fast (the minFac is always small), `native_decide` should work. The precondition 2*k ≤ n is automatically satisfied for all n > 284 and k ≤ 28, so we don't need to worry about it.
> 
> Now I'm sketching out the full proof structure with a case split on whether n > k².
> 
> Continuing with the proof...
> 
> I need to handle the k = 1 case separately since `large_n_minFac_bound` requires k ≥ 2. When k = 1, the binomial coefficient is just n, and I need to verify that minFac(n) ≤ n, which follows from `Nat.minFac_le` as long as n ≠ 1 (which is guaranteed since n > 284).
> 
> For k = 2, the binomial coefficient is n(n-1)/2, which is always even since one of n or n-1 must be even, so minFac equals 2 and satisfies the bound.
> 
> For k ≥ 3, I can split into two cases: when k ≤ 16, we have k² < 284 < n so I can apply the structural bound directly, and when k ≥ 17, I need to handle the boundary cases more carefully.
> 
> Defining the Lean theorem... I'm realizing the pattern matching approach is getting unwieldy, so I'm switching to a cleaner strategy using omega and interval_cases to handle the finite cases more directly.
> 
> Now I'm structuring the proof by first handling the base case where k = 1, then splitting into two main scenarios: when n exceeds k², I can apply the existing large_n_minFac_bound lemma, and when n stays within k², I need to handle that separately.
> 
> For the constrained case where n ≤ k², I've established that k must be at least 17 since larger values of k would make k² too small to contain n > 284. This reduces the problem to a finite verification: checking all pairs where k ranges from 17 to 28 and n falls between 285 and k². I'm planning to use interval_cases to systematically verify each value of k. ∀ n ∈ Finset.Icc 285 784, (n.choose 28).minFac ≤ max (n / 28) 28
> 
> This is decidable over the finite range, so I can prove it directly with `native_decide`. The tricky part is that `interval_cases k` will give me concrete values for k, but n stays as a variable, so I need a helper lemma that uses `native_decide` to verify the inequality for all n in the specific range determined by each k value.
> 
> Writing helper lemma... I need to verify that this approach is actually decidable—the `Finset.decidableBAll` instance should handle the nested quantifiers over the finite sets, and while the largest binomial coefficient C(784, 28) is enormous (around 10^49), computing it and finding its smallest prime factor should still be feasible since most binomial coefficients are even. k) is odd? Then minFac would need to try 3, 5, etc. But the NL proof guarantees that some small prime divides it. So the worst case is trying up to k ≤ 28, which means at most ~10 trial divisions. That's very fast.
> 
> Actually, `Nat.minFac` works as follows: it checks divisibility by 2, then 3, 5, 7, ... (odd numbers). So for each (n, k), the computation is: compute C(n, k), then find its smallest factor. Even for a 50-digit number, trial division by small primes is essentially instant.
> 
> The total computation is ~2810 binomial coefficient computations and minFac checks. Each binomial coefficient C(n, k) with n ≤ 784 and k ≤ 28 involves at most 28 multiplications and divisions, which should run in milliseconds with native code.
> 
> Now I need to set up the Lean file structure. I'll add a new module `Erdos.KLe28` to the existing project that imports the other modules, and I should check what Mathlib lemmas are available for working with `Nat.minFac` to establish the divisibility properties I need.


```bash
$ cd /home/jarred/code/erdos-1094 && cat lakefile.lean
```

```bash
$ cd /home/jarred/code/erdos-1094 && lake build 2>&1 | tail -20
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat lakefile.toml
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-7tg --status "Exploring API and planning proof structure"
```
Let

> **Thinking:**
>  me check the available Mathlib API for the key lemmas I'll need.

Let me explore the key Lean/Mathlib API I'll need:
```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test.lean << 'EOF'
import Mathlib

-- Check key lemmas exist
#check Nat.minFac_le
#check Nat.minFac_le_of_dvd
#check Nat.choose_one_right
#check Nat.minFac_prime
#check Finset.Icc
#check Nat.choose_pos
EOF
lake env lean /tmp/api_test.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test2.lean << 'EOF'
import Mathlib

-- Check decidability of Finset.forall
#check @Finset.decidableBAll
-- Check minFac properties
#check Nat.minFac_eq_one_iff
#check @Nat.minFac_dvd
-- Check if native_decide works with choose and minFac
example : (10 : ℕ).choose 3 = 120 := by native_decide
example : (120 : ℕ).minFac = 2 := by native_decide
-- Test a small finite check
example : ∀ n ∈ Finset.Icc 5 10, (n.choose 2).minFac ≤ n / 2 := by native_decide
EOF
lake env lean /tmp/api_test2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test3.lean << 'EOF'
import Mathlib

-- Test the finite check pattern
example : ∀ n ∈ Finset.Icc 5 10, (n.choose 2).minFac ≤ n / 2 := by native_decide

-- Test dependent range
example : ∀ k ∈ Finset.Icc 3 5, ∀ n ∈ Finset.Icc 10 (k * k),
    (n.choose k).minFac ≤ max (n / k) k := by native_decide
EOF
lake env lean /tmp/api_test3.lean 2>&1
```


> **Thinking:**
> Hmm, the `native_decide` says the proposition is false for the test case. Let me check which case fails.


```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test4.lean << 'EOF'
import Mathlib

-- Debug: which cases fail?
#eval do
  let mut failures := #[]
  for k in List.range 3 |>.map (· + 3) do
    for n in List.range (k * k - 10 + 1) |>.map (· + 10) do
      let c := Nat.choose n k
      let mf := c.minFac
      let bound := max (n / k) k
      if mf > bound then
        failures := failures.push (n, k, c, mf, bound)
  return failures
EOF
lake env lean /tmp/api_test4.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-1094 && python3 -c "
from math import comb
from sympy import factorint
for k in range(3, 6):
    for n in range(10, k*k+1):
        c = comb(n, k)
        if c <= 1:
            continue
        mf = min(factorint(c).keys())
        bound = max(n // k, k)
        if mf > bound:
            print(f'FAIL: n={n}, k={k}, C={c}, minFac={mf}, bound={bound}')
" 2>/dev/null || python3 -c "
from math import comb

def min_fac(n):
    if n <= 1: return n
    if n % 2 == 0: return 2
    i = 3
    while i * i <= n:
        if n % i == 0: return i
        i += 2
    return n

for k in range(3, 6):
    for n in range(10, k*k+1):
        c = comb(n, k)
        if c <= 1: continue
        mf = min_fac(c)
        bound = max(n // k, k)
        if mf > bound:
            print(f'FAIL: n={n}, k={k}, C={c}, minFac={mf}, bound={bound}')
"
```


> **Thinking:**
> Right, the test range was wrong. These are actual exceptions to the Erdős conjecture! The theorem we need to prove says n > 284, so these small exceptions don't apply. Let me fix the test.
> 
> The theorem statement is:
> ```
> theorem bound_n_for_small_k (n k : ℕ) (hk : 0 < k) (hn : 2 * k ≤ n) (hk28 : k ≤ 28) (hn284 : 284 < n) :
>     (n.choose k).minFac ≤ max (n / k) k
> 
> 
> ```
> 
> Now I need to run the finite computation check for the correct range where n exceeds 284.


```bash
$ cd /home/jarred/code/erdos-1094 && python3 -c "
from math import comb

def min_fac(n):
    if n <= 1: return n
    if n % 2 == 0: return 2
    i = 3
    while i * i <= n:
        if n % i == 0: return i
        i += 2
    return n

# Test the actual case: k in [17,28], n in [285, k^2]
for k in range(17, 29):
    for n in range(285, k*k+1):
        if 2*k > n: continue
        c = comb(n, k)
        if c <= 1: continue
        mf = min_fac(c)
        bound = max(n // k, k)
        if mf > bound:
            print(f'FAIL: n={n}, k={k}, C(n,k) has minFac={mf}, bound={bound}')

print('Done checking. If no FAIL lines above, all cases pass.')
"
```
Good, the finite computation confirms no exceptions. Now let me test `native_decide` for the actual range:
```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test5.lean << 'EOF'
import Mathlib

-- Test the finite check for the actual range
-- k ∈ [17, 28], n ∈ [285, k²], with 2k ≤ n (always true since 2*28 = 56 ≤ 285)
-- But we need to be careful about what native_decide can handle

-- Start small: just k = 17, n ∈ [285, 289]
example : ∀ n ∈ Finset.Icc 285 289,
    (n.choose 17).minFac ≤ max (n / 17) 17 := by native_decide
EOF
lake env lean /tmp/api_test5.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test6.lean << 'EOF'
import Mathlib

-- Test larger range: k = 28, n ∈ [285, 784]
-- This is 500 values with C(n, 28) which are large numbers
set_option maxHeartbeats 800000 in
example : ∀ n ∈ Finset.Icc 285 784,
    (n.choose 28).minFac ≤ max (n / 28) 28 := by native_decide
EOF
lake env lean /tmp/api_test6.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test7.lean << 'EOF'
import Mathlib

-- Test the full dependent range: all k ∈ [17, 28], n ∈ [285, k²]
set_option maxHeartbeats 2000000 in
example : ∀ k ∈ Finset.Icc 17 28, ∀ n ∈ Finset.Icc 285 (k * k),
    (n.choose k).minFac ≤ max (n / k) k := by native_decide
EOF
lake env lean /tmp/api_test7.lean 2>&1
```
Excellent! `native_decide` handles all finite cases. Now let me verify the full proof structure works:
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-7tg --status "Writing KLe28.lean - proof structure validated, native_decide works for finite cases"
```
Now let me check what API I need for the k=1 case and figure out the overall proof:
```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test8.lean << 'EOF'
import Mathlib

-- Check available APIs for the proof
#check Nat.minFac_le  -- 0 < n → n.minFac ≤ n
#check @le_max_left
#check @le_max_right
#check Nat.choose_one_right -- n.choose 1 = n

-- Check: for k=1, n/1 = n, so max(n/1, 1) = n
-- minFac(n) ≤ n (for n > 0)
-- So minFac(C(n,1)) = minFac(n) ≤ n = max(n/1, 1)
example (n : ℕ) (hn : 284 < n) :
    (n.choose 1).minFac ≤ max (n / 1) 1 := by
  rw [Nat.choose_one_right, Nat.div_one]
  exact le_trans (Nat.minFac_le (by omega)) (le_max_left _ _)
EOF
lake env lean /tmp/api_test8.lean 2>&1
```
Good. Now let me verify the `large_n_minFac_bound` dependency has the right signature:
```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test9.lean << 'EOF'
import Erdos.KGe29

-- Check signature
#check @Erdos1094.large_n_minFac_bound
-- large_n_minFac_bound (n k : ℕ) (hk : 2 ≤ k) (hn : k * k < n) (hkn : k ≤ n)
EOF
lake env lean /tmp/api_test9.lean 2>&1
```
Now let me also check the `nlinarith` usage for proving k ≥ 17:
```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test10.lean << 'EOF'
import Mathlib

-- Test: if k ≤ 28, 284 < n, n ≤ k*k, then 17 ≤ k
example (k n : ℕ) (hk28 : k ≤ 28) (hn284 : 284 < n) (hkk : n ≤ k * k) : 17 ≤ k := by
  nlinarith

-- Test: for k ≥ 2 and n > 284, we have k ≤ n
example (n k : ℕ) (hn : 2 * k ≤ n) (hn284 : 284 < n) : k ≤ n := by omega

-- Test: for k ≤ 16 and n > 284, k*k < n
example (n k : ℕ) (hk : k ≤ 16) (hn284 : 284 < n) : k * k < n := by nlinarith
EOF
lake env lean /tmp/api_test10.lean 2>&1
```
All the pieces work. Let me now write the full proof:
🛠️ **Executing tool: write**

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-7tg --status "Building KLe28.lean - testing compilation"
```

```bash
$ cd /home/jarred/code/erdos-1094 && lake env lean Erdos/KLe28.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test11.lean << 'EOF'
import Mathlib
-- Find the right name for eq_or_gt
#check @eq_or_gt_of_le
#check @Nat.eq_one_or_self_of_prime
-- Actually, for k = 1 case, let's just use omega or interval_cases
example (k : ℕ) (hk : 0 < k) (hk2 : ¬(2 ≤ k)) : k = 1 := by omega
EOF
lake env lean /tmp/api_test11.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat > /tmp/api_test12.lean << 'EOF'
import Mathlib
example (k : ℕ) (hk : 0 < k) : k = 1 ∨ 2 ≤ k := by omega
EOF
lake env lean /tmp/api_test12.lean 2>&1
```

🛠️ **Executing tool: edit**


> **Thinking:**
> Wait, `hk` is `0 < k`, so `hk.eq_or_gt` would give `0 = k ∨ 0 < k`... that's not right. Let me think...
> 
> Actually, for `Nat.lt_iff_add_one_le`, `0 < k` means `1 ≤ k`. We want to split k = 1 vs k ≥ 2. Let me use `rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2`.


🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-1094 && lake env lean Erdos/KLe28.lean 2>&1
```
No errors. Let me now add the import to `Erdos.lean` and run the full build:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-1094 && lake build 2>&1
```
Build succeeds. Let me clean up the linter warnings since they're just style warnings from Mathlib's linter, not actual issues:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-1094 && lake build 2>&1
```
Clean build. Only the expected `sorry` warnings from the existing files remain (those are in `Erdos/Basic.lean` and `Erdos/KGe29.lean`, which are pre-existing). The new `KLe28.lean` has no `sorry` - it's fully proven!

Let me verify the final file:
🛠️ **Executing tool: read**
The proof is clean, well-documented, and fully compiles with no `sorry` holes. Let me commit:
```bash
$ cd /home/jarred/code/erdos-1094 && git add Erdos/KLe28.lean Erdos.lean && git commit -m "Formalize bound_n_for_small_k: k ≤ 28 exceptions have n ≤ 284

New file Erdos/KLe28.lean proves that for k ≤ 28, n > 284, 2k ≤ n:
  (n.choose k).minFac ≤ max (n/k) k

Proof structure:
- k = 1: C(n,1) = n, minFac(n) ≤ n directly
- k ∈ [2,16]: k² ≤ 256 < 284 < n, so large_n_minFac_bound applies
- k ∈ [17,28], n > k²: large_n_minFac_bound applies
- k ∈ [17,28], 284 < n ≤ k²: exhaustive native_decide over 2810 cases

No sorry holes introduced. lake build succeeds."
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-7tg --status "Complete - KLe28.lean compiles, no sorry holes, committed"
```
```json
{
  "status": "completed",
  "summary": "Closed all goals in bound_n_for_small_k (Erdos/KLe28.lean). lake build succeeds with zero new sorry holes.",
  "details": "Created Erdos/KLe28.lean with the theorem bound_n_for_small_k proving that for k ≤ 28, n > 284, and 2k ≤ n, (n.choose k).minFac ≤ max (n/k) k.\n\nProof structure (no sorry holes):\n1. k = 1: C(n,1) = n, so minFac(n) ≤ n = max(n/1, 1) by Nat.minFac_le.\n2. k ∈ [2, 16]: Since k² ≤ 256 < 284 < n, we have n > k². Apply large_n_minFac_bound from Erdos.KGe29.\n3. k ∈ [17, 28], n > k²: Same large_n_minFac_bound applies.\n4. k ∈ [17, 28], 284 < n ≤ k²: Exhaustive finite verification of all 2810 cases via native_decide (private lemma case_b_finite).\n\nThe key insight is that k ≤ 16 forces n > k² (since k² ≤ 256 < 284), and for k ∈ [17,28] the finite range 284 < n ≤ k² ≤ 784 is small enough for native_decide to verify computationally. No new sorry holes were introduced."
}
```

## Final Result

```json
{
  "status": "completed",
  "summary": "Closed all goals in bound_n_for_small_k (Erdos/KLe28.lean). lake build succeeds with zero new sorry holes.",
  "details": "Created Erdos/KLe28.lean with the theorem bound_n_for_small_k proving that for k ≤ 28, n > 284, and 2k ≤ n, (n.choose k).minFac ≤ max (n/k) k.\n\nProof structure (no sorry holes):\n1. k = 1: C(n,1) = n, so minFac(n) ≤ n = max(n/1, 1) by Nat.minFac_le.\n2. k ∈ [2, 16]: Since k² ≤ 256 < 284 < n, we have n > k². Apply large_n_minFac_bound from Erdos.KGe29.\n3. k ∈ [17, 28], n > k²: Same large_n_minFac_bound applies.\n4. k ∈ [17, 28], 284 < n ≤ k²: Exhaustive finite verification of all 2810 cases via native_decide (private lemma case_b_finite).\n\nThe key insight is that k ≤ 16 forces n > k² (since k² ≤ 256 < 284), and for k ∈ [17,28] the finite range 284 < n ≤ k² ≤ 784 is small enough for native_decide to verify computationally. No new sorry holes were introduced."
}
```

End Time: 2026-02-08T10:52:25.332Z
