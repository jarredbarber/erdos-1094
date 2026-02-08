# timtam Task: Gap analysis: design proof decomposition from exploration (erdos1094-1k9)

Role: advisor
Agent: advisor (anthropic/claude-opus-4-5:high)
Start Time: 2026-02-08T07:43:10.479Z

## Agent Interaction



> **Thinking:**
> Let me start by understanding the current state of the project. I need to:
> 
> 1. Read the sorry in Erdos/Basic.lean to understand the formalization target
> 2. Read proofs/exploration.md for the mathematical analysis
> 3. Read proofs/dead-ends.md for approaches to avoid
> 4. Design the proof decomposition and create tasks
> 
> Let me begin by reading these files.


```bash
$ tm update erdos1094-1k9 --status "Reading sorry goals and exploration results"
```

```bash
$ grep -rn sorry *.lean **/*.lean 2>/dev/null | grep -v '.lake/'
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**
Let me now

> **Thinking:**
>  read the sorry in Basic.lean to understand the exact formalization target:


🛠️ **Executing tool: read**


> **Thinking:**
> Now I have a complete picture:
> 
> **Sorry target:** Prove that `{(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite`
> 
> **Exploration findings:**
> 1. All 14 exceptions satisfy k ≤ 28 and n ≤ 284
> 2. Proof strategy: Show exceptions ⊆ {k ≤ 28, n ≤ 284}, use Set.Finite.subset
> 3. Requires: (a) k ≥ 29 → no exceptions, (b) k ≤ 28 → n ≤ 284
> 
> **Dead ends to avoid:**
> - Single prime arguments
> - Pure counting/size arguments
> - Density arguments alone
> - Bertrand's postulate for single interval
> - Avoiding Kummer's theorem
> 
> Now I need to design the proof decomposition. Based on the exploration, the recommended approach is:
> 
> 1. **Infrastructure**: Kummer's theorem (divisibility conditions in terms of digit-domination)
> 2. **Main bound**: Prove the exceptional set ⊆ {(n,k) : k ≤ 28 ∧ n ≤ 284}
> 3. **Finiteness**: Apply Set.Finite.subset
> 
> The exploration identifies these key results needed:
> 
> **Level 1: Core Kummer infrastructure**
> - Kummer's theorem: v_p(C(n,k)) = #carries when adding k and n-k in base p
> - Equivalently: p ∤ C(n,k) iff k is digit-dominated by n in base p
> 
> **Level 2: Two regimes**
> - Regime 1 (p ≤ k): p | C(n,k) iff digit-domination fails
> 
> 
> - Regime 2 (p > k): p | C(n,k) iff n mod p ≤ k-1
> 
> **Level 3: Main bounds**
> - For k ≥ 29: The CRT constraints from digit-domination for primes 2,3,5,...,29 are too restrictive
> - For k ≤ 28: Explicit bounds on n (all exceptions have n ≤ 284)
> 
> Let me design specific tasks. Each task should target ONE provable mathematical statement.
> 
> ### Task pipeline:
> 
> **EXPLORE TASKS:**
> 
> 1. **Kummer's theorem statement for binomials** - Formalize the carry-counting characterization and its equivalence to digit-domination conditions
> 
> .
> 
> 2. **Regime 2: Large prime divisibility criterion** - For primes exceeding k, divisibility of C(n,k) depends only on the residue class of n modulo p.
> 
> 3. **Digit-domination density bound** - The proportion of integers satisfying digit-domination in a given base p decays exponentially with the number of digits required to represent k.
> 
> 4. **CRT density bound for k ≥ 29** - Simultaneous digit-domination across the first several primes becomes impossible in the range [2k, k²] when k is sufficiently large.
> 
> 5. **Regime 1 divisibility for small primes** - When p ≤ k, the divisibility condition involves comparing digit sequences and becomes more complex than the large-prime case.
> 
> 6. **Regime 2 bound for n > k²** - Beyond the quadratic threshold, Bertrand's postulate guarantees a prime p in the interval (k, n/k] where the residue condition p | C(n,k) holds.
> 
> 7. **Combined bound k ≥ 29** - For sufficiently large k, the existence of a prime divisor of C(n,k) in the range n ≥ 2k follows from combining the small and large prime regimes.
> 
> 8. **Explicit n-bounds for k ≤ 28** - Each small value of k admits a finite upper bound on exceptional n, with all such bounds staying below 284.
> 
> The strategy consolidates around showing the exceptional pairs are confined to k ≤ 28 and n ≤ 284. This splits into two complementary pieces: ruling out exceptions entirely when k ≥ 29, and establishing explicit bounds for k ≤ 28. For k ≥ 29, the Chinese Remainder Theorem density argument applies to the primes up to 29, creating overlapping residue constraints that force a prime divisor of C(n,k) to exist. is finite.
> 
> To establish this, I need to prove two things: first, that k ≥ 29 eliminates all exceptions through CRT density arguments and Bertrand's postulate applied to the prime gap structure; second, that for k ≤ 28, the bound n ≤ 284 captures all remaining cases by analyzing the k consecutive integers and showing that having enough k-smooth terms or large prime divisors becomes impossible beyond this threshold.
> 
> The exploration phase requires understanding Kummer's theorem for binomial coefficients, establishing when large primes divide binomials, characterizing the CRT structure underlying digit-domination, then combining these to rule out k ≥ 29 and deriving the specific bound for smaller k values. Verification tasks check each exploration result, while formalization translates the mathematical arguments into Lean, culminating in the main theorem that unifies both bounds.
> 
> For the actual formalization, the most practical approach appears to be showing all counterexamples fall within n ≤ 300, then applying decidability for that finite range rather than proving the general case directly. This means establishing the mathematical argument for why n > 300 works, then leveraging computation for the remaining cases. The concrete steps involve formalizing Kummer's theorem first, handling the small k cases explicitly, developing the bounding argument for larger k, and determining the specific upper bound N(k) for each intermediate value.
> 
> The exploration should focus on individual mathematical statements without Lean code. I need to identify the key results: Kummer's theorem itself (relating p-adic valuations to carries in base-p addition), the Lucas characterization (when p doesn't divide the binomial coefficient based on digit comparisons), and the criterion for large primes (when p > k determines divisibility through modular arithmetic).
> 
> For the harder cases, I'm looking at two critical statements: one about how the Chinese Remainder Theorem constrains solutions when k is digit-dominated across all small primes, and another establishing that for small k values, sufficiently large n always has some prime dividing the binomial coefficient. The exploration indicates these density arguments—particularly that for k ≥ 29 the solution density becomes too sparse to find valid candidates—are where the real difficulty lies.
> 
> To make progress, I need to establish several foundational results. First, I should prove Kummer's theorem relating the p-adic valuation of binomial coefficients to carries in base-p arithmetic. Then I need the equivalence showing that a prime avoids dividing C(n,k) precisely when k's digits don't exceed n's digits in that base. Finally, I need to handle large primes that must divide C(n,k) when n exceeds certain thresholds.
> 
> The strategy involves showing that for k ≥ 29, the Chinese Remainder Theorem constraints from small primes create an impossible system—no n exists in [2k, k²] satisfying digit-domination simultaneously across bases 2, 3, and 5. For larger n beyond k², Bertrand-style arguments guarantee a prime divisor in the appropriate range that forces divisibility of the binomial coefficient.
> 
> For smaller k values between 3 and 28, a computational or case-by-case verification handles n > 284, establishing the existence of a suitable prime divisor. The overall approach reduces to combining these bounds across different ranges of k and n. from showing the exceptional set ⊆ {k ≤ 28, n ≤ 284}
> - The k ≥ 29 case uses CRT density
> - The k ≤ 28 case uses explicit bounds
> 
> I'll create a focused set of tasks:
> 
> 1. **Kummer + Lucas** - the foundational tool
> 2. **Large prime criterion** - needed for both branches
> 3. **k ≥ 29 case** - CRT density argument
> 4. **k ≤ 28 case** - explicit bounds (may need subdivision)
> 5. **Main theorem** - combine via Set.Finite.subset
> 
> Kummer's theorem is a classical result from 1852, so I could either cite it as an axiom or prove it directly for formalization purposes.
> 
> Now I'll structure this into concrete explore and verify tasks, aiming for 4-5 of each with clear, provable statements and a corresponding formalization plan.

Now let me check the current task state before creating new tasks:
```bash
$ tm list
```
Good

> **Thinking:**
> , I have a clean slate. Let me now design the task pipeline.
> 
> Based on the exploration findings and dead-ends, here's my decomposition:
> 
> ## Proof Strategy Summary
> 
> The main theorem follows from: `exceptional_set ⊆ {(n,k) : k ≤ 28 ∧ n ≤ 284}` + finite bounding set
> 
> This requires two main branches:
> 1. **k ≥ 29 case**: Prove no exceptions exist
> 2. **k ≤ 28 case**: Prove exceptions have n ≤ 284
> 
> ## Task Pipeline
> 
> ### Foundation Layer (Kummer + Divisibility)
> 
> **E1: Kummer/Lucas criterion for binomial divisibility**
> - This is a classical 1852 result
> - For formalization, can use axiom with citation
> 
> **E2: Large prime divisibility criterion**
> - For p > k: p | C(n,k) iff n mod p < k
> 
> ### k ≥ 29 Branch
> 
> **E3: CRT density bound for digit-domination**
> - For k ≥ 29, the CRT constraints are too restrictive
> - Show: no n in [2k, k²] satisfies digit-domination for all primes ≤ 29
> 
> **E4: Large n forces divisibility (Bertrand iteration)**
> - For n > k², there exist multiple primes in (k, n/k]
> - CRT argument: can't avoid all of them
> 
> **E5: Combined k ≥ 29 bound** (depends on E3, E4)
> - Combine to show: k ≥ 29 → no exceptions
> 
> ### k ≤ 28 Branch
> 
> **E6: Explicit bounds for small k**
> - For k ∈ {3,...,28}, prove n ≤ 284
> - May use: near-prime capacity argument or explicit case analysis
> 
> 
> - The final step merges both branches and handles the remaining finite cases through direct verification.


```bash
$ tm update erdos1094-1k9 --status "Designing proof decomposition and creating task pipeline"
```


> **Thinking:**
> Now let me create the explore tasks, then the verify tasks, then outline the formalize pipeline.
> 
> I'll start with the foundation layer:Now

 let me create the task pipeline. I'll start with the foundational explore tasks, then layer the dependencies properly.

### Foundation Layer: Kummer's Theorem and Divisibility Criteria
```bash
$ tm create -t "Prove Kummer/Lucas criterion for prime non-divisibility of binomials" -r explore -p 2 -d "Prove: For prime p and integers n ≥ k ≥ 0, we have p ∤ C(n,k) if and only if every base-p digit of k is ≤ the corresponding base-p digit of n (digit-domination).

Equivalently: v_p(C(n,k)) = number of carries when adding k and (n-k) in base p.

This is Kummer's theorem (1852). Provide a complete proof suitable for formalization. The proof should:
1. Use the formula v_p(m!) = Σ_{i≥1} floor(m/p^i)
2. Show v_p(C(n,k)) = (s_p(k) + s_p(n-k) - s_p(n))/(p-1) where s_p(m) = digit sum in base p
3. Relate this to carry counting

Write to: proofs/kummer-theorem.md"
```
Good

> **Thinking:**
> . Now let me create the verify task for this, and the large prime criterion task.


```bash
$ tm create -t "Review proofs/kummer-theorem.md" -r verify -p 2 --deps erdos1094-58u
```

```bash
$ tm create -t "Prove large prime divisibility criterion for binomials" -r explore -p 2 -d "Prove: For prime p > k and n ≥ k, we have p | C(n,k) if and only if n mod p < k.

Proof approach:
1. Since p > k, we have v_p(k!) = 0
2. v_p(C(n,k)) = v_p(n!) - v_p((n-k)!) - v_p(k!) = v_p(n!/(n-k)!)
3. n!/(n-k)! = n(n-1)...(n-k+1) is the product of k consecutive integers ending at n
4. Since p > k, at most one of these k consecutive integers is divisible by p
5. Exactly one is divisible by p iff there exists m ∈ {n-k+1, ..., n} with p | m
6. This happens iff floor(n/p) > floor((n-k)/p), i.e., n mod p < k

Write to: proofs/large-prime-criterion.md"
```


> **Thinking:**
> Good. Now let me create the verify task for the large prime criterion, and the k ≥ 29 case tasks.


```bash
$ tm create -t "Review proofs/large-prime-criterion.md" -r verify -p 2 --deps erdos1094-a0e
```
Now let me create the k 

> **Thinking:**
> ≥ 29 branch. This is the harder branch, involving CRT density arguments.

### Branch 1: k ≥ 29 Case (No Exceptions Exist)
```bash
$ tm create -t "Prove CRT constraint eliminates all n in [2k, k²] for k ≥ 29" -r explore -p 2 -d "Prove: For k ≥ 29, there is no integer n ∈ [2k, k²] such that k is digit-dominated by n in base p for all primes p ≤ 29.

The argument:
1. For each prime p ≤ 29, the digit-domination condition 'each base-p digit of k ≤ corresponding digit of n' constrains n to certain residue classes mod p^L where L = ceil(log_p(k+1))
2. The density of valid n for a single prime p is ∏_i ((p - d_i(k))/p) where d_i(k) is the i-th base-p digit of k
3. By CRT, the combined constraints mod lcm(2^a, 3^b, 5^c, ..., 29^f) have density δ_k = ∏_{p ≤ 29} (single-prime density)
4. For k = 29, compute δ_29 explicitly and show δ_29 · (29² - 2·29) < 1
5. For k ≥ 30, show δ_k decreases (additional digits create stricter constraints)
6. Conclude: no valid n exists in the interval [2k, k²]

This is a concrete calculation with explicit bounds. Show the density computation for k = 29, 30, and argue monotonicity.

Write to: proofs/crt-density-k-ge-29.md"
```


> **Thinking:**
> Now the second part of the k ≥ 29 case: what happens for n > k²?


```bash
$ tm create -t "Prove n > k² forces some prime in (k, n/k] to divide C(n,k)" -r explore -p 2 -d "Prove: For k ≥ 2 and n > k², there exists a prime p with k < p ≤ n/k such that p | C(n,k).

The argument:
1. For n > k², we have n/k > k, so the interval (k, n/k] is non-empty
2. By Bertrand's postulate (iterated), there exist multiple primes in (k, n/k]
3. For each such prime p, we have p | C(n,k) iff n mod p < k (by large prime criterion)
4. The condition 'n mod p ≥ k for all primes p ∈ (k, n/k]' constrains n via CRT
5. Count primes in (k, n/k] using PNT or Chebyshev bounds: there are ≥ c·(n/k - k)/ln(n/k) primes
6. The probability of avoiding all these primes is ∏_p ((p-k)/p) which decreases exponentially
7. For n > k², show this probability times the interval length gives < 1 valid n per period

The key is that having n/k > k means there are 'enough' primes to cover all residue classes.

Write to: proofs/large-n-divisibility.md"
```


> **Thinking:**
> Good. Now the combined k ≥ 29 bound and its verify tasks.


```bash
$ tm create -t "Review proofs/crt-density-k-ge-29.md" -r verify -p 2 --deps erdos1094-6fs
```

```bash
$ tm create -t "Review proofs/large-n-divisibility.md" -r verify -p 2 --deps erdos1094-5y9
```


> **Thinking:**
> Now let me create the combined k ≥ 29 task that depends on both previous proofs.


```bash
$ tm create -t "Prove no exceptions exist for k ≥ 29 (combine density bounds)" -r explore -p 2 -d "Prove: For k ≥ 29 and n ≥ 2k, there exists a prime p ≤ max(n/k, k) with p | C(n,k).

This combines two prior results:
1. From crt-density-k-ge-29.md: For n ∈ [2k, k²], digit-domination fails for some prime ≤ k
2. From large-n-divisibility.md: For n > k², some prime in (k, n/k] divides C(n,k)

Structure of the proof:
- Case 1: n ∈ [2k, k²]. By (1), there exists prime p ≤ k where digit-domination fails.
  By Kummer, p | C(n,k). Since p ≤ k ≤ max(n/k, k), we're done.
- Case 2: n > k². By (2), there exists prime p ∈ (k, n/k] with p | C(n,k).
  Since p ≤ n/k ≤ max(n/k, k), we're done.

Conclusion: The exceptional set contains no pairs (n, k) with k ≥ 29.

Dependencies: proofs/kummer-theorem.md, proofs/crt-density-k-ge-29.md, proofs/large-n-divisibility.md
Write to: proofs/no-exceptions-k-ge-29.md"
```
Now

> **Thinking:**
>  let me create the verify task for this combined proof, with dependencies on the previous verify tasks.


```bash
$ tm create -t "Review proofs/no-exceptions-k-ge-29.md" -r verify -p 2 --deps erdos1094-liv,erdos1094-2gy,erdos1094-7c8
```


> **Thinking:**
> Now the k ≤ 28 branch. This needs to show that for k ≤ 28, all exceptions have n ≤ 284.

### Branch 2: k ≤ 28 Case (Bound n ≤ 284)
```bash
$ tm create -t "Prove exceptions with k ≤ 28 satisfy n ≤ 284 (near-prime capacity)" -r explore -p 2 -d "Prove: For k ∈ {1, 2, ..., 28} and n > 284, there exists prime p ≤ max(n/k, k) with p | C(n,k).

The strategy uses 'near-prime capacity analysis' from the exploration:

For C(n,k) to avoid all primes ≤ max(n/k, k), each of the k consecutive integers {n-k+1, ..., n} must factor as s·q where:
- s is the k-smooth part (all prime factors ≤ k)  
- q is either 1 or a prime > n/k

Key observations:
1. For q > 1: s = m/q < m·k/n ≤ k (since q > n/k)
2. So each m uses a 'channel' s ∈ {1, 2, ..., k-1} for its smooth part
3. Channel s can support at most one prime q in the range (n/s - k/s, n/s]
4. Total capacity ≈ k · (average primes per channel) ≈ k · Σ_{s<k} 1/(s·ln(n/s))
5. For n large, this capacity falls below k (the requirement)

For n > 284 and k ≤ 28:
- Either n > k² (handled by large-prime iteration) OR
- n ∈ (284, k²] requires explicit analysis for each k

Show that for each k ≤ 28, the capacity argument or direct verification gives n ≤ 284.

Write to: proofs/bound-n-for-small-k.md"
```
Now

> **Thinking:**
>  the verify task for this.


```bash
$ tm create -t "Review proofs/bound-n-for-small-k.md" -r verify -p 2 --deps erdos1094-w0p
```


> **Thinking:**
> Now the final combination task: combine both branches to prove the main theorem.

### Main Theorem: Combine Both Branches
```bash
$ tm create -t "Prove finiteness of exceptional set (combine k≥29 and k≤28 bounds)" -r explore -p 1 -d "Prove: The set {(n,k) : 0 < k, 2k ≤ n, minFac(C(n,k)) > max(n/k, k)} is finite.

This combines the two established bounds:
1. From no-exceptions-k-ge-29.md: k ≥ 29 → no exceptions
2. From bound-n-for-small-k.md: k ≤ 28 → exceptions have n ≤ 284

The proof:
1. Let E = {(n,k) : 0 < k ∧ 2k ≤ n ∧ minFac(C(n,k)) > max(n/k, k)}
2. If (n,k) ∈ E, then k ≤ 28 (by contrapositive of result 1)
3. If (n,k) ∈ E, then n ≤ 284 (by result 2 applied to k ≤ 28)
4. Therefore E ⊆ {(n,k) : k ≤ 28 ∧ n ≤ 284}
5. The bounding set {(n,k) : k ≤ 28 ∧ n ≤ 284} is finite (28 × 284 = 7952 elements)
6. By Set.Finite.subset, E is finite

Conclusion: The exceptional set is finite, completing the proof of Erdős 1094.

Dependencies: proofs/no-exceptions-k-ge-29.md, proofs/bound-n-for-small-k.md
Write to: proofs/main-theorem.md"
```


> **Thinking:**
> Now the verify task for the main theorem.


```bash
$ tm create -t "Review proofs/main-theorem.md" -r verify -p 1 --deps erdos1094-sac,erdos1094-gca,erdos1094-8tg
```


> **Thinking:**
> Now let me create the formalize tasks. These will depend on the verify tasks completing successfully.

### Formalize Pipeline

Now let me create the formalization tasks:
```bash
$ tm create -t "Formalize Kummer/Lucas criterion for binomial divisibility" -r formalize -p 2 -d "Formalize the Kummer/Lucas criterion from proofs/kummer-theorem.md.

Target location: Erdos/Kummer.lean (new file)

Required statement:
  theorem kummer_criterion (p : ℕ) [Fact p.Prime] (n k : ℕ) (hk : k ≤ n) :
    p ∣ n.choose k ↔ ∃ i, (Nat.digits p k).getD i 0 > (Nat.digits p n).getD i 0

Or equivalently using carries:
  theorem kummer_valuation (p : ℕ) [Fact p.Prime] (n k : ℕ) :
    padicValNat p (n.choose k) = <carry count formula>

Note: Kummer's theorem is a classical result (1852). If Mathlib already has this, use it. If not, it may be acceptable to introduce as an axiom with citation for the main proof, with a sorry for the proof of Kummer itself.

Check Mathlib for: Nat.Prime.multiplicity_choose, lucas_theorem, or similar.

Depends on: proofs/kummer-theorem.md being verified" --deps erdos1094-nii
```


> **Thinking:**
> Now the formalize tasks for the main bounds.


```bash
$ tm create -t "Formalize large prime divisibility criterion" -r formalize -p 2 -d "Formalize the large prime criterion from proofs/large-prime-criterion.md.

Target location: Erdos/LargePrime.lean (new file)

Required statement:
  theorem large_prime_dvd_choose (p n k : ℕ) (hp : p.Prime) (hpk : k < p) (hkn : k ≤ n) :
    p ∣ n.choose k ↔ n % p < k

This is simpler than Kummer and should be directly provable using:
- The fact that n.choose k = (n-k+1) * ... * n / k!
- When p > k, we have p ∤ k!
- Among k consecutive integers, at most one is divisible by p (when p > k)

Depends on: proofs/large-prime-criterion.md being verified" --deps erdos1094-oil
```


> **Thinking:**
> Now the formalize task for the k ≥ 29 bound.


```bash
$ tm create -t "Formalize: no exceptions for k ≥ 29" -r formalize -p 1 -d "Formalize the k ≥ 29 bound from proofs/no-exceptions-k-ge-29.md.

Target location: Erdos/KGe29.lean (new file)

Required statement:
  theorem no_exception_k_ge_29 (n k : ℕ) (hk : 0 < k) (hn : 2 * k ≤ n) (hk29 : 29 ≤ k) :
    (n.choose k).minFac ≤ max (n / k) k

This depends on:
- proofs/crt-density-k-ge-29.md (CRT density eliminates n ∈ [2k, k²])
- proofs/large-n-divisibility.md (large primes cover n > k²)
- Kummer criterion from Erdos/Kummer.lean
- Large prime criterion from Erdos/LargePrime.lean

The formalization may involve:
- A decidable predicate for digit-domination
- Finite computation for the CRT check (for specific k values)
- Prime counting/existence lemmas

Depends on: verification of k≥29 proof + formalization of Kummer/large-prime criteria" --deps erdos1094-gca,erdos1094-419,erdos1094-41t
```
Now the

> **Thinking:**
>  formalize task for k ≤ 28.


```bash
$ tm create -t "Formalize: exceptions with k ≤ 28 have n ≤ 284" -r formalize -p 1 -d "Formalize the k ≤ 28 bound from proofs/bound-n-for-small-k.md.

Target location: Erdos/KLe28.lean (new file)

Required statement:
  theorem bound_n_for_small_k (n k : ℕ) (hk : 0 < k) (hn : 2 * k ≤ n) (hk28 : k ≤ 28) (hn284 : 284 < n) :
    (n.choose k).minFac ≤ max (n / k) k

This may be proven by:
- Case split on k values (for k ≤ 28, there are only 28 cases)
- For each k, use the near-prime capacity argument OR
- For each k, use explicit computation up to some bound + analytical argument beyond

The formalization may involve:
- Decidable predicates for the main condition
- Bertrand's postulate / prime existence lemmas
- Finite computation for boundary cases

Depends on: verification of k≤28 proof + formalization of Kummer/large-prime criteria" --deps erdos1094-8tg,erdos1094-419,erdos1094-41t
```


> **Thinking:**
> Finally, the main formalization task that combines everything.


```bash
$ tm create -t "Close sorry at Basic.lean:15 (erdos_1094) using verified proofs" -r formalize -p 0 -d "Close the main sorry in Erdos/Basic.lean:15.

Target: Complete the proof of erdos_1094:
  theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite

Using the established bounds:
1. Erdos/KGe29.lean: no_exception_k_ge_29 (k ≥ 29 → no exceptions)
2. Erdos/KLe28.lean: bound_n_for_small_k (k ≤ 28 ∧ n > 284 → no exceptions)

The proof structure:
1. Show: exceptional_set ⊆ {(n,k) : k ≤ 28 ∧ n ≤ 284}
   - Use no_exception_k_ge_29 and bound_n_for_small_k as contrapositives
2. The bounding set {(n,k) : k ≤ 28 ∧ n ≤ 284} is finite:
   - Use Finset.product on Finset.range 29 and Finset.range 285
3. Apply Set.Finite.subset

Mathematical reference: proofs/main-theorem.md
Depends on: verification + formalization of both branches" --deps erdos1094-hvy,erdos1094-qw0,erdos1094-7tg
```


> **Thinking:**
> Now let me verify the complete task pipeline and summarize what was created.

Let me verify the complete pipeline:
```bash
$ tm list
```
Let

> **Thinking:**
>  me now create a summary document and close this task.

Let me now update the exploration status and close this task:
```bash
$ tm update erdos1094-1k9 --status "Completed task pipeline creation"
```

🛠️ **Executing tool: read**


> **Thinking:**
> Good, the exploration status is "Draft ✏️". Since this is reference material (not one of the prove targets), I don't need to change it. Let me close this task with a summary.


```bash
$ tm close erdos1094-1k9 -d "Created complete task pipeline with 19 tasks:

**EXPLORE tasks (7):**
- erdos1094-58u: Kummer/Lucas criterion (foundation)
- erdos1094-a0e: Large prime divisibility criterion (foundation)
- erdos1094-6fs: CRT density bound for k≥29
- erdos1094-5y9: Large n forces prime divisor
- erdos1094-liv: Combined k≥29 bound
- erdos1094-w0p: Bound n≤284 for k≤28
- erdos1094-sac: Main theorem (combine both branches)

**VERIFY tasks (7):**
- One for each explore task, properly chained

**FORMALIZE tasks (5):**
- erdos1094-419: Kummer criterion
- erdos1094-41t: Large prime criterion
- erdos1094-qw0: k≥29 bound
- erdos1094-7tg: k≤28 bound
- erdos1094-n3e: Main theorem (close sorry at Basic.lean:15)

**Proof architecture:**
1. Foundation: Kummer + large prime criterion
2. Branch 1 (k≥29): CRT density + Bertrand iteration → no exceptions
3. Branch 2 (k≤28): Near-prime capacity → n≤284
4. Combine: E ⊆ {k≤28, n≤284} is finite

Current sorry count: 1 (Basic.lean:15)
Next step: Execute parallel foundation tasks (erdos1094-58u, erdos1094-a0e)"
```


> **Thinking:**
> Great, task completed. Let me provide the final summary.

```json
{
  "status": "completed",
  "summary": "Created 19 tasks: 7 explore, 7 verify, 5 formalize",
  "details": "Designed complete proof decomposition for Erdős 1094 based on exploration findings.\n\n**Proof Architecture:**\n\n1. **Foundation Layer** (parallel):\n   - Kummer/Lucas criterion: p ∤ C(n,k) ↔ digit-domination\n   - Large prime criterion: for p > k, p | C(n,k) ↔ n mod p < k\n\n2. **Branch 1 (k ≥ 29):**\n   - CRT density: no n ∈ [2k, k²] satisfies digit-domination for all primes ≤ 29\n   - Large n: for n > k², Bertrand iteration forces some prime to divide\n   - Combined: k ≥ 29 → no exceptions\n\n3. **Branch 2 (k ≤ 28):**\n   - Near-prime capacity: for n > 284, cannot fill k channels with valid primes\n   - Result: k ≤ 28 ∧ exception → n ≤ 284\n\n4. **Main Theorem:**\n   - E ⊆ {k ≤ 28, n ≤ 284} → E finite by Set.Finite.subset\n\n**Current state:** 1 sorry (Basic.lean:15)\n\n**Next steps:** Foundation explore tasks (erdos1094-58u, erdos1094-a0e) are unblocked and can run in parallel.",
  "tasks_created": {
    "explore": ["erdos1094-58u", "erdos1094-a0e", "erdos1094-6fs", "erdos1094-5y9", "erdos1094-liv", "erdos1094-w0p", "erdos1094-sac"],
    "verify": ["erdos1094-nii", "erdos1094-oil", "erdos1094-2gy", "erdos1094-7c8", "erdos1094-gca", "erdos1094-8tg", "erdos1094-hvy"],
    "formalize": ["erdos1094-419", "erdos1094-41t", "erdos1094-qw0", "erdos1094-7tg", "erdos1094-n3e"]
  },
  "critical_path": "erdos1094-58u → erdos1094-nii → erdos1094-419 → erdos1094-qw0 → erdos1094-n3e"
}
```

## Final Result

```json
{
  "status": "completed",
  "summary": "Created 19 tasks: 7 explore, 7 verify, 5 formalize",
  "details": "Designed complete proof decomposition for Erdős 1094 based on exploration findings.\n\n**Proof Architecture:**\n\n1. **Foundation Layer** (parallel):\n   - Kummer/Lucas criterion: p ∤ C(n,k) ↔ digit-domination\n   - Large prime criterion: for p > k, p | C(n,k) ↔ n mod p < k\n\n2. **Branch 1 (k ≥ 29):**\n   - CRT density: no n ∈ [2k, k²] satisfies digit-domination for all primes ≤ 29\n   - Large n: for n > k², Bertrand iteration forces some prime to divide\n   - Combined: k ≥ 29 → no exceptions\n\n3. **Branch 2 (k ≤ 28):**\n   - Near-prime capacity: for n > 284, cannot fill k channels with valid primes\n   - Result: k ≤ 28 ∧ exception → n ≤ 284\n\n4. **Main Theorem:**\n   - E ⊆ {k ≤ 28, n ≤ 284} → E finite by Set.Finite.subset\n\n**Current state:** 1 sorry (Basic.lean:15)\n\n**Next steps:** Foundation explore tasks (erdos1094-58u, erdos1094-a0e) are unblocked and can run in parallel.",
  "tasks_created": {
    "explore": ["erdos1094-58u", "erdos1094-a0e", "erdos1094-6fs", "erdos1094-5y9", "erdos1094-liv", "erdos1094-w0p", "erdos1094-sac"],
    "verify": ["erdos1094-nii", "erdos1094-oil", "erdos1094-2gy", "erdos1094-7c8", "erdos1094-gca", "erdos1094-8tg", "erdos1094-hvy"],
    "formalize": ["erdos1094-419", "erdos1094-41t", "erdos1094-qw0", "erdos1094-7tg", "erdos1094-n3e"]
  },
  "critical_path": "erdos1094-58u → erdos1094-nii → erdos1094-419 → erdos1094-qw0 → erdos1094-n3e"
}
```

End Time: 2026-02-08T07:47:43.962Z
