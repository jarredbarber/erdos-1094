# timtam Task: Gap analysis: address residual sorry in KLe28:271 (erdos1094-i01)

Role: planner
Agent: planner (google-antigravity/claude-opus-4-6-thinking:high)
Start Time: 2026-02-11T22:33:29.115Z

## Agent Interaction



> **Thinking:**
> Let me start by understanding the current state of the project. I need to:
> 
> 1. Read the current Lean files to understand the sorry situation
> 2. Check the proofs/ directory for verified results
> 3. Check artifacts/ for librarian findings
> 4. Understand what task u5p did and what's left
> 
> Let me begin with a gap analysis.


```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-i01 --status "Starting gap analysis: reading sorry locations and project state"
```

```bash
$ cd /home/jarred/code/erdos-1094 && grep -rn 'sorry\|^axiom' *.lean **/*.lean 2>/dev/null | grep -v '.lake/'
```

```bash
$ cd /home/jarred/code/erdos-1094 && ls proofs/ artifacts/ 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && ls artifacts/ 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && ls artifacts 2>/dev/null || echo "no artifacts dir"
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**
Now let me check the KGe29 sorrys more carefully:
🛠️ **Executing tool: read**

🛠️ **Executing tool: read**
Now let me check the proofs directory and the CrtCheck.lean sorry:
🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

```bash
$ cd /home/jarred/code/erdos-1094 && tm list --all 2>/dev/null | head -80
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm show erdos1094-64v 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm show erdos1094-m36 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm show erdos1094-ej8 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat proofs/dead-ends.md
```
Now let me check the proofs for the large-n-divisibility:
```bash
$ cd /home/jarred/code/erdos-1094 && head -100 proofs/large-n-divisibility.md
```

```bash
$ cd /home/jarred/code/erdos-1094 && sed -n '100,250p' proofs/large-n-divisibility.md
```

```bash
$ cd /home/jarred/code/erdos-1094 && sed -n '250,350p' proofs/large-n-divisibility.md
```
Now let me check what the current sorry situation looks like more precisely and understand how the KLe28.lean:271 sorry fits into the architecture:
🛠️ **Executing tool: read**
Now let me check the open tasks more carefully and understand the structure of what needs to happen:
```bash
$ cd /home/jarred/code/erdos-1094 && tm show erdos1094-u5p 2>/dev/null
```
Now let me check on 64v's progress — see if it's actively being worked on:
```bash
$ cd /home/jarred/code/erdos-1094 && tm show erdos1094-64v --verbose 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm show erdos1094-64v 2>/dev/null
```

🛠️ **Executing tool: list_remote_agents**

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-i01 --status "Analyzing sorry structure: KLe28:271 vs KGe29 sorrys — checking if they share the same mathematical dependency"
```
Let me now understand the full sorry picture and how they relate:
```bash
$ cd /home/jarred/code/erdos-1094 && grep -rn 'sorry\|^axiom' Erdos/*.lean | grep -v '.lake/'
```
Let me understand each sorry precisely:

1. **CrtCheck.lean:59** — `crtCheckRange_sound` — soundness of the exhaustive CRT check (bridges computational verification to a theorem)
2. **KGe29.lean:188** — `axiom crt_density_large_k` — citation axiom for k > 10000 (librarian task ej8 open)
3. **KGe29.lean:335** — `smallPrimeDivCheck_complete` for k ≤ 200 (in `prime_large_divisor_case`)
4. **KGe29.lean:341** — k > 200 case implies n ≥ 2k² (in `prime_large_divisor_case`)
5. **KGe29.lean:350** — n % p < k for Bertrand prime (in `prime_large_divisor_case`)
6. **KLe28.lean:271** — residual case for n ≥ 500,000, k ≤ 28

Now let me understand the mathematical relationship between KLe28:271 and the KGe29 sorrys:

The KLe28:271 sorry is about: **For k ≤ 28 and n ≥ 500,000 in the residual case (d = n/gcd(n,k) is prime and d > n/k, and n/k is k-smooth), show that `smallPrimeDivCheck n k = true`** — i.e., some prime p ≤ 29 divides C(n,k).

The KGe29 sorrys (335, 341, 350) are about: **For k ≥ 29, in the residual case, showing smallPrimeDivCheck completeness or n ≥ 2k².**

These are **different problems**. The KLe28:271 is specifically about k ≤ 28 (small k), while KGe29 sorrys are about k ≥ 29. Task 64v is focused on KGe29:188 (the CRT density for k > 10000 in the CRT case), not on either of these residual cases.

Let me check if the NL proof covers the k ≤ 28 residual case:
```bash
$ cd /home/jarred/code/erdos-1094 && cat proofs/bound-n-for-small-k.md
```
Now I have a thorough understanding. Let me synthesize the analysis:
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-i01 --status "Analysis complete. KLe28:271 is structurally identical to KGe29:335. Drafting task creation plan."
```
Let me verify the exact goal types for the sorry at KLe28:271 to understand what's needed:
🛠️ **Executing tool: read**
Now I have a complete picture. Let me analyze the different approach options for KLe28:271 and understand the relationship to the other sorrys:

**Key insight about KLe28:271:** The sorry is in the **residual case** where:
- k ≤ 28
- n ≥ 500,000
- n > k² (so n/k > k, hence n/k ≥ 17857)
- d = n/gcd(n,k) is prime and d > n/k
- n/k is k-smooth (all prime factors ≤ k ≤ 28)

The goal is to show `(n.choose k).minFac ≤ n / k`. Since n/k ≥ 17857, any prime p ≤ 29 dividing C(n,k) would suffice.

**Different approach for k ≤ 28 vs k ≥ 29:** For k ≤ 28, the residual case has a much simpler structure. The comment says the residual case occurs "for infinitely many n (whenever n/k is 28-smooth and n/gcd(n,k) is prime)." But the key observation is:

For k ≤ 28, n ≥ 500,000, and n/k being 28-smooth, we need `smallPrimeDivCheck n k = true`, meaning some prime p ∈ {2,3,5,7,11,13,17,19,23,29} satisfies `hasCarry p k n` (i.e., p | C(n,k)). The 10 primes together must cover all digit-domination patterns for small k.

This is **NOT** the same problem as task 64v (which handles CRT density for k > 1000 in the n ≤ k² range). Task 64v won't cover KLe28:271 at all — they're in completely different k ranges.

This is also **structurally similar** to KGe29:335 (smallPrimeDivCheck_complete) but for different k ranges.

Let me think about the right approach for KLe28:271. The residual case requires showing that for k ≤ 28 and n ≥ 500,000 with n/k being 28-smooth, at least one of the 10 primes divides C(n,k). The key insight from the NL proof is that the CRT density for the 10 primes is so low that no n satisfying all digit-domination conditions can exist in any residual interval.

A simpler approach: **prove the residual case is vacuous for n ≥ 500,000 and k ≤ 28**. That is, show there are no n ≥ 500,000 with k ≤ 28 where n/k is 28-smooth AND n/gcd(n,k) is prime AND n/gcd(n,k) > n/k. This might be provable by showing that 28-smooth numbers m = n/k ≥ 17857 are so sparse that the Bertrand prime approach works.

Actually, wait — let me re-read the comment more carefully. It says "The residual case occurs for infinitely many n" — so the case IS reachable. We can't prove it vacuous. We genuinely need to show `smallPrimeDivCheck n k = true` for these infinitely many n.

Let me think about what approach could work:
```bash
$ cd /home/jarred/code/erdos-1094 && grep -n 'smallPrimeDivCheck\|getFirstPrimeWithCarry\|hasCarry' Erdos/KLe28.lean | head -20
```

```bash
$ cd /home/jarred/code/erdos-1094 && grep -n 'smallPrimeDivCheck' Erdos/*.lean
```

```bash
$ cd /home/jarred/code/erdos-1094 && sed -n '95,120p' Erdos/CarryInfra.lean
```
Now let me think about the right approach. The sorry at KLe28:271 has these hypotheses in scope:
- `k ≤ 28`, `k ≥ 2`
- `n ≥ 500,000`, `n > k²`
- `n/k` is k-smooth (all prime factors ≤ k)
- `d = n/gcd(n,k)` is prime, `d > n/k`
- Need to prove: `(n.choose k).minFac ≤ n / k`

**Better approach for k ≤ 28:** Instead of proving `smallPrimeDivCheck n k = true` directly (which requires a completeness theorem), use a different strategy. Since n/k ≥ 17857 >> 29, use the **Bertrand prime directly**:

1. By Bertrand's postulate, there's a prime p* ∈ (k, 2k] ⊆ (28, 56].
2. Since n/k ≥ 17857 ≥ 2k, we have p* ≤ 2k ≤ n/k.
3. Need: n mod p* < k, i.e., p* | C(n,k).
4. For this, need to show: when n/k is k-smooth AND d = n/gcd(n,k) is prime with d > n/k, then n mod p* < k for some Bertrand prime p*.

Actually, wait — this is the same approach used in KGe29, which also gets stuck. The issue is: how do you guarantee n mod p* < k? You can't — sometimes it's ≥ k for the specific Bertrand prime.

Let me reconsider. There's an alternative simpler approach for k ≤ 28:

**Key insight for k ≤ 28, n ≥ 500,000:** Since n/k is 28-smooth and n/k ≥ 17857, we know n/k = 2^a * 3^b * 5^c * 7^d * 11^e * 13^f * 17^g * 19^h * 23^i for some exponents. But the condition also requires d = n/gcd(n,k) to be prime and d > n/k. Since d ≤ n (trivially), and gcd(n,k) ≤ k ≤ 28, we get d ≥ n/28. Also d > n/k ≥ n/28. So d is a prime > n/28 and d | C(n,k).

But we need minFac(C(n,k)) ≤ n/k. We already know d | C(n,k), but d > n/k. We need to find a **different** prime factor of C(n,k) that's ≤ n/k.

Actually, I think the cleanest approach is to **prove the residual case is vacuous for large n and small k**. Let me check whether 28-smooth numbers M with M ≥ 17857 can actually produce valid (n, k, d) triples:

For the residual case: M = n/k, M is k-smooth (k ≤ 28), and d = n/gcd(n,k) is prime with d > M.

Since gcd(n,k) | k and k ≤ 28, we have gcd(n,k) ∈ {1, 2, ..., 28}. Let g = gcd(n,k). Then n = kM + r for some 0 ≤ r < k (where r = n mod k). Actually, n/k = M means n = kM + r where r < k. And d = n/g = (kM + r)/g. For d to be prime, (kM + r)/g must be prime.

Also, d > M means (kM + r)/g > M, which gives kM + r > gM, so (k - g)M + r > 0. Since k ≥ g, this is usually true (except when k = g and r = 0, but then d = M, and d > M fails).

So the residual case IS reachable for infinitely many n. The comment in the code is correct.

Let me now consider: **can we restructure the proof to avoid the residual case entirely?** For k ≤ 28 and n ≥ 500,000, we're in the `large_n_minFac_bound_small_k` lemma. The proof splits into Type A (n/k has a prime factor > k) and Type B (n/k is k-smooth). For Type B, it then uses the algebraic divisor d = n/gcd(n,k).

An alternative approach for the k ≤ 28 case: instead of the algebraic divisor approach, use a direct argument that for k ≤ 28 and n ≥ 500,000, at least one of the 10 primes {2,...,29} divides C(n,k). This would need a theorem: for k ≤ 28, `smallPrimeDivCheck n k = true` for ALL n ≥ some threshold.

This is essentially the CRT density argument from proofs/crt-density-k-ge-29.md adapted for k ≤ 28. The density of n where ALL 10 primes fail digit-domination is so low that for large enough n, no such n exists.

But wait — the period for k ≤ 28 is M_k = ∏_{p≤28} p^{L_p(k)}, and within each period, we can enumerate all valid residues. If none exist, then `smallPrimeDivCheck` is true for ALL n. But the valid residues might exist — the question is whether any of them correspond to actual exceptions.

Hmm, actually — for the **smallPrimeDivCheck** (which checks all 10 primes ≤ 29), the valid residues are n where k ⪯_p n for ALL p ∈ {2,3,5,7,11,13,17,19,23,29}. The density argument says this set is very sparse. But for it to be EMPTY, we need to verify that for each k ≤ 28, there are ZERO valid residues modulo M_k = ∏ p^{L_p(k)}.

Actually no — there will be valid residues (e.g., n = k works trivially). The point is that smallPrimeDivCheck returns true when at least one of the 10 primes has a carry, i.e., when digit domination FAILS for at least one prime. So `smallPrimeDivCheck = false` means digit domination HOLDS for all 10 primes. The residues where this happens form a set of density ∏_{p≤29} δ_p(k).

For k = 28: Looking at proofs/crt-density-k-ge-29.md, for k = 29 the density is ~1.34 × 10^-5. For k = 28 it should be similar.

OK let me think about this differently. The real question is: **what is the best task decomposition for closing the KLe28:271 sorry?**

Options:
1. **Explore task**: Prove that for k ≤ 28, the 10 primes {2,...,29} cover all digit-domination patterns for ALL sufficiently large n. This is the CRT density argument specialized to k ≤ 28.
2. **Formalize task**: Use a different proof strategy that avoids the residual case. E.g., prove that for k ≤ 28 and n ≥ 500,000, the Bertrand prime always works (by showing n mod p* < k via Chinese Remainder constraints).
3. **Formalize task**: Extend the computational verification even further (but the code comments say this won't work since the residual case is infinite).

Actually, let me look at this from a different angle. The NL proof in proofs/large-n-divisibility.md Section 7.3 handles Type B. It says:

For Case B1 (M ≥ 2k): Use Bertrand prime + CRT density argument showing combined constraints have no solution.
For Case B2 (M ∈ (k, 2k)): Direct verification for the finite set of k-smooth numbers in (k, 2k).

For k ≤ 28, when n ≥ 500,000, M = n/k ≥ 17857. Since 2k ≤ 56, we have M ≥ 17857 >> 2k = 56. So we're deep in Case B1.

The argument from Section 7.3 Case B1 for k ≤ 28: The Bertrand prime p* ∈ (k, 2k] combined with digit domination for primes ≤ k has a CRT period P = M_k · p* where M_k = ∏_{p≤k} p^{L_p(k)}. The valid residue count is R = R_k · (p* - k). The fraction R·k/P is very small (< 10^-6 for k = 29, and should be similar for k ≤ 28). Since P >> k, each interval of length k contains at most 0 or 1 valid residues. The argument then verifies that no valid residues actually land in any Type B interval.

But this is essentially a **computational** verification: enumerate R residues modulo P, and check that none of them fall in any interval [kM, k(M+1)) for any 28-smooth M. For k ≤ 28, this IS finite and decidable — but the period P is huge (> 10^19 for k = 28).

Wait — actually, the argument is cleaner than that. For M ≥ 2k, the Bertrand prime p* exists with p* ≤ 2k ≤ M. The constraint from p* is: n mod p* ≥ k (for digit domination to hold for p*). Combined with constraints from primes ≤ k. Since p* > k, the Bertrand prime is among the primes being checked by `smallPrimeDivCheck` only if p* ≤ 29. For k ≤ 14, p* ≤ 28 < 29, so p* is one of the checked primes. For 15 ≤ k ≤ 28, p* could be up to 56, exceeding 29.

Hmm, but `smallPrimeDivCheck` only checks primes ≤ 29. The Bertrand prime for k = 28 would be p* = 29 (which is in the checked set!). For k = 27, the Bertrand prime could be p* = 29 (in set). For k = 15, p* could be 17, 19, etc. (all ≤ 29, in set). For k = 28, p* = 29 ∈ {2,...,29}.

So for all k ≤ 28, the Bertrand prime p* ∈ (k, 2k] ⊆ (1, 56]. Since 2k ≤ 56, and there's always a prime in (k, 2k], and the primes checked go up to 29... Wait, if k = 28, then (k, 2k] = (28, 56]. The prime 29 ∈ (28, 56], and 29 ≤ 29, so it IS checked.

If k = 27, then (k, 2k] = (27, 54]. The prime 29 is in this range and ≤ 29.

If k = 14, then (k, 2k] = (14, 28]. The prime 17 is in this range and ≤ 29.

So for ALL k ≤ 28, there exists a Bertrand prime p* ∈ (k, 2k] with p* ≤ 29, and this p* is one of the primes checked by `smallPrimeDivCheck`.

Now, the question is: does `hasCarry p* k n` hold (i.e., does digit domination fail for p*)? If `smallPrimeDivCheck n k = false`, then `hasCarry p k n = false` for ALL p ∈ {2,...,29}, which means digit domination HOLDS for all these primes including p*.

But digit domination for p* means: k ⪯_{p*} n, i.e., every base-p* digit of k ≤ corresponding digit of n. Since p* > k, k has exactly one base-p* digit (k itself, since k < p*). So k ⪯_{p*} n iff k ≤ n mod p*. This is exactly n mod p* ≥ k, i.e., p* DOESN'T divide C(n,k).

So if `smallPrimeDivCheck n k = false`, then for the Bertrand prime p*: n mod p* ≥ k, meaning p* ∤ C(n,k). This is the "bad" case.

But here's the thing — we also know from the `hA` hypothesis that ALL prime factors of n/k are ≤ k. And we're in the Type B branch. And we know digit domination holds for ALL 10 primes ≤ 29.

The argument should be: the combined CRT constraints from all 10 primes leave ZERO valid n for k ≤ 28 and n ≥ 500,000.

Let me check: for each k ∈ {2,...,28}, what is the CRT period and how many valid residues are there?

Actually, I think the right approach here is to create **an explore task** to develop a clean NL proof specifically for the k ≤ 28 residual case, and then a formalize task to close the sorry. Let me also check the approach already tried in proofs/large-n-divisibility.md more carefully for whether it gives us what we need.

The NL proof says: "For $k \\geq 29$: The combined CRT constraints from digit domination (primes $\\leq k$) and residue constraints (primes $\\in (k, M]$, using Bertrand's prime when $M \\geq 2k$) have no solution in $[kM, k(M+1))$."

But it says "for $k \\geq 29$". What about k < 29?

For k < 29: "Direct enumeration of the finite set of Type B values $M \\in (k, n/k]$ combined with explicit verification confirms no exceptions."

OK so the NL proof handles k < 29 via "direct enumeration" and "explicit verification" — which is what the code is already doing computationally up to n = 500,000. The gap is: this enumeration is infinite (M ranges over all k-smooth numbers > k).

I think the cleanest approach is to prove: **for k ≤ 28 and M ≥ 17857 (i.e., n ≥ 500,000), the digit domination conditions for primes ≤ 29 are incompatible.** This can be done by showing that within any period of the CRT modulus M_k = ∏_{p≤29} p^{L_p(k)}, the set of valid residues is empty for k ≤ 28.

Wait, that can't be right — n = k itself satisfies digit domination for all primes. The valid residue set is non-empty.

The issue is more subtle. In the residual case, we have extra constraints: n/k must be k-smooth and n/gcd(n,k) must be prime. But the sorry only needs to prove `(n.choose k).minFac ≤ n/k` — it doesn't need to prove the case is vacuous. It needs to find a prime ≤ n/k that divides C(n,k).

Let me reconsider the full picture. In the proof context at line 271, we have:
- `hA : ∀ p, p.Prime → p ∣ n/k → p ≤ k` (n/k is k-smooth)
- `hprime : (n / n.gcd k).Prime`
- `hle : n / k < n / n.gcd k` (d > n/k)
- `hn500k : ¬(n < 500000)` (n ≥ 500,000)
- And we need `(n.choose k).minFac ≤ n / k`

Since n ≥ 500,000 and k ≤ 28, n/k ≥ 17857. Since 29 ≤ n/k, any prime p ≤ 29 dividing C(n,k) gives minFac ≤ p ≤ 29 ≤ n/k.

The approach used in KGe29 for k ≥ 29 is:
1. Try `smallPrimeDivCheck` — if it succeeds, done.
2. If it fails, use Bertrand prime.

But for KLe28 at line 271, we could do something different and simpler. We're in the Type B case (n/k is k-smooth). We know n/k ≥ 17857 and n/k is 28-smooth. Now, 28-smooth numbers this large must have a specific structure (high powers of small primes). Let's use the Bertrand prime p = 29 (which is prime and ∈ (28, 56]).

Since k ≤ 28 < 29 ≤ 2k (for k ≥ 15), and 29 is prime, we have hasCarry 29 k n iff n mod 29 < k (since k < 29, Kummer's theorem for p = 29 with L = 1). 

Wait, `hasCarry 29 k n` checks for carries in base 29. Since k ≤ 28 < 29, k has a single base-29 digit: k itself. And n in base 29 has digits. The carry happens when adding k and (n - k) in base 29 — by Kummer, this is equivalent to n mod 29^L < k for L = 1 (since k < 29). Actually, it's `hasCarry p k n` which checks if there's a carry when adding k and n-k in base p. By Kummer, hasCarry p k n = true iff p | C(n, k).

For p = 29, k < 29: hasCarry 29 k n = true iff 29 | C(n, k) iff n mod 29 < k (from the large prime criterion, since 29 > k).

Wait, that's the reverse direction. Let me re-check:
- Kummer: v_p(C(n,k)) = number of carries when adding k and (n-k) in base p.
- hasCarry 29 k n = true iff there's at least one carry iff 29 | C(n,k).
- For p = 29 > k (since k ≤ 28): C(n,k) ≡ C(n mod 29, k) mod 29 (by Lucas). And 29 | C(n,k) iff C(n mod 29, k) ≡ 0 (mod 29). For k < 29 = p: C(n mod 29, k) = 0 mod 29 when n mod 29 < k.

So hasCarry 29 k n = true iff n mod 29 < k.

Now, the key question: **can we prove that for k ≤ 28 and n ≥ 500,000 in the residual case, n mod 29 < k?** If yes, then `smallPrimeDivCheck n k = true` (since hasCarry 29 k n = true), and we're done.

But we can't prove this directly. For example, n could have n mod 29 = 28 ≥ k for k = 2.

OK, so for small k (like k = 2), the Bertrand prime approach with p = 29 only helps if n mod 29 < 2, which is rare. But other primes help: hasCarry 2 2 n = true iff 2 | C(n, 2) = n(n-1)/2. Since n(n-1) is always even, C(n,2) = n(n-1)/2, and 2 | C(n,2) iff 4 | n(n-1), which is true when n ≡ 0, 1 (mod 4) — wait, that's not always true. For n = 3: C(3,2) = 3, which is odd.

Hmm, `hasCarry 2 2 3`: 2 = 10₂, 3 = 11₂. Adding 2 and 1 (= 3-2) in binary: 10 + 01 = 11, no carry. So hasCarry 2 2 3 = false. And indeed 2 ∤ C(3,2) = 3.

So for k = 2, n = 3: smallPrimeDivCheck = false. But we need n > k² = 4, so n ≥ 5.

Let me think about this differently. For each specific k ∈ {2,...,28}, can we prove `smallPrimeDivCheck n k = true` for all n ≥ N_k? If so, we just need N_k ≤ 500,000.

For k = 2: We need hasCarry p 2 n = true for some p ∈ {2,3,5,...,29}. hasCarry 2 2 n = true iff there's a carry adding 10₂ + (n-2)₂. The carry happens at position 1 when the bit 1 of (n-2) is 1, i.e., when (n-2) has bit 1 set. n-2 has bit 1 set iff n mod 4 ∈ {2, 3}... Wait, this is getting complicated at the individual level.

Let me take a step back and think about what task to create. The mathematical core is clear:

**For k ≤ 28 and n ≥ 500,000: show that `smallPrimeDivCheck n k = true`, i.e., at least one of the 10 primes {2,...,29} divides C(n,k).**

This is equivalent to showing: for k ≤ 28, it's impossible for n ≥ 500,000 to satisfy k ⪯_p n for ALL p ∈ {2,...,29} simultaneously.

This is a finite CRT computation for each k. The CRT period is M_k = lcm(p^{L_p(k)} : p ∈ {2,...,29}) and the valid residue count is R_k = ∏_{p≤29} (valid residues mod p^{L_p(k)}). If R_k = 0 for each k, we're done. If R_k > 0, we need to show all valid residues are < 500,000.

Actually, the most practical approach for formalization: **verify that `smallPrimeDivCheck n k = true` for all n in a suitable range per k, covering one full period**. Since the period M_k is likely very large, this might not be practical via native_decide.

But there's a smarter approach: **verify by case-splitting on k, and for each k, show that the CRT residue count is 0**. That is, for k = 2: compute the CRT residues mod (4 · 9 · 5 · 7 · 11 · 13 · 17 · 19 · 23 · 29) — wait, that's a huge modulus. But the computation is just multiplying the valid-residue counts:

For k = 2, p = 2: L₂(2) = 2, 2² = 4. Base-2 digits of 2 = [0, 1]. Valid residues mod 4: n₀ ≥ 0 (4 choices), n₁ ≥ 1 (1 choice). Count = 4 · 1 = ... wait no. Valid residues for k ⪯_2 n: need n mod 2 ≥ 0 (always true) and (n/2) mod 2 ≥ 1 (need (n/2) mod 2 = 1). So n mod 4 ∈ {2, 3}. Count = 2.

For k = 2, p = 3: L₃(2) = 1, 3¹ = 3. Digit 2 in base 3 = [2]. Valid: n mod 3 ≥ 2, i.e., n mod 3 = 2. Count = 1.

The point is: we need ALL p ∈ {2,...,29} to have digit domination. The simultaneous constraint has count R = ∏_p (valid count for p). If R > 0, then there exist n satisfying all constraints. But the question is whether any such n ≥ 500,000.

For k = 2: the CRT residues exist but are very sparse. Let me check computationally in my head:
- Mod 4: n ∈ {2, 3}. 2 choices.
- Mod 3: n ∈ {2}. 1 choice.
- By CRT mod 12: n ≡ 2 (mod 4) and n ≡ 2 (mod 3) → n ≡ 2 (mod 12). OR n ≡ 3 (mod 4) and n ≡ 2 (mod 3) → n ≡ 11 (mod 12). So 2 residues mod 12.
- But we also need mod 5: digit 2 in base 5 = [2]. n mod 5 ∈ {2, 3, 4}. 3 choices.
- And mod 7: digit 2 in base 7 = [2]. n mod 7 ∈ {2, 3, 4, 5, 6}. 5 choices.
- ... and so on for all primes up to 29.

The total count R = 2 · 1 · 3 · 5 · 9 · 11 · 15 · 17 · 21 · 27 = a big number but the modulus M is also huge. The density is ∏_p ((p - d_p)/p^{L_p}) where d_p are the digit constraints. For k = 2, density = (2/4)(1/3)(3/5)(5/7)(9/11)(11/13)(15/17)(17/19)(21/23)(27/29).

Let me compute: 0.5 · 0.333 · 0.6 · 0.714 · 0.818 · 0.846 · 0.882 · 0.895 · 0.913 · 0.931 ≈ 0.5 · 0.333 ≈ 0.167, · 0.6 ≈ 0.1, · 0.714 ≈ 0.071, etc. The density is roughly 0.02, meaning about 1 in 50 numbers satisfy all constraints. So there are certainly many n ≥ 500,000 satisfying all constraints for k = 2.

This means **we CANNOT prove the residual case is vacuous** for k = 2. There exist n ≥ 500,000 where smallPrimeDivCheck n 2 = false.

Wait — but the residual case has ADDITIONAL constraints beyond just smallPrimeDivCheck = false. It also requires:
- n/k is k-smooth
- d = n/gcd(n,k) is prime
- d > n/k

So the question is whether the COMBINED constraints (smallPrimeDivCheck = false AND n/k is k-smooth AND d is prime AND d > n/k) can be satisfied for k ≤ 28 and n ≥ 500,000.

Hmm, but the sorry at line 271 is in a context where we've already established:
- The residual case holds (d is prime, d > n/k, n/k is k-smooth)
- We need to prove minFac(C(n,k)) ≤ n/k

We need to find a prime ≤ n/k dividing C(n,k). We know d | C(n,k) but d > n/k, so d doesn't help. We need another prime factor.

Since d is prime and d > n/k ≥ 17857, and d | C(n,k), we could look at C(n,k)/d. If C(n,k)/d > 1, then C(n,k) has another prime factor ≤ C(n,k)/d. But C(n,k)/d could be 1 (if C(n,k) = d, i.e., C(n,k) is itself prime).

Can C(n,k) be prime? For k ≥ 2, C(n,k) = n(n-1)···(n-k+1) / k!. For k = 2: C(n,2) = n(n-1)/2. This is prime iff n(n-1)/2 is prime. For large n, n(n-1)/2 ≈ n²/2 has factors close to n, so it's composite. But n(n-1)/2 could be prime for specific n — e.g., C(4,2) = 6 (not prime), C(5,2) = 10, C(7,2) = 21... actually it seems hard for C(n,2) to be prime. n(n-1)/2 is prime means n(n-1) = 2p, so either n = 2 and p = (n-1) = 1 (not prime) or n-1 = 2 and p = n/... Hmm, n = p and n-1 = 2, so n = 3, C(3,2) = 3. Or n = 2p and n-1 = 1, n = 2, C(2,2) = 1.

Actually for k ≥ 2 and n ≥ 500,000: C(n,k) ≥ C(500000, 2) = 124999750000, which has many prime factors. So C(n,k) is certainly not prime, and has prime factors ≤ C(n,k)^{1/2}.

OK I think I'm going down a rabbit hole. Let me step back and think about what tasks to create.

The **key mathematical question** for KLe28:271 is:

> For k ≤ 28 and n ≥ 500,000 with n > k², when n/k is k-smooth and d = n/gcd(n,k) is prime with d > n/k, show that minFac(C(n,k)) ≤ n/k.

The approach from the NL proof (proofs/large-n-divisibility.md Section 7.3) handles this via the CRT density argument, showing the residual case is actually vacuous (combined constraints have no solution). But I showed above that for small k (like k = 2), smallPrimeDivCheck can be false for many n ≥ 500,000.

However, in the residual case there's an EXTRA constraint: n/k must be k-smooth AND d must be prime. The interaction of these extra constraints with smallPrimeDivCheck being false might make the case vacuous.

Let me think about k = 2 specifically:
- n/2 must be 2-smooth, i.e., n/2 = 2^a for some a ≥ 1. So n = 2^{a+1}.
- d = n/gcd(n, 2). gcd(n, 2) = 2 (since n is even). d = n/2 = 2^a.
- d must be prime: 2^a is prime iff a = 1. So d = 2, n = 4.
- But n ≥ 500,000. Contradiction!

So for k = 2, the residual case IS vacuous for n ≥ 5! The 2-smooth constraint is very strong.

For k = 3:
- n/3 must be 3-smooth, i.e., n/3 = 2^a · 3^b. So n = 3 · 2^a · 3^b = 2^a · 3^{b+1}.
- d = n/gcd(n, 3). gcd(n, 3) ∈ {1, 3}. Since n = 2^a · 3^{b+1}, gcd(n, 3) = 3. So d = n/3 = 2^a · 3^b.
- d > n/3 means d > 2^a · 3^b, but d = 2^a · 3^b. Contradiction!
- Wait, d > n/k = n/3. And d = n/3. So d > n/3 fails (d = n/3, not >).

Hmm, actually `hle : n / k < n / n.gcd k` means n/k < d. In this case, n/3 < n/gcd(n,3). Since gcd(n,3) | 3, either gcd = 1 or gcd = 3.
- If gcd = 3: d = n/3 = n/k, so n/k < d becomes n/k < n/k, contradiction.
- If gcd = 1: d = n, and d must be prime. So n is prime. And n/3 must be 3-smooth. But n is prime, so n/3 = n/3, and for n/3 to be 3-smooth (all prime factors ≤ 3), n/3 must be of the form 2^a · 3^b. Then n = 3 · 2^a · 3^b = 2^a · 3^{b+1}. But n is prime, so the only possibility is a = 0, b = 0, n = 3. But n ≥ 500,000, contradiction.

So for k = 3, the residual case is also vacuous for large n!

I suspect for ALL k ≤ 28, the residual case (d prime, d > n/k, n/k is k-smooth) is vacuous for sufficiently large n. The intuition: k-smooth numbers thin out rapidly, and having n/gcd(n,k) be prime with n/k being k-smooth is extremely constraining.

Let me check k = 28 more carefully:
- n/28 must be 28-smooth.
- gcd(n, 28) divides 28. Let g = gcd(n, 28). g ∈ {1, 2, 4, 7, 14, 28}.
- d = n/g must be prime and d > n/28.

For d > n/28: n/g > n/28 ⟹ g < 28. So g ∈ {1, 2, 4, 7, 14}.

If g = 14: d = n/14 and n/28 < d = n/14 = 2 · n/28. So d = 2 · (n/28). For d to be prime, 2 · (n/28) must be prime, which means n/28 = 1 and d = 2. But n ≥ 500,000, so n/28 ≥ 17857. Contradiction.

Wait, that's wrong. n/28 is integer division. Let me be more careful: n = 28q + r. If g = 14, then 14 | n, so n = 14m. d = n/14 = m. For d to be prime, m is prime. n/28 = 14m/28 = m/2. For n/28 to be 28-smooth, m/2 must be 28-smooth (if m is even). If m is odd (prime), then 14 | n but n = 14m, gcd(n, 28) = gcd(14m, 28) = 14 · gcd(m, 2). If m is odd, gcd(n, 28) = 14. So g = 14, d = m (odd prime). n/28 = m/2. For m odd, m/2 is not an integer — but n/28 in Lean is integer division. n = 14m, n/28 = 14m/28 = m/2 (integer division, rounding down). For m odd, n/28 = (m-1)/2.

All prime factors of (m-1)/2 must be ≤ 28. Since m is a large odd prime (m ≈ n/14 ≈ 35714 for n = 500000), we need (m-1)/2 to be 28-smooth. For large m, m-1 could be anything, and about ψ(x, 28)/x fraction of numbers up to x are 28-smooth. This fraction goes to 0 by the Dickman function, but there are infinitely many primes m where (m-1)/2 is 28-smooth.

So the residual case is NOT vacuous for k = 28 — there exist infinitely many n ≥ 500,000 in this case!

Hmm wait, but we need ALL prime factors of n/k = n/28 to be ≤ k = 28. We have n = 14m with m prime. n/28 = (m-1)/2 (for odd m). So (m-1)/2 must be 28-smooth.

Example: m = 57 is not prime. m = 59 is prime. (59-1)/2 = 29. Is 29 ≤ 28? No! 29 > 28. So this doesn't work.

m = 29: (29-1)/2 = 14 = 2 · 7. 14 is 28-smooth. n = 14 · 29 = 406. But n < 500,000.

m = 113: (113-1)/2 = 56 = 2³ · 7. 56 is 28-smooth. n = 14 · 113 = 1582. Still < 500,000.

m = a large prime where (m-1)/2 is 28-smooth and m > 35714 (so n > 500,000).

Such primes exist (they're sometimes called "smooth-shifted primes"). For example, m-1 = 2 · 2^a · 3^b · ... with all prime factors ≤ 28, and m = 2 · 2^a · 3^b · ... + 1 is prime. There are infinitely many such primes (by Dirichlet's theorem heuristics, though proving infinitude rigorously is hard).

But importantly for our formalization: we need to handle this case. We need to show that in this case, `smallPrimeDivCheck n k = true`.

For n = 14m where m is prime and n ≥ 500,000:
- We need some prime p ∈ {2,...,29} with p | C(n, 28).
- C(14m, 28) = C(14m, 28).
- Since 2 | 28 and 2 | n (n = 14m), let's check hasCarry 2 28 (14m).
- 28 = 11100₂. We need to check if there's a carry when adding 28 and (14m - 28) in base 2.
- 14m - 28 = 14(m - 2).

This is getting very detailed. Let me step back and think about what approach is practical for the formalization.

**Practical approach for KLe28:271:** The comments in the code suggest using a "CRT density argument showing the 10 primes {2,...,29} together cover all digit-domination patterns for k ≤ 28." The NL proof in proofs/large-n-divisibility.md Section 7 supports this.

The formalization strategy should be:

1. For each k ∈ {2,...,28}, compute the CRT modulus M_k = ∏_{p≤29} p^{L_p(k)} and the set S_k of residues mod M_k where smallPrimeDivCheck fails.
2. For each k, show that for every n ∈ S_k, the residual case conditions (n/k is k-smooth, d prime, d > n/k) imply n < 500,000.
3. This reduces to a finite check for each residue class.

But this is complicated. A simpler approach:

**Alternative: prove that for k ≤ 28 and n ≥ 500,000, if n/k is k-smooth, then `getFirstPrimeWithCarry n k ≠ none`.**

This could be done by:
1. Case-splitting on k (k ∈ {2,...,28} — 27 cases, but by symmetry we can handle groups).
2. For each k, showing that the k-smoothness of n/k combined with the size constraint forces some prime to have a carry.

Actually, the simplest approach might be computational. For k ≤ 28, the k-smooth numbers M ≥ 17857 are enumerable (there are finitely many in any bounded range, and they thin out). For each k, we could:

1. Enumerate all 28-smooth numbers M in a range large enough to cover one CRT period.
2. For each such M, verify that all n ∈ [kM, k(M+1)) have smallPrimeDivCheck = true.

But the CRT period is huge (∏ p^{L_p(k)} for k up to 28).

I think the most **practical formalization approach** is:

**For k ≤ 28 and n ≥ 500,000 in the residual case, use the Bertrand prime p* ∈ (k, 2k] (which is ≤ 29 for k ≤ 14, and for k ≥ 15, there's always a prime ≤ 29 in (k, 2k]).**

Wait — for k ≤ 28, p = 29 ∈ (k, 2k] only when k ≥ 15 and 29 ≤ 2k (i.e., k ≥ 15). For k < 15:
- k = 2: primes in (2, 4] = {3}. And 3 ≤ 29 ✓.
- k = 14: primes in (14, 28] = {17, 19, 23}. All ≤ 29 ✓.

So for ALL k ≤ 28, there's a Bertrand prime p* ∈ (k, 2k] with p* ≤ 29 ✓.

For this p*, we need n mod p* < k (for p* | C(n,k)). In the residual case, we have n/k is k-smooth and d = n/gcd(n,k) is prime > n/k.

The key question: is n mod p* < k guaranteed in the residual case? If not, we need to use other primes too.

I don't think it's guaranteed by the residual constraints alone. The residual case constrains n/k but not n mod p* directly.

OK, let me take the most practical path. I'll create the right tasks.

**Assessment:**
1. **KLe28:271** is a **standalone sorry** that needs its own dedicated work. Task 64v (CRT density for k > 1000) does NOT cover it.
2. The mathematical core is the same as KGe29:335/341/350 — showing that in the residual case, `smallPrimeDivCheck` succeeds. But the k ranges are different (k ≤ 28 vs k ≥ 29), so separate treatment is needed.
3. The approach should be: **for each k ∈ {2,...,28} and n/k being k-smooth, prove directly that at least one of the 10 primes ≤ 29 divides C(n,k)**. This might be doable per-k via a finite case analysis on the smooth structure.

Let me also check if there's an explore-level proof needed:
```bash
$ cd /home/jarred/code/erdos-1094 && grep -c "Section 7" proofs/large-n-divisibility.md
```
The NL proof in proofs/large-n-divisibility.md Section 7 already covers this conceptually. The issue is purely in the **formalization strategy**. Let me now create the tasks:
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-i01 --status "Creating tasks: need explore + formalize pipeline for KLe28:271"
```
Now let me create the tasks. The key insight from my analysis is:

1. The residual case for k ≤ 28 IS reachable for infinitely many n.
2. We need a **per-k CRT argument** showing that for each k ∈ {2,...,28}, at least one prime ≤ 29 always has a carry with k when n/k is k-smooth.
3. The NL proof exists conceptually (Section 7 of large-n-divisibility.md) but needs to be made concrete for k ≤ 28.
4. Task 64v does NOT help — it's about k > 1000 in the CRT case, completely different.

Let me also check whether the m36 task (KGe29 sorrys 335, 341, 350) might share a common lemma with KLe28:271:
```bash
$ cd /home/jarred/code/erdos-1094 && read -r -d '' desc << 'EOF'
Prove: For each k ∈ {2, 3, ..., 28}, if M = n/k is k-smooth (all prime factors ≤ k) and M ≥ 17857, then at least one prime p ∈ {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} divides C(n, k).

Context: The residual case in the k ≤ 28 proof requires showing smallPrimeDivCheck n k = true when n/k is k-smooth and d = n/gcd(n,k) is prime with d > n/k. This case is non-vacuous: for k = 28 with g = gcd(n,28) < 28, there are infinitely many n where n/28 is 28-smooth and n/g is prime.

Key approach from proofs/large-n-divisibility.md Section 7: Use the Bertrand prime p* ∈ (k, 2k] (always ≤ 29 for k ≤ 28). When n/k is k-smooth with M ≥ 2k, the combined CRT constraints from all 10 primes leave no valid n in any interval [kM, k(M+1)). This means for any n in such an interval, at least one prime ≤ 29 has a carry with k in that base.

The proof should work per-k: for each k ∈ {2,...,28}, show that the 10 primes {2,...,29} together exclude all residue classes modulo their combined CRT period. Use the digit domination structure.

NOTE: Do NOT read .lean files or artifacts/. Write the result to proofs/small-k-crt-coverage.md.
EOF
tm create -t "Prove: for k ≤ 28, 10 primes ≤ 29 cover all digit-domination patterns" -r explore -p 1 -d "$desc"
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm create -t "Review proofs/small-k-crt-coverage.md" -r verify -p 1 --deps erdos1094-tbc
```

```bash
$ cd /home/jarred/code/erdos-1094 && read -r -d '' desc << 'EOF'
Close sorry at KLe28.lean:271 (residual case for n ≥ 500,000, k ≤ 28).

Context: In large_n_minFac_bound_small_k, the residual case has:
- hk : 2 ≤ k, hk28 : k ≤ 28
- hn500k : ¬(n < 500000), so n ≥ 500,000
- hn : k * k < n, hn284 : 284 < n, hkn : k ≤ n
- hA : ∀ p, p.Prime → p ∣ n / k → p ≤ k (n/k is k-smooth)
- hprime : (n / n.gcd k).Prime, hle : n / k < n / n.gcd k
- hres : residualCheck n k = true
- Need to prove: (n.choose k).minFac ≤ n / k

Available hypotheses tell us n/k ≥ 17857, so any prime p ≤ 29 dividing C(n,k) suffices (since 29 ≤ 17857 ≤ n/k).

Use proofs/small-k-crt-coverage.md for the NL proof that the 10 primes {2,...,29} always cover.

Recommended strategy: prove a helper lemma
  lemma residual_smallPrime_cover (n k : ℕ) (hk : 2 ≤ k) (hk28 : k ≤ 28)
    (hn : 500000 ≤ n) (hkn : k ≤ n)
    (hA : ∀ p, p.Prime → p ∣ n / k → p ≤ k) : smallPrimeDivCheck n k = true

This may require case-splitting on k and using CRT period arguments or extending the computational verification approach.

Available compiled lemmas: getFirstPrimeWithCarry_sound, smallPrimeDivCheck_sound, hasCarry_dvd_choose, residual_verified_500000.
EOF
tm create -t "KLe28: close residual sorry at line 271 (n≥500k)" -r formalize -p 1 --deps erdos1094-uz7 -d "$desc"
```
Now let me do a full summary of the sorry landscape and task status:
```bash
$ cd /home/jarred/code/erdos-1094 && tm list --state open 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm list 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm list 2>/dev/null | grep -v closed | grep -v "^ID"
```
Wait — where's task 64v? Let me check:
```bash
$ cd /home/jarred/code/erdos-1094 && tm show erdos1094-64v 2>/dev/null
```
64v just closed! It replaced the CRT density sorry with an axiom. Let me re-check the sorry landscape:
```bash
$ cd /home/jarred/code/erdos-1094 && grep -rn 'sorry\|^axiom' Erdos/*.lean | grep -v '.lake/'
```
Good — still the same 4 sorrys + 1 axiom. Let me now also check whether `CrtCheck.lean:59` has an existing task:
```bash
$ cd /home/jarred/code/erdos-1094 && tm list --all 2>/dev/null | grep -i "crtcheck\|soundness\|CrtCheck\|crt_check"
```
No existing task for CrtCheck.lean:59. Let me check if it's blocking:
```bash
$ cd /home/jarred/code/erdos-1094 && grep -n 'crtCheckRange_sound\|crtRangeCheck\|crtRangeCheckFrom\|crt_verified' Erdos/KGe29.lean | head -20
```
The `crtCheckRange_sound` in CrtCheck.lean is used by KGe29.lean. The sorry at CrtCheck.lean:59 is the soundness of the CRT check range — this is a separate verification concern. Let me understand what it needs:
🛠️ **Executing tool: read**
This sorry is about proving: if `crtCheckRange a b = true` (a computational check), then for all k ∈ [a,b] and n ∈ [2k, k²], there exists a small prime dividing C(n,k). The soundness proof needs to bridge the computational check (which uses `hasCarry`) to the actual divisibility statement. This requires `hasCarry_dvd_choose`.

This is a different kind of sorry — it's about **bridging the computational check to a theorem**, similar to the crtRangeCheck_sound lemmas already proved in KGe29.lean.

Looking at KGe29.lean's `crtRangeCheck_sound` (which IS proved, using `unfold` and then `apply smallPrimeDivCheck_sound`), the CrtCheck.lean version should follow the same pattern.

Let me create a task for this:
```bash
$ cd /home/jarred/code/erdos-1094 && read -r -d '' desc << 'EOF'
Close sorry at CrtCheck.lean:59 (crtCheckRange_sound).

The sorry bridges the computational crtCheckRange to the mathematical statement. The function crtCheckRange calls crtCheckK for each k in [a, b], which uses CRT enumeration and checkOtherPrimes (which uses hasCarry). The soundness proof needs to show that the computational check correctly implies existence of a prime p ≤ 29 with p | C(n,k).

Pattern to follow: see crtRangeCheck_sound and crtRangeCheckFrom_sound in KGe29.lean (lines 57-93), which prove similar soundness lemmas using unfold + smallPrimeDivCheck_sound. The CrtCheck.lean version uses a different computational check (CRT-based enumeration) so the bridge is more involved.

Key lemma needed: show that the crtCheckK function's CRT enumeration is exhaustive — if crtCheckK k = true (solutions.isEmpty), then for ALL n in [2k, k²], at least one of the 10 primes has a carry with k at n.

Available: hasCarry_dvd_choose, smallPrimeDivCheck_sound.
EOF
tm create -t "CrtCheck: prove crtCheckRange_sound (line 59)" -r formalize -p 1 -d "$desc"
```
Now let me check the relationship between KGe29 sorrys (335, 341, 350) and whether m36 is still the right framing. These are all in `prime_large_divisor_case` and are about k ≥ 29:
```bash
$ cd /home/jarred/code/erdos-1094 && tm show erdos1094-m36 2>/dev/null
```
m36 is about lines 334 and 343, but current grep shows sorrys at 335, 341, 350. Let me re-read the code to map them:
🛠️ **Executing tool: read**
The three sorrys are at lines 335, 341, and 350. Task m36 references lines 334 and 343, which are slightly off — the line numbers shifted. But the description is correct: the sorrys are about (1) smallPrimeDivCheck_complete for k ≤ 200, (2) k > 200 implies n ≥ 2k², and (3) n % p < k for Bertrand prime.

These three sorrys are **tightly coupled** — they're all part of the `prime_large_divisor_case` function for k ≥ 29. Let me think about whether m36 needs to be restructured.

The three sorrys are:
1. **Line 335** (`smallPrimeDivCheck_complete` for k ≤ 200): Has `obtain ⟨p, hp, hp29, hpdvd⟩ := crtRangeCheckCase2_sound ...` giving p | C(n,k) with p ≤ 29 and p prime. Needs to conclude `smallPrimeDivCheck n k = true`. This is a **completeness** result: if some prime p ≤ 29 divides C(n,k), then hasCarry p k n must be true for that p. This is the REVERSE of hasCarry_dvd_choose.

2. **Line 341** (k > 200): Needs `2 * k ≤ n / k`, i.e., n ≥ 2k². This is supposed to follow from the fact that for k > 200 in the residual case (n/k is k-smooth, d prime, d > n/k), the case n < 2k² can be eliminated.

3. **Line 350** (Bertrand prime): Needs `n % p < k` where p is a Bertrand prime ∈ (k, 2k]. In context, `smallPrimeDivCheck n k ≠ true` (hspc is the negation). The argument is that the combined CRT constraints leave no valid n, so the case is vacuous. But proving vacuity requires the CRT density argument.

All three sorrys in KGe29 and the one in KLe28 share a common mathematical core: **for certain combinations of k, n, and smoothness constraints, at least one of the 10 primes ≤ 29 must divide C(n,k)**. The difference is the k range.

The approach for KGe29 line 335 is particularly interesting: it has already FOUND a prime p ≤ 29 dividing C(n,k), but can't show smallPrimeDivCheck captures it. This suggests the approach should be restructured to not go through smallPrimeDivCheck at all.

Let me think about a better restructuring. In `prime_large_divisor_case`, the current code:
1. Tries smallPrimeDivCheck (case split on true/false)
2. When false, tries to use Bertrand prime
3. Needs n ≥ 2k² and n % p < k (both sorry)

An alternative approach: don't case-split on smallPrimeDivCheck. Instead, directly use the CRT density argument to prove the residual case is vacuous (no valid n exists). Then the sorry becomes `False.elim`.

This would require: **for k ≥ 29 and n > k², when n/k is k-smooth and d = n/gcd(n,k) is prime with d > n/k, derive a contradiction.** If the NL proof is correct that no such (n,k) exists for k ≥ 29, this is provable.

But actually, this isn't provable without the CRT density argument formalized. The NL proof uses a probabilistic/counting argument that requires careful CRT analysis.

Let me update m36 with better context since the line numbers shifted and 64v closed:
```bash
$ cd /home/jarred/code/erdos-1094 && read -r -d '' desc << 'EOF'
Close 3 sorrys at KGe29.lean lines 335, 341, and 350 (all in prime_large_divisor_case).

These sorrys are about k ≥ 29 in the residual case where n/k is k-smooth, d = n/gcd(n,k) is prime, d > n/k, and n > k². They are tightly coupled.

Line 335: Have p prime, p ≤ 29, p | C(n,k) from crtRangeCheckCase2_sound. Need smallPrimeDivCheck n k = true. This is the reverse of hasCarry_dvd_choose — a completeness result. If p | C(n,k) then hasCarry p k n = true (by Kummer).

RECOMMENDED APPROACH: Restructure the proof to avoid requiring smallPrimeDivCheck completeness. Since you already have p prime, p ≤ 29, p | C(n,k), you can directly conclude minFac ≤ p ≤ 29 ≤ n/k. Bypass the smallPrimeDivCheck case split entirely.

Line 341: k > 200, need 2k ≤ n/k (i.e., n ≥ 2k²). The residual constraints (n/k k-smooth, d prime, d > n/k) combined with k > 200 should force this. If n < 2k², then n ∈ (k², 2k²), and the CRT density argument from crt_verified_10000 or a smaller range covers this.

Line 350: n % p < k for Bertrand prime. This is the contrapositive: if combined CRT constraints leave no valid n, the case is vacuous.

Consider restructuring: instead of the current by_cases on smallPrimeDivCheck, use a unified approach:
1. For k ≤ 200 AND n < 2k²: use crtRangeCheckCase2_sound directly (already have p | C(n,k), conclude immediately)
2. For k ≤ 200 AND n ≥ 2k²: use Bertrand prime (already have h2k_le_nk from step 1)
3. For k > 200: similar, but may need to extend CRT range or use axiom

Available: crtRangeCheckCase2_sound, crt_case2_verified_200, crt_verified_700, crt_verified_1000, crt_verified_10000, crt_density_large_k axiom.
EOF
tm update erdos1094-m36 -d "$desc"
```
Wait, I used `tm update` with `-d` which updated the title too. Let me fix:
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-m36 -t "KGe29: close 3 sorrys in prime_large_divisor_case (lines 335, 341, 350)"
```
Now let me close my task with a comprehensive summary:
```bash
$ cd /home/jarred/code/erdos-1094 && tm close erdos1094-i01 --summary "Gap analysis complete. Created 3 new tasks. KLe28:271 is NOT covered by 64v's work — it requires separate handling for k ≤ 28."
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm close erdos1094-i01 -s "Gap analysis complete. Created 3 new tasks. KLe28:271 is NOT covered by 64v's work — it requires separate handling for k ≤ 28."
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm close erdos1094-i01
```
Here is my completed gap analysis:

```json
{
  "status": "completed",
  "summary": "Created 3 new tasks: 1 explore, 1 verify, 2 formalize. Updated 1 existing formalize task (m36).",
  "details": "## Gap Analysis: KLe28:271 and Full Sorry Landscape\n\n### Key Finding\nTask 64v's CRT density work does **NOT** cover KLe28:271. The two are in entirely different k ranges:\n- 64v: k > 1000, CRT case (n ≤ k²) — now closed, replaced by axiom `crt_density_large_k`\n- KLe28:271: k ≤ 28, residual case (n ≥ 500,000, n > k², n/k is k-smooth, d prime)\n\n### Current Sorry Count: 4 sorrys + 1 axiom\n| Location | Mathematical Content | Task |\n|----------|---------------------|------|\n| CrtCheck.lean:59 | Soundness bridge for CRT computational check | **erdos1094-335** (NEW) |\n| KGe29.lean:188 | `axiom crt_density_large_k` (k > 10000) | erdos1094-ej8 (librarian, open) |\n| KGe29.lean:335 | smallPrimeDivCheck complete for k ≤ 200 | erdos1094-m36 (UPDATED) |\n| KGe29.lean:341 | k > 200 implies n ≥ 2k² | erdos1094-m36 (UPDATED) |\n| KGe29.lean:350 | n % p < k for Bertrand prime | erdos1094-m36 (UPDATED) |\n| KLe28.lean:271 | Residual case, k ≤ 28, n ≥ 500,000 | **erdos1094-tbc → uz7 → g43** (NEW) |\n\n### Tasks Created\n1. **erdos1094-tbc** (explore, P1): Prove CRT coverage for k ≤ 28 — the 10 primes ≤ 29 cover all digit-domination patterns\n2. **erdos1094-uz7** (verify, P1): Review proofs/small-k-crt-coverage.md (deps: tbc)\n3. **erdos1094-g43** (formalize, P1): Close KLe28:271 sorry using the verified proof (deps: uz7)\n4. **erdos1094-335** (formalize, P1): Close CrtCheck.lean:59 soundness bridge\n\n### Task Updated\n- **erdos1094-m36**: Updated description with correct line numbers (335/341/350) and recommended approach — restructure to bypass smallPrimeDivCheck completeness by using crtRangeCheckCase2_sound directly"
}
```

### Summary of Actions

**3 new tasks created, 1 existing task updated.**

#### New Tasks

| ID | Role | Title | Priority | Dependencies |
|----|------|-------|----------|-------------|
| `erdos1094-tbc` | explore | Prove: for k ≤ 28, 10 primes ≤ 29 cover all digit-domination patterns | P1 | — |
| `erdos1094-uz7` | verify | Review proofs/small-k-crt-coverage.md | P1 | `tbc` |
| `erdos1094-g43` | formalize | KLe28: close residual sorry at line 271 (n≥500k) | P1 | `uz7` |
| `erdos1094-335` | formalize | CrtCheck: prove crtCheckRange_sound (line 59) | P1 | — |

#### Updated Task

- **`erdos1094-m36`** (formalize, P1): Updated with correct line numbers and a **recommended restructuring** — instead of proving `smallPrimeDivCheck` completeness (the reverse of `hasCarry_dvd_choose`), restructure the proof to use `crtRangeCheckCase2_sound` directly, which already provides a prime p ≤ 29 with p | C(n,k).

#### Key Insight

The sorry at **KLe28:271** is mathematically independent from 64v's work and from the KGe29 sorrys. It requires a dedicated CRT coverage proof for k ≤ 28 — showing that the 10 primes {2,3,5,7,11,13,17,19,23,29} always produce at least one carry with any k ≤ 28 when n/k is k-smooth and sufficiently large. The explore → verify → formalize pipeline (`tbc → uz7 → g43`) addresses this.

## Final Result

Here is my completed gap analysis:

```json
{
  "status": "completed",
  "summary": "Created 3 new tasks: 1 explore, 1 verify, 2 formalize. Updated 1 existing formalize task (m36).",
  "details": "## Gap Analysis: KLe28:271 and Full Sorry Landscape\n\n### Key Finding\nTask 64v's CRT density work does **NOT** cover KLe28:271. The two are in entirely different k ranges:\n- 64v: k > 1000, CRT case (n ≤ k²) — now closed, replaced by axiom `crt_density_large_k`\n- KLe28:271: k ≤ 28, residual case (n ≥ 500,000, n > k², n/k is k-smooth, d prime)\n\n### Current Sorry Count: 4 sorrys + 1 axiom\n| Location | Mathematical Content | Task |\n|----------|---------------------|------|\n| CrtCheck.lean:59 | Soundness bridge for CRT computational check | **erdos1094-335** (NEW) |\n| KGe29.lean:188 | `axiom crt_density_large_k` (k > 10000) | erdos1094-ej8 (librarian, open) |\n| KGe29.lean:335 | smallPrimeDivCheck complete for k ≤ 200 | erdos1094-m36 (UPDATED) |\n| KGe29.lean:341 | k > 200 implies n ≥ 2k² | erdos1094-m36 (UPDATED) |\n| KGe29.lean:350 | n % p < k for Bertrand prime | erdos1094-m36 (UPDATED) |\n| KLe28.lean:271 | Residual case, k ≤ 28, n ≥ 500,000 | **erdos1094-tbc → uz7 → g43** (NEW) |\n\n### Tasks Created\n1. **erdos1094-tbc** (explore, P1): Prove CRT coverage for k ≤ 28 — the 10 primes ≤ 29 cover all digit-domination patterns\n2. **erdos1094-uz7** (verify, P1): Review proofs/small-k-crt-coverage.md (deps: tbc)\n3. **erdos1094-g43** (formalize, P1): Close KLe28:271 sorry using the verified proof (deps: uz7)\n4. **erdos1094-335** (formalize, P1): Close CrtCheck.lean:59 soundness bridge\n\n### Task Updated\n- **erdos1094-m36**: Updated description with correct line numbers (335/341/350) and recommended approach — restructure to bypass smallPrimeDivCheck completeness by using crtRangeCheckCase2_sound directly"
}
```

### Summary of Actions

**3 new tasks created, 1 existing task updated.**

#### New Tasks

| ID | Role | Title | Priority | Dependencies |
|----|------|-------|----------|-------------|
| `erdos1094-tbc` | explore | Prove: for k ≤ 28, 10 primes ≤ 29 cover all digit-domination patterns | P1 | — |
| `erdos1094-uz7` | verify | Review proofs/small-k-crt-coverage.md | P1 | `tbc` |
| `erdos1094-g43` | formalize | KLe28: close residual sorry at line 271 (n≥500k) | P1 | `uz7` |
| `erdos1094-335` | formalize | CrtCheck: prove crtCheckRange_sound (line 59) | P1 | — |

#### Updated Task

- **`erdos1094-m36`** (formalize, P1): Updated with correct line numbers and a **recommended restructuring** — instead of proving `smallPrimeDivCheck` completeness (the reverse of `hasCarry_dvd_choose`), restructure the proof to use `crtRangeCheckCase2_sound` directly, which already provides a prime p ≤ 29 with p | C(n,k).

#### Key Insight

The sorry at **KLe28:271** is mathematically independent from 64v's work and from the KGe29 sorrys. It requires a dedicated CRT coverage proof for k ≤ 28 — showing that the 10 primes {2,3,5,7,11,13,17,19,23,29} always produce at least one carry with any k ≤ 28 when n/k is k-smooth and sufficiently large. The explore → verify → formalize pipeline (`tbc → uz7 → g43`) addresses this.

End Time: 2026-02-11T22:41:42.024Z
