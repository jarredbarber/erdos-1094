# timtam Task: Prove large prime divisibility criterion for binomials (erdos1094-a0e)

Role: explore
Agent: explore (anthropic/claude-opus-4-6:high)
Start Time: 2026-02-08T07:53:36.064Z

## Agent Interaction





> **Thinking:**
> Let me start by understanding the task. I need to prove that for prime p > k and n ≥ k, we have p | C(n,k) if and only if n mod p < k. Let me first check existing literature and then develop the proof.


```bash
$ cd /home/jarred/code/erdos-1094 && ls proofs/ 2>/dev/null || echo "No proofs directory yet"
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat proofs/dead-ends.md 2>/dev/null || echo "No dead-ends file"
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**


> **Thinking:**
> Now I have a thorough understanding of the project context. The task asks me to prove the "large prime divisibility criterion for binomials": For prime $p > k$ and $n \geq k$, we have $p \mid \binom{n}{k}$ if and only if $n \bmod p < k$.
> 
> I notice that this result is already mentioned in several places:
> - In the exploration.md (Section 2.2, Regime 2)
> - In the kummer-theorem.md (the final remark about primes $p > k$)
> 
> But it hasn't been given a full standalone proof in its own file. 
> 
> I'll structure the proof using Legendre's formula: since $p > k$, the factorial $k!$ has no factors of $p$, so $v_p(\binom{n}{k})$ reduces to comparing the $p$-adic valuations of $n!$ and $(n-k)!$. The key insight is that $n!/(n-k)!$ is a product of exactly $k$ consecutive integers, and since $p > k$, at most one of these integers can be divisible by $p$. This means $p$ divides the binomial coefficient if and only if one of these $k$ consecutive integers is divisible by $p$, which happens precisely when $n \bmod p < k$.
> 
> Let me write this up rigorously and also mention the connection to the Kummer/digit-domination approach as an alternative perspective.


```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-a0e --status "Developing proof of large prime criterion"
```
Now let me develop and write the proof carefully.
🛠️ **Executing tool: write**

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-a0e --status "Proof written, verifying completeness and rigor"
```
Let me re

> **Thinking:**
> -read the proof to verify it's complete and rigorous. Let me check for any gaps or issues.

Let me re-read the proof to check for any gaps or issues.
🛠️ **Executing tool: read**


> **Thinking:**
> The proof looks solid. Let me clean it up a bit - there's some meandering in Steps 3-4 where I go back and forth on the higher powers issue. Let me tighten that section to make the argument cleaner and more direct. The key logical chain is clear and correct:
> 
> 1. v_p(C(n,k)) = v_p(n!) - v_p((n-k)!) (since v_p(k!) = 0)
> 2. Using Legendre's formula, this equals sum over i of (floor(n/p^i) - floor((n-k)/p^i))
> 3. 
> 
> Each term in that sum counts multiples of p^i in the range {n-k+1,...,n}, and since this range has size k and p^i ≥ p > k, there's at most one such multiple. The i=1 term being zero forces all higher powers to vanish, so p divides C(n,k) exactly when floor(n/p) > floor((n-k)/p). A case analysis on n mod p then yields the final result.

The proof is logically complete but has some unnecessary meandering in Steps 3–4 where I self-correct. Let me clean that up for clarity.
🛠️ **Executing tool: edit**
Now let me also clean up the Case B analysis which has some unnecessary back-and-forth:
🛠️ **Executing tool: edit**
Now let me verify the final version reads cleanly:
🛠️ **Executing tool: read**
The proof is clean and rigorous. Let me verify there are no logical gaps by tracing through the argument once more:

1. **Step 1**: Standard factorization of v_p(C(n,k)) — correct.
2. **Step 2**: v_p(k!) = 0 because p > k — every factor 1,...,k is less than p — correct.
3. **Step 3**: Legendre's formula applied to get the sum of floor differences — correct.
4. **Step 4**: Each floor difference counts multiples of p^i in an interval of length k < p ≤ p^i, so at most 1. The i=1 term controls all others since p^i | m ⟹ p | m — correct.
5. **Step 5**: Case split on r = n mod p. Case A (r ≥ k): floor doesn't change, so 0. Case B (r < k): floor decreases by 1, so difference is 1. Bounds on the remainder p+r-k are verified — correct.
6. **Step 6**: Combines to the stated equivalence — correct.

The alternative proof via digit domination is also complete and correct, providing a second independent verification.
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-a0e --status "Proof complete, publishing"
```
The proof is complete and published. Let me provide the final summary.

```json
{
  "status": "completed",
  "summary": "Proved: For prime p > k ≥ 1 and n ≥ k, p | C(n,k) iff n mod p < k. Published to proofs/large-prime-criterion.md",
  "details": "Confidence: Certain. Two independent proofs provided. The main proof uses Legendre's formula: since v_p(k!) = 0 when p > k, the valuation v_p(C(n,k)) equals the sum over i ≥ 1 of (⌊n/p^i⌋ - ⌊(n-k)/p^i⌋). Each term counts multiples of p^i in {n-k+1,...,n}, which is at most 1 since p^i > k. The i=1 term controls all others (multiples of p^2 are multiples of p), so p | C(n,k) iff ⌊n/p⌋ > ⌊(n-k)/p⌋. A case split on r = n mod p shows this holds iff r < k. A second proof via the digit-domination criterion (Kummer's theorem) gives the same result in three lines: since k < p, k is a single base-p digit, and digit domination reduces to n mod p ≥ k. Also proved two corollaries: (1) the geometric interpretation (p | C(n,k) iff a multiple of p lies in {n-k+1,...,n}), and (2) the sharpened valuation v_p(C(n,k)) ∈ {0,1} for p > k."
}
```

## Final Result

The proof is complete and published. Let me provide the final summary.

```json
{
  "status": "completed",
  "summary": "Proved: For prime p > k ≥ 1 and n ≥ k, p | C(n,k) iff n mod p < k. Published to proofs/large-prime-criterion.md",
  "details": "Confidence: Certain. Two independent proofs provided. The main proof uses Legendre's formula: since v_p(k!) = 0 when p > k, the valuation v_p(C(n,k)) equals the sum over i ≥ 1 of (⌊n/p^i⌋ - ⌊(n-k)/p^i⌋). Each term counts multiples of p^i in {n-k+1,...,n}, which is at most 1 since p^i > k. The i=1 term controls all others (multiples of p^2 are multiples of p), so p | C(n,k) iff ⌊n/p⌋ > ⌊(n-k)/p⌋. A case split on r = n mod p shows this holds iff r < k. A second proof via the digit-domination criterion (Kummer's theorem) gives the same result in three lines: since k < p, k is a single base-p digit, and digit domination reduces to n mod p ≥ k. Also proved two corollaries: (1) the geometric interpretation (p | C(n,k) iff a multiple of p lies in {n-k+1,...,n}), and (2) the sharpened valuation v_p(C(n,k)) ∈ {0,1} for p > k."
}
```

End Time: 2026-02-08T07:56:15.916Z
