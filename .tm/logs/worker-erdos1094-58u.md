# timtam Task: Prove Kummer/Lucas criterion for prime non-divisibility of binomials (erdos1094-58u)

Role: explore
Agent: explore (anthropic/claude-opus-4-6:high)
Start Time: 2026-02-08T07:49:30.893Z

## Agent Interaction





> **Thinking:**
> Let me start by understanding the task. I need to prove Kummer's theorem about the p-adic valuation of binomial coefficients. Let me first check the existing literature in the proofs directory and any dead-ends file.


```bash
$ ls proofs/ 2>/dev/null && cat proofs/dead-ends.md 2>/dev/null || echo "No proofs directory or dead-ends file"
```

```bash
$ cd /home/jarred/code/erdos-1094 && ls proofs/*.md 2>/dev/null || echo "No existing proof files"
```

```bash
$ cat proofs/exploration.md 2>/dev/null
```

```bash
$ cat proofs/main-theorem.md 2>/dev/null
```

```bash
$ tm update erdos1094-58u --status "Reviewing existing literature, developing proof of Kummer's theorem"
```


> **Thinking:**
> Good, I have a clear picture of the context. The project is proving Erdős conjecture 1094 about prime factors of binomial coefficients. They need Kummer's theorem as a foundational tool. Let me now write a complete, rigorous proof of Kummer's theorem.
> 
> The task asks me to:
> 1. Use the formula $v_p(m!) = \sum_{i \geq 1} \lfloor m/p^i \rfloor$ (Legendre's formula)
> 2. Show $v_p(\binom{n}{k}) = (s_p(k) + s_p(n-k) - s_p(n))/(p-1)$ where $s_p(m)$ is the digit sum in base $p$
> 
> 
> 3. Relate this to carry counting
> 
> Now I'm establishing the key identity that connects Legendre's formula to digit sums—specifically, that the sum of floor divisions equals the difference between the number itself and its base-$p$ digit sum, scaled by $p-1$.
> 
> To prove this, I'm expressing each floor term using the base-$p$ digits and then reorganizing the double sum by changing the order of summation. This gives me a geometric series for each digit, which simplifies to show that the total equals $\frac{m - s_p(m)}{p-1}$.
> 
> Now I'm applying Legendre's formula to find the $p$-adic valuation of a binomial coefficient by taking the difference of the valuations of the three factorials involved.
> 
> The key insight is connecting this to carries in base-$p$ addition: when we add $k$ and $n-k$ to get $n$, the carries at each position determine whether the digit sum condition is satisfied. $s_p(k) + s_p(n-k) + \sum_{i=1}^{L} c_i = s_p(n) + p \sum_{i=1}^{L} c_i$
> 
> Rearranging this, I get $s_p(k) + s_p(n-k) - s_p(n) = (p-1) \sum_{i=1}^{L} c_i$, where the sum of carries equals some total $C$. This gives me Kummer's theorem: the $p$-adic valuation of the binomial coefficient equals the number of carries when adding $k$ and $n-k$ in base $p$. Now I'm moving on to characterize this using digit domination and Lucas' criterion.
> 
> The key insight is that $p$ doesn't divide the binomial coefficient exactly when there are no carries at all, which happens when each digit of $k$ plus the corresponding digit of $n-k$ stays below $p$. But I need to be careful here—the digits of $n-k$ depend on how the subtraction itself is performed, so I should think about this condition more directly in terms of the base-$p$ representations. are no carries iff $k_i + r_i < p$ for all $i$ (where $r_i$ are the digits of $n - k$). But since $k_i + r_i + c_i = n_i + p \cdot c_{i+1}$ and all $c_i = 0$, we get $k_i + r_i = n_i$ for all $i$. Since $0 \leq k_i, r_i \leq p-1$, the condition $k_i + r_i = n_i$ with $n_i \leq p - 1$ gives $k_i \leq n_i$ (since $r_i = n_i - k_i \geq 0$).
> 
> Conversely, if $k_i \leq n_i$ for all $i$, then subtracting $k$ from $n$ in base $p$ requires no borrowing, so $r_i = n_i - k_i$ and $k_i + r_i = n_i < p$, confirming no carries occur. Now I can tie everything together: Legendre's formula connects to the digit sum identity, which gives the formula for $v_p(\binom{n}{k})$ in terms of carries, and the carry analysis shows this equals the number of carries when subtracting $k$ from $n$. This leads to the digit domination characterization. I should also state Lucas' theorem as a corollary before writing this up.

Now I have full context. Let me develop the proof of Kummer's theorem carefully.
```bash
$ tm update erdos1094-58u --status "Writing complete proof of Kummer's theorem"
```

🛠️ **Executing tool: write**
Now let me verify the proof is complete and correct by re-reading it:
🛠️ **Executing tool: read**
The proof is complete and rigorous. Let me verify a small detail — in the (iii) ⇒ (ii) direction of Corollary 5, I need to make sure the claim that the defined $b_j$ actually give the digits of $n-k$ is properly justified:

The key step is: if $a_j \leq n_j$ for all $j$, then $n - k = \sum(n_j - a_j)p^j$, and since each $n_j - a_j \in [0, p-1]$, this IS the base-$p$ representation. This is correct because:
- $\sum(n_j - a_j)p^j = \sum n_j p^j - \sum a_j p^j = n - k$ ✓
- Each coefficient is in $[0, p-1]$ ✓
- So by uniqueness of base-$p$ representation, these are the digits ✓

The proof is solid. Let me update the task status.
```bash
$ tm update erdos1094-58u --status "Proof complete, published to proofs/kummer-theorem.md"
```
```json
{
  "status": "completed",
  "summary": "Proved Kummer's theorem and the digit-domination criterion. Published to proofs/kummer-theorem.md",
  "details": "Confidence: Certain. The proof proceeds in 5 steps: (1) Legendre's formula v_p(m!) = Σ floor(m/p^i) via double counting; (2) Digit sum identity Σ floor(m/p^i) = (m - s_p(m))/(p-1) by expanding floors in terms of base-p digits and summing the geometric series; (3) Valuation formula v_p(C(n,k)) = (s_p(k) + s_p(n-k) - s_p(n))/(p-1) by subtracting the Legendre formulas; (4) Kummer's theorem v_p(C(n,k)) = number of carries, proved by summing the carry recurrence a_j + b_j + c_j = n_j + p·c_{j+1} over all positions to get s_p(a) + s_p(b) - s_p(n) = (p-1)C; (5) Digit-domination corollary: p ∤ C(n,k) iff k_j ≤ n_j for all j, proved by showing zero carries ⟺ digit-domination via uniqueness of base-p representation. All steps are fully rigorous with no gaps."
}
```

## Final Result

```json
{
  "status": "completed",
  "summary": "Proved Kummer's theorem and the digit-domination criterion. Published to proofs/kummer-theorem.md",
  "details": "Confidence: Certain. The proof proceeds in 5 steps: (1) Legendre's formula v_p(m!) = Σ floor(m/p^i) via double counting; (2) Digit sum identity Σ floor(m/p^i) = (m - s_p(m))/(p-1) by expanding floors in terms of base-p digits and summing the geometric series; (3) Valuation formula v_p(C(n,k)) = (s_p(k) + s_p(n-k) - s_p(n))/(p-1) by subtracting the Legendre formulas; (4) Kummer's theorem v_p(C(n,k)) = number of carries, proved by summing the carry recurrence a_j + b_j + c_j = n_j + p·c_{j+1} over all positions to get s_p(a) + s_p(b) - s_p(n) = (p-1)C; (5) Digit-domination corollary: p ∤ C(n,k) iff k_j ≤ n_j for all j, proved by showing zero carries ⟺ digit-domination via uniqueness of base-p representation. All steps are fully rigorous with no gaps."
}
```

End Time: 2026-02-08T07:51:50.228Z
