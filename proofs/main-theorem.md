# Finiteness of the Exceptional Set (Erdős 1094)

**Status:** Draft ✏️
**Statement:** The set $E = \{(n, k) \in \mathbb{N} \times \mathbb{N} \mid 0 < k \;\wedge\; 2k \leq n \;\wedge\; \mathrm{minFac}\!\left(\binom{n}{k}\right) > \max\!\left(\lfloor n/k \rfloor,\, k\right)\}$ is finite.
**Dependencies:** proofs/no-exceptions-k-ge-29.md, proofs/bound-n-for-small-k.md
**Confidence:** Certain (given the two dependencies)

## Setup

We prove that $E$ is finite by exhibiting a finite set $B$ with $E \subseteq B$.

**Notation.** For natural numbers $n, k$ with $0 < k$ and $2k \leq n$:
- $\binom{n}{k}$ denotes the binomial coefficient $n! / (k!(n-k)!)$.
- $\mathrm{minFac}(m)$ denotes the smallest prime factor of $m$ (for $m \geq 2$).
- $\lfloor n/k \rfloor$ denotes the integer floor division of $n$ by $k$.

**Note on $\binom{n}{k} \geq 2$.** Since $0 < k$ and $2k \leq n$, we have $k \geq 1$ and $n \geq 2$. If $k = 1$, then $\binom{n}{1} = n \geq 2$. If $k \geq 2$, then $n \geq 4$ and $\binom{n}{k} \geq \binom{n}{2} = n(n-1)/2 \geq 6$. In either case, $\binom{n}{k} \geq 2$, so $\mathrm{minFac}\!\left(\binom{n}{k}\right)$ is well-defined and is a prime.

## Dependencies

We use two results, proved separately:

**Result A** (proofs/no-exceptions-k-ge-29.md): *For all $n, k \in \mathbb{N}$ with $0 < k$, $2k \leq n$, and $k \geq 29$:*
$$\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\lfloor n/k \rfloor,\, k\right).$$

Equivalently: if $(n,k) \in E$, then $k < 29$, i.e., $k \leq 28$.

**Result B** (proofs/bound-n-for-small-k.md): *For all $n, k \in \mathbb{N}$ with $0 < k$, $2k \leq n$, $k \leq 28$, and $n > 284$:*
$$\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\lfloor n/k \rfloor,\, k\right).$$

Equivalently: if $(n,k) \in E$ and $k \leq 28$, then $n \leq 284$.

## Proof

**Step 1. Define the bounding set.**

Let
$$B = \{(n, k) \in \mathbb{N} \times \mathbb{N} \mid k \leq 28 \;\wedge\; n \leq 284\}.$$

**Step 2. Show $E \subseteq B$.**

Let $(n, k) \in E$. Then $0 < k$, $2k \leq n$, and $\mathrm{minFac}\!\left(\binom{n}{k}\right) > \max\!\left(\lfloor n/k \rfloor,\, k\right)$.

- **Claim: $k \leq 28$.**
  Suppose for contradiction that $k \geq 29$. Then by Result A (applied with our $n, k$ satisfying $0 < k$, $2k \leq n$, and $k \geq 29$), we have $\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\lfloor n/k \rfloor,\, k\right)$. This contradicts $(n,k) \in E$. Therefore $k \leq 28$.

- **Claim: $n \leq 284$.**
  We have established $k \leq 28$. Suppose for contradiction that $n > 284$. Then by Result B (applied with our $n, k$ satisfying $0 < k$, $2k \leq n$, $k \leq 28$, and $n > 284$), we have $\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\lfloor n/k \rfloor,\, k\right)$. This contradicts $(n,k) \in E$. Therefore $n \leq 284$.

Since $k \leq 28$ and $n \leq 284$, we have $(n, k) \in B$. As $(n,k) \in E$ was arbitrary, $E \subseteq B$.

**Step 3. $B$ is finite.**

The set $B = \{(n, k) \in \mathbb{N} \times \mathbb{N} \mid k \leq 28 \;\wedge\; n \leq 284\}$ is a subset of $\{0, 1, \ldots, 284\} \times \{0, 1, \ldots, 28\}$, which is a product of two finite sets and hence finite. Explicitly, $|B| = 285 \times 29 = 8265$.

**Step 4. $E$ is finite.**

Since $E \subseteq B$ (Step 2) and $B$ is finite (Step 3), the set $E$ is finite. $\square$

## Formalization Notes

The proof structure maps directly to the Lean theorem:

```
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite
```

The formalization strategy:
1. Apply `Set.Finite.subset` with the bounding set $B = \text{Finset.product} \; (\text{Finset.range}\; 285) \; (\text{Finset.range}\; 29)$ (viewed as a `Set` via `Finset.finite_toSet`).
2. The inclusion $E \subseteq B$ reduces to: for $(n,k)$ satisfying the predicate, $n < 285$ and $k < 29$. This follows from the contrapositives of Results A and B.
3. Results A and B are the substantive mathematical content; this combining step is purely set-theoretic.

## References

- proofs/no-exceptions-k-ge-29.md — Result A: no exceptions exist for $k \geq 29$
- proofs/bound-n-for-small-k.md — Result B: for $k \leq 28$, all exceptions have $n \leq 284$
- proofs/exploration.md — Computational verification identifying the 14 specific exceptions
