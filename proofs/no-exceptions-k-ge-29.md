# No Exceptions Exist for $k \geq 29$

**Status:** Draft ✏️
**Statement:** For all integers $k \geq 29$ and $n \geq 2k$:
$$\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\left\lfloor \frac{n}{k} \right\rfloor,\, k\right).$$
Equivalently, the exceptional set $E = \{(n, k) \mid 0 < k,\; 2k \leq n,\; \mathrm{minFac}(\binom{n}{k}) > \max(\lfloor n/k \rfloor, k)\}$ contains no pair $(n, k)$ with $k \geq 29$.
**Dependencies:** proofs/kummer-theorem.md, proofs/crt-density-k-ge-29.md, proofs/large-n-divisibility.md
**Confidence:** Certain (conditional on the two main dependencies)

---

## 1. Notation and Setup

Throughout, $k$ and $n$ denote positive integers with $k \geq 29$ and $n \geq 2k$.

- $\binom{n}{k} = \frac{n!}{k!(n-k)!}$ is the binomial coefficient.
- $\mathrm{minFac}(m)$ is the smallest prime factor of $m$ (well-defined for $m \geq 2$).
- $\lfloor \cdot \rfloor$ denotes the integer floor function.

**Observation:** Since $k \geq 29 \geq 2$ and $n \geq 2k \geq 4$, we have $\binom{n}{k} \geq \binom{n}{2} = \frac{n(n-1)}{2} \geq 6$, so $\mathrm{minFac}\!\left(\binom{n}{k}\right)$ is well-defined.

We write $T(n,k) = \max(\lfloor n/k \rfloor, k)$ for the threshold appearing in the conjecture.

**Goal:** Show there exists a prime $p \leq T(n,k)$ with $p \mid \binom{n}{k}$.

---

## 2. The Two Dependencies

We use two results, proved separately:

### Result 1: No digit-domination survivors in $[2k, k^2]$ (proofs/crt-density-k-ge-29.md)

*For every integer $k \geq 29$, there is no integer $n \in [2k, k^2]$ such that $k \preceq_p n$ (digit-domination) holds for all primes $p \leq 29$.*

**Contrapositive form:** For every $k \geq 29$ and every $n \in [2k, k^2]$, there exists a prime $p \leq 29$ such that digit-domination $k \preceq_p n$ fails.

### Result 2: Small minimum factor for $n > k^2$ (proofs/large-n-divisibility.md)

*For all $k \geq 2$ and $n > k^2$:*
$$\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \left\lfloor \frac{n}{k} \right\rfloor.$$

That is, there exists a prime $p \leq \lfloor n/k \rfloor$ dividing $\binom{n}{k}$.

### Bridge: Digit-domination and Kummer's theorem (proofs/kummer-theorem.md)

By Corollary 5 of proofs/kummer-theorem.md (the digit-domination criterion): for any prime $p$ and integers $n \geq k \geq 0$,
$$p \nmid \binom{n}{k} \iff k \preceq_p n \quad \text{(every base-$p$ digit of $k$ $\leq$ the corresponding digit of $n$)}.$$

Taking the contrapositive:
$$\text{digit-domination } k \preceq_p n \text{ fails} \implies p \mid \binom{n}{k}.$$

---

## 3. Proof

Let $k \geq 29$ and $n \geq 2k$ be given. We split into two exhaustive cases based on the size of $n$ relative to $k^2$.

### Case 1: $2k \leq n \leq k^2$

**Step 1a. Obtain a small prime dividing $\binom{n}{k}$.**

By Result 1 (contrapositive form), since $k \geq 29$ and $n \in [2k, k^2]$, there exists a prime $p_0 \leq 29$ such that the digit-domination condition $k \preceq_{p_0} n$ fails.

By the bridge (Kummer's theorem, Corollary 5, contrapositive), $p_0 \mid \binom{n}{k}$.

**Step 1b. Verify $p_0 \leq T(n,k)$.**

Since $2k \leq n \leq k^2$, we have $\lfloor n/k \rfloor \leq k$, so:
$$T(n,k) = \max\!\left(\left\lfloor \frac{n}{k} \right\rfloor, k\right) = k.$$

Since $p_0 \leq 29 \leq k$ (using $k \geq 29$), we obtain:
$$p_0 \leq k = T(n,k).$$

**Conclusion for Case 1:** $p_0$ is a prime with $p_0 \leq T(n,k)$ and $p_0 \mid \binom{n}{k}$, so $\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq p_0 \leq T(n,k)$.

### Case 2: $n > k^2$

**Step 2a. Obtain a prime dividing $\binom{n}{k}$ that is at most $\lfloor n/k \rfloor$.**

By Result 2 (applied with $k \geq 29 \geq 2$ and $n > k^2$):
$$\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \left\lfloor \frac{n}{k} \right\rfloor.$$

**Step 2b. Verify $\lfloor n/k \rfloor \leq T(n,k)$.**

By definition, $T(n,k) = \max(\lfloor n/k \rfloor, k) \geq \lfloor n/k \rfloor$.

**Conclusion for Case 2:** $\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \lfloor n/k \rfloor \leq T(n,k)$.

### Combining Cases

Since every pair $(k, n)$ with $k \geq 29$ and $n \geq 2k$ falls into Case 1 or Case 2 (the cases are exhaustive: either $n \leq k^2$ or $n > k^2$), we conclude:

$$\forall\, k \geq 29,\; \forall\, n \geq 2k: \quad \mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\left\lfloor \frac{n}{k} \right\rfloor,\, k\right). \qquad \blacksquare$$

---

## 4. Corollary: Exceptional Set Restriction

**Corollary.** *If $(n, k) \in E$ (i.e., $0 < k$, $2k \leq n$, and $\mathrm{minFac}(\binom{n}{k}) > \max(\lfloor n/k \rfloor, k)$), then $k \leq 28$.*

*Proof.* Suppose $(n, k) \in E$ with $k \geq 29$. By the theorem, $\mathrm{minFac}(\binom{n}{k}) \leq \max(\lfloor n/k \rfloor, k)$, contradicting $(n,k) \in E$. $\square$

This corollary is the key input to the main finiteness result (proofs/main-theorem.md): it reduces the problem to finitely many values of $k$ (namely $k \in \{1, 2, \ldots, 28\}$), after which a separate argument bounds $n$ for each such $k$.

---

## 5. Discussion

### 5.1 Why the case split at $k^2$

The threshold $n = k^2$ is the natural dividing line because:

- **For $n \leq k^2$:** The threshold $T(n,k) = k$, so we need a prime $p \leq k$ dividing $\binom{n}{k}$. The primes $> k$ are irrelevant. The digit-domination analysis via Kummer's theorem is the right tool, as it precisely characterizes when small primes divide the binomial coefficient.

- **For $n > k^2$:** The threshold $T(n,k) = \lfloor n/k \rfloor > k$, so primes larger than $k$ are also available. The Interval Divisibility Lemma from proofs/large-n-divisibility.md, combined with a structural case analysis on $k$-smooth numbers, provides the result.

### 5.2 Tightness of the bound $k \geq 29$

The number 29 is not arbitrary. The set of primes $\{2, 3, 5, 7, 11, 13, 17, 19, 23, 29\}$ provides ten independent CRT constraints. For $k < 29$, the digit-domination density from these primes can be large enough that survivors exist in $[2k, k^2]$. Indeed, the known exceptions include $(n, k)$ pairs with $k$ as large as 28 (e.g., $(284, 28)$).

### 5.3 Dependency status

This proof is a clean logical combination. Its correctness is **conditional** on Results 1 and 2:

| Dependency | Current Status | Role in This Proof |
|-----------|---------------|-------------------|
| proofs/kummer-theorem.md | Verified ✅ | Bridge: digit-domination failure ⟹ divisibility |
| proofs/crt-density-k-ge-29.md | Under review 🔍 | Result 1: eliminates $n \in [2k, k^2]$ |
| proofs/large-n-divisibility.md | Under review 🔍 | Result 2: eliminates $n > k^2$ |

The combining argument itself introduces no new mathematical content — it is a two-case split with straightforward inequality chaining. Any gaps in the overall argument reside entirely within the dependencies.

---

## References

- proofs/kummer-theorem.md — Kummer's theorem and the digit-domination criterion (Corollary 5). **Verified ✅.**
- proofs/crt-density-k-ge-29.md — CRT density analysis showing no digit-domination survivors in $[2k, k^2]$ for $k \geq 29$.
- proofs/large-n-divisibility.md — Structural proof that $\mathrm{minFac}(\binom{n}{k}) \leq \lfloor n/k \rfloor$ for $n > k^2$.
