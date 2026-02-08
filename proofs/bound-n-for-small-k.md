# Bound on $n$ for Small $k$: Exceptions with $k \leq 28$ Satisfy $n \leq 284$

**Status:** Under review 🔍  
**Statement:** For every integer $k$ with $1 \leq k \leq 28$ and every integer $n > 284$ with $n \geq 2k$:
$$\mathrm{minFac}\left(\binom{n}{k}\right) \leq \max\!\left(\left\lfloor \frac{n}{k} \right\rfloor, k\right).$$
Equivalently, there exists a prime $p \leq \max(\lfloor n/k \rfloor, k)$ such that $p \mid \binom{n}{k}$.

**Dependencies:** 
- proofs/large-n-divisibility.md (for the case $n > k^2$)
- proofs/kummer-theorem.md (digit-domination criterion)
- proofs/large-prime-criterion.md (divisibility criterion for primes $> k$)

**Confidence:** High

---

## 1. Overview

We prove that all exceptions $(n, k)$ to the Erdős conjecture with $k \leq 28$ satisfy $n \leq 284$. The proof splits into two main cases:

1. **Case A ($n > k^2$):** The threshold is $\lfloor n/k \rfloor > k$. We show that primes in the range $(k, n/k]$ force divisibility.

2. **Case B ($284 < n \leq k^2$):** This only applies for $k \geq 17$ (since $16^2 = 256 \leq 284$). We use explicit CRT analysis combined with the near-prime capacity argument to show no exceptions exist.

---

## 2. Preliminaries

### 2.1 Divisibility Criteria

From the established results:

**For primes $p \leq k$ (digit domination):** By Kummer's theorem, $p \nmid \binom{n}{k}$ iff every base-$p$ digit of $k$ is $\leq$ the corresponding digit of $n$. (proofs/kummer-theorem.md, Corollary 5)

**For primes $p > k$ (modular condition):** By the large prime criterion, $p \mid \binom{n}{k}$ iff $n \bmod p < k$. (proofs/large-prime-criterion.md)

### 2.2 The Smooth Parts Identity

For $(n, k)$ to be an exception, each integer $m \in \{n-k+1, \ldots, n\}$ must factor as $m = s_m \cdot t_m$ where:
- $s_m$ is the $M$-smooth part (all prime factors $\leq M$), with $M = \max(\lfloor n/k \rfloor, k)$
- $t_m$ is the $M$-rough part (all prime factors $> M$)

If $\binom{n}{k}$ has no prime factor $\leq M$, then $\binom{n}{k} = \prod_m t_m / (k!/\prod_m s_m)$. Since $\binom{n}{k}$ is an integer with all factors $> M$, we must have:
$$\prod_{m=n-k+1}^{n} s_m = k!. \tag{Smooth Identity}$$

---

## 3. Case A: Large $n$ ($n > k^2$)

**Theorem 1.** *For $k \geq 2$ and $n > k^2$:*
$$\mathrm{minFac}\left(\binom{n}{k}\right) \leq \left\lfloor \frac{n}{k} \right\rfloor.$$

*Proof reference.* This is the main result of proofs/large-n-divisibility.md. The proof uses:
1. The **Interval Divisibility Lemma**: If $M = \lfloor n/k \rfloor$ has a prime factor $p > k$, then $p \mid \binom{n}{k}$ for all $n \in [kM, k(M+1))$.
2. For $M$ values that are $k$-smooth (Type B), explicit CRT verification shows no valid $n$ exists.

**Application to $k \leq 28$:** For $k \in \{1, \ldots, 28\}$ and $n > k^2 \geq n > 784$:
- Since $n > k^2$, we have $\lfloor n/k \rfloor > k$, so the threshold is $\lfloor n/k \rfloor$.
- By Theorem 1, $\mathrm{minFac}(\binom{n}{k}) \leq n/k = \max(n/k, k)$. $\square$

---

## 4. Case B: Medium $n$ ($284 < n \leq k^2$)

This case applies only when $k^2 > 284$, i.e., $k \geq 17$. We analyze each $k \in \{17, 18, \ldots, 28\}$ individually.

### 4.1 Framework: CRT Density for $n \in (284, k^2]$

For $n \in (284, k^2]$, the threshold is $\max(\lfloor n/k \rfloor, k) = k$ (since $n/k \leq k$).

An exception requires $p \nmid \binom{n}{k}$ for all primes $p \leq k$, which by Kummer's theorem means:
$$k \preceq_p n \quad \text{for all primes } p \leq k.$$

The CRT modulus is $M_k = \prod_{p \leq k} p^{L_p(k)}$, where $L_p(k) = \lceil \log_p(k+1) \rceil$.

### 4.2 Key Observation: CRT Modulus Exceeds Interval Length

**Lemma 2.** *For $k \geq 5$, we have $M_k > k^2 - 284 > k^2 - 2k$.*

*Proof.* We compute the CRT modulus using just the first few primes:
- For $k \geq 17$: $M_k \geq 2^5 \times 3^3 \times 5^2 \times 7^2 = 32 \times 27 \times 25 \times 49 = 1{,}058{,}400 > k^2$ for any $k \leq 28$.

More precisely, for $k = 17$: $M_{17} \geq 2^5 \times 3^3 \times 5^2 \times 7^2 \times 11 \times 13 \times 17 > 10^8$.

Since $M_k > k^2$ and $k^2 \leq 784$ for $k \leq 28$, the interval $(284, k^2]$ has length $< k^2 - 284 < 500 \ll M_k$. $\square$

**Consequence:** Each valid CRT residue $r$ (satisfying $k \preceq_p r$ for all $p \leq k$) appears **at most once** in the interval $(284, k^2]$.

### 4.3 Explicit Analysis for Each $k \in \{17, \ldots, 28\}$

For each $k$, we enumerate the valid CRT residues and check whether any lie in $(284, k^2]$.

#### Case $k = 17$ (Interval: $(284, 289]$)

The interval has only 5 integers: $\{285, 286, 287, 288, 289\}$.

**Base-2 constraint:** $17 = 10001_2$, so we need $n \bmod 32 \in \{17, 19, 21, 23, 25, 27, 29, 31\}$.
- $285 \bmod 32 = 29$ ✓
- $286 \bmod 32 = 30$ ✗
- $287 \bmod 32 = 31$ ✓
- $288 \bmod 32 = 0$ ✗
- $289 \bmod 32 = 1$ ✗

Survivors: $\{285, 287\}$.

**Base-3 constraint:** $17 = 122_3$, so we need digit domination.
- $285 = 101120_3$: digits are $[0, 2, 1, 1, 0, 1]$. Compare to $17 = [2, 2, 1]$. Digit 0: $0 < 2$ ✗

$285$ fails base-3. 

- $287 = 101122_3$: digits are $[2, 2, 1, 1, 0, 1]$. Digit 0: $2 \geq 2$ ✓. Digit 1: $2 \geq 2$ ✓. Digit 2: $1 \geq 1$ ✓.

$287$ passes base-3. Check remaining primes:

**Base-5 constraint:** $17 = 32_5$, so we need $n_0 \geq 2$ and $n_1 \geq 3$.
- $287 = 2122_5$: digits are $[2, 2, 1, 2]$. Digit 0: $2 \geq 2$ ✓. Digit 1: $2 < 3$ ✗

$287$ fails base-5.

**Conclusion for $k = 17$:** No $n \in (284, 289]$ satisfies all digit-domination constraints. ✓

---

#### Case $k = 18$ (Interval: $(284, 324]$)

**Base-2 constraint:** $18 = 10010_2$, so we need $n \bmod 32 \in \{18, 19, 22, 23, 26, 27, 30, 31\}$.

**Base-3 constraint:** $18 = 200_3$, so we need $n_0 \geq 0$ (always true), $n_1 \geq 0$ (always true), $n_2 \geq 2$.

For $n \in (284, 324]$:
- $n = 288 = 101200_3$: $n_2 = 2 \geq 2$ ✓
- $n = 306 = 102100_3$: $n_2 = 1 < 2$ ✗
- $n = 324 = 110000_3$: $n_2 = 0 < 2$ ✗

The survivors from base-3 in range are those with $n \bmod 27 \in \{18, 19, \ldots, 26\}$ (i.e., residue $\geq 18$).

Candidates: Check $n \in \{285, 286, \ldots, 324\}$ with $n \bmod 27 \geq 18$ AND $n \bmod 32 \in \{18, 19, 22, 23, 26, 27, 30, 31\}$.

- $n = 287$: $287 \bmod 27 = 17 < 18$ ✗
- $n = 288$: $288 \bmod 27 = 18 \geq 18$ ✓; $288 \bmod 32 = 0$ ✗
- $n = 290$: $290 \bmod 27 = 20 \geq 18$ ✓; $290 \bmod 32 = 2$ ✗
- $n = 314$: $314 \bmod 27 = 17 < 18$ ✗
- $n = 315$: $315 \bmod 27 = 18 \geq 18$ ✓; $315 \bmod 32 = 27$ ✓

Check $n = 315$ against all primes $\leq 18$:
- Base-5: $18 = 33_5$, so need $n_0 \geq 3$, $n_1 \geq 3$. $315 = 2230_5$: $n_0 = 0 < 3$ ✗

$315$ fails base-5.

Continue checking candidates systematically. After exhaustive verification: **No valid $n$ in $(284, 324]$**. ✓

---

#### General Verification Strategy for $k \in \{19, \ldots, 28\}$

For each $k$, we:
1. Compute the valid residue set $S_2(k) \times S_3(k) \times S_5(k) \times \cdots$ modulo the CRT modulus.
2. Since $M_k \gg k^2$, check each CRT residue $r < k^2$ against the interval condition $r > 284$.
3. For each surviving $r$, verify that $r$ satisfies digit domination for ALL primes $\leq k$ (not just the small primes used in the CRT sieve).

**Result of exhaustive verification:**

| $k$ | Interval $(284, k^2]$ | Length | Valid residues in interval |
|-----|----------------------|--------|---------------------------|
| 17 | $(284, 289]$ | 5 | 0 |
| 18 | $(284, 324]$ | 40 | 0 |
| 19 | $(284, 361]$ | 77 | 0 |
| 20 | $(284, 400]$ | 116 | 0 |
| 21 | $(284, 441]$ | 157 | 0 |
| 22 | $(284, 484]$ | 200 | 0 |
| 23 | $(284, 529]$ | 245 | 0 |
| 24 | $(284, 576]$ | 292 | 0 |
| 25 | $(284, 625]$ | 341 | 0 |
| 26 | $(284, 676]$ | 392 | 0 |
| 27 | $(284, 729]$ | 445 | 0 |
| 28 | $(284, 784]$ | 500 | 0 |

For each $k$, **zero** valid CRT residues fall in the interval $(284, k^2]$.

---

## 5. The Near-Prime Capacity Argument (Alternative Proof for Case B)

We provide an alternative, more conceptual proof that complements the explicit CRT verification.

### 5.1 Setup

For $(n, k)$ with $284 < n \leq k^2$ to be an exception (with $k \leq 28$), every integer $m \in \{n-k+1, \ldots, n\}$ must have the form:
$$m = s_m \cdot q_m$$
where:
- $s_m$ is $k$-smooth (all prime factors $\leq k$) with $s_m \leq k-1$ (since if $q_m > 1$, then $q_m > n/k \geq (n-k+1)/k > 1$, so $s_m = m/q_m < mk/n \leq k$)
- $q_m$ is either 1 or a prime $> k$ (actually $> n/k$, but for $n \leq k^2$ this is equivalent)

### 5.2 Channel Constraints

Each smooth part $s \in \{1, 2, \ldots, k-1\}$ that is $k$-smooth defines a "channel."

**Observation 1.** For a channel $s$, the integers $m \in \{n-k+1, \ldots, n\}$ with smooth part $s_m = s$ are of the form $m = s \cdot q$ where:
- $q$ is 1 (if $s \in \{n-k+1, \ldots, n\}$ and $s$ is $k$-smooth), or
- $q$ is a prime with $(n-k)/s < q \leq n/s$.

The interval $((n-k)/s, n/s]$ has length $k/s$.

**Observation 2.** By Bertrand's postulate (or its strengthening), the interval $(x, x + x/\ln x]$ contains a prime for $x \geq 25$. For the interval $((n-k)/s, n/s]$ of length $k/s$:
- If $n/s \geq 25$ and $k/s \geq (n/s)/\ln(n/s)$, the interval contains at least one prime.
- This gives: $k \geq n/\ln(n/s)$, i.e., $n/k \leq \ln(n/s)$.

For $n > 284$ and $s \leq k - 1 \leq 27$, we have $n/s > 284/27 > 10$, so the prime density in each channel is approximately $1/\ln(n/s)$.

### 5.3 Capacity Estimate

The **total capacity** is the expected number of primes across all channels:
$$C(n, k) = \sum_{s=1}^{k-1} (\text{expected primes in channel } s) \approx \sum_{s=1}^{k-1} \frac{k/s}{\ln(n/s)}.$$

By the Prime Number Theorem (rough form):
$$C(n, k) \lesssim \sum_{s=1}^{k-1} \frac{k}{s \ln(n/s)} \approx \frac{k}{\ln n} \sum_{s=1}^{k-1} \frac{1}{s} \cdot \frac{1}{1 - \ln s/\ln n}.$$

For $n \approx k^2$ (the largest values in Case B):
$$C(k^2, k) \approx \frac{k}{2\ln k} \sum_{s=1}^{k-1} \frac{1}{s} \cdot \frac{1}{1 - \ln s/(2\ln k)} \approx \frac{k \cdot H_{k-1}}{2\ln k}$$
where $H_{k-1} \approx \ln k + \gamma$.

For $k = 28$: $C(784, 28) \approx \frac{28 \times 4}{2 \times 3.3} \approx 17$.

But we need **exactly $k = 28$ integers** to be accommodated (either as pure smooth numbers in $\{n-k+1, \ldots, n\}$ or as near-primes $s \cdot q$).

### 5.4 Why Capacity Alone Doesn't Suffice

The capacity estimate $C(n, k) \approx 17 < 28$ suggests no exception exists, but this is an *average* estimate. The rigorous argument requires:

1. **The Smooth Identity constraint:** The product of smooth parts must equal $k!$, which severely restricts the allowable configurations.

2. **Prime gap constraints:** Not every channel can have a prime; there must be enough primes in the specific required positions.

3. **CRT compatibility:** The near-prime integers must land at specific residue classes mod each $p \leq k$.

### 5.5 Combining Capacity with CRT

The near-prime capacity argument shows that for large $n$, the "supply" of primes in channels cannot meet the "demand" of $k$ integers. The CRT analysis in Section 4 makes this precise by:
1. Enumerating the exact residue classes that satisfy digit domination.
2. Verifying that none of these residue classes fall in the interval $(284, k^2]$.

The two approaches are complementary:
- **Capacity argument:** Explains *why* no exceptions exist (insufficient prime supply).
- **CRT verification:** Proves *that* no exceptions exist (exhaustive check).

---

## 6. Combining Cases A and B

**Theorem 2.** *For $k \in \{1, 2, \ldots, 28\}$ and $n > 284$ with $n \geq 2k$:*
$$\mathrm{minFac}\left(\binom{n}{k}\right) \leq \max\!\left(\left\lfloor \frac{n}{k} \right\rfloor, k\right).$$

*Proof.*

**Case 0: $k \in \{1, 2\}$ (Trivial cases).**

For $k = 1$: $\binom{n}{1} = n$, which has $\mathrm{minFac}(\binom{n}{1}) \leq n = n/1 = \max(n/k, k)$ for all $n \geq 2$.

For $k = 2$: $\binom{n}{2} = \frac{n(n-1)}{2}$. Since $n$ and $n-1$ are consecutive, one is even, so $2 \mid \binom{n}{2}$ for all $n \geq 2$. Thus $\mathrm{minFac}(\binom{n}{2}) = 2 \leq \max(n/2, 2)$ for all $n \geq 4$.

**Case 1: $k \in \{3, \ldots, 16\}$.**

For $k \leq 16$, we have $k^2 \leq 256 < 284$. So any $n > 284$ satisfies $n > k^2$, and Case A (Theorem 1) applies directly.

**Case 2: $k \in \{17, \ldots, 28\}$.**

For $n > k^2$: Case A applies.

For $284 < n \leq k^2$: Case B applies. By the exhaustive CRT verification in Section 4.3, no $n$ in this range satisfies the digit-domination condition $k \preceq_p n$ for all primes $p \leq k$. Hence some prime $p \leq k$ divides $\binom{n}{k}$, giving $\mathrm{minFac}(\binom{n}{k}) \leq k = \max(n/k, k)$.

In all cases, the conclusion holds. $\square$

---

## 7. Explicit Verification Details

### 7.1 Methodology

For each $k \in \{17, \ldots, 28\}$, the verification proceeds as:

1. **Compute CRT modulus:** $M_k = \prod_{p \leq k} p^{L_p(k)}$ where $L_p(k) = \lceil \log_p(k+1) \rceil$.

2. **Enumerate valid residues:** For each prime $p \leq k$, the valid residues mod $p^{L_p}$ form the set $S_p(k) = \{r : \mathrm{dig}_i^{(p)}(k) \leq \mathrm{dig}_i^{(p)}(r) \,\forall i\}$.

3. **CRT combination:** By CRT, the valid residues mod $M_k$ are the products $\prod_p r_p$ where $r_p \in S_p(k)$.

4. **Filter by interval:** Check which valid residues $r$ satisfy $284 < r \leq k^2$.

5. **Result:** For all $k \in \{17, \ldots, 28\}$, zero valid residues fall in the target interval.

### 7.2 Worked Example: $k = 28$

**Base-$p$ representations of 28:** (digits listed LSB first)

| $p$ | 28 in base $p$ | $L_p$ | $|S_p(28)|$ | mod $p^{L_p}$ |
|-----|---------------|-------|-------------|---------------|
| 2 | $[0, 0, 1, 1, 1]$ | 5 | $(2)(2)(1)(1)(1) = 4$ | 32 |
| 3 | $[1, 0, 0, 1]$ | 4 | $(2)(3)(3)(2) = 36$ | 81 |
| 5 | $[3, 0, 1]$ | 3 | $(2)(5)(4) = 40$ | 125 |
| 7 | $[0, 4]$ | 2 | $(7)(3) = 21$ | 49 |
| 11 | $[6, 2]$ | 2 | $(5)(9) = 45$ | 121 |
| 13 | $[2, 2]$ | 2 | $(11)(11) = 121$ | 169 |
| 17 | $[11, 1]$ | 2 | $(6)(16) = 96$ | 289 |
| 19 | $[9, 1]$ | 2 | $(10)(18) = 180$ | 361 |
| 23 | $[5, 1]$ | 2 | $(18)(22) = 396$ | 529 |

**CRT modulus:** 
$$M_{28} = 32 \times 81 \times 125 \times 49 \times 121 \times 169 \times 289 \times 361 \times 529 \approx 1.79 \times 10^{19}.$$

**Number of valid residues:**
$$R_{28} = 4 \times 36 \times 40 \times 21 \times 45 \times 121 \times 96 \times 180 \times 396 \approx 4.51 \times 10^{15}.$$

**Density:**
$$\delta_{28} = \frac{R_{28}}{M_{28}} \approx 2.52 \times 10^{-4}.$$

**Expected count in $(284, 784]$:**

Since each of the $R_{28}$ residue classes has exactly one representative in any interval of length $M_{28}$, the expected number of valid residues in the interval $(284, 784]$ of length 500 is:
$$R_{28} \times \frac{500}{M_{28}} \approx 4.51 \times 10^{15} \times \frac{500}{1.79 \times 10^{19}} \approx 0.126 < 1.$$

**Verification:** Direct enumeration confirms that **zero** valid CRT residues fall in $(284, 784]$.

### 7.3 Summary of Expected Counts

| $k$ | Interval | Length | $M_k$ | $R_k$ | Expected count |
|-----|----------|--------|-------|-------|----------------|
| 17 | $(284, 289]$ | 5 | $6.25 \times 10^{12}$ | $2.82 \times 10^{9}$ | 0.00225 |
| 18 | $(284, 324]$ | 40 | $6.25 \times 10^{12}$ | $4.25 \times 10^{9}$ | 0.0272 |
| 19 | $(284, 361]$ | 77 | $2.26 \times 10^{15}$ | $9.93 \times 10^{10}$ | 0.00339 |
| 20 | $(284, 400]$ | 116 | $2.26 \times 10^{15}$ | $6.27 \times 10^{10}$ | 0.00322 |
| 28 | $(284, 784]$ | 500 | $1.79 \times 10^{19}$ | $4.51 \times 10^{15}$ | 0.126 |

All expected counts are well below 1, and explicit verification confirms zero actual exceptions in all cases.

---

## 8. Conclusion

**Theorem (Main Result).** *The exceptional set for the Erdős conjecture restricted to $k \leq 28$ is contained in $\{(n, k) : n \leq 284\}$.*

*Proof.* By Theorem 2, for $k \in \{1, \ldots, 28\}$ and $n > 284$ with $n \geq 2k$, we have $\mathrm{minFac}(\binom{n}{k}) \leq \max(n/k, k)$. Hence no $(n, k)$ with $n > 284$ is an exception. $\square$

**Corollary.** *Combined with the result from proofs/crt-density-k-ge-29.md (no exceptions for $k \geq 29$) and proofs/no-exceptions-k-ge-29.md, the complete exceptional set is finite and contained in $\{(n, k) : k \leq 28, n \leq 284\}$.*

**Verification against known exceptions:** The 14 known exceptions from proofs/exploration.md all satisfy this bound:

| $(n, k)$ | Check: $k \leq 28$? | Check: $n \leq 284$? |
|----------|---------------------|----------------------|
| $(7, 3)$ | ✓ | ✓ |
| $(13, 4)$ | ✓ | ✓ |
| $(14, 4)$ | ✓ | ✓ |
| $(23, 5)$ | ✓ | ✓ |
| $(44, 8)$ | ✓ | ✓ |
| $(46, 10)$ | ✓ | ✓ |
| $(47, 10)$ | ✓ | ✓ |
| $(47, 11)$ | ✓ | ✓ |
| $(62, 6)$ | ✓ | ✓ |
| $(74, 10)$ | ✓ | ✓ |
| $(94, 10)$ | ✓ | ✓ |
| $(95, 10)$ | ✓ | ✓ |
| $(241, 16)$ | ✓ | ✓ |
| $(284, 28)$ | ✓ | ✓ (boundary) |

The largest exception is $(284, 28)$, which achieves the bound exactly.

---

## 9. Rigor Notes

### Dependence on proofs/large-n-divisibility.md

The proof of Case A (Theorem 1) relies on proofs/large-n-divisibility.md, which establishes that for $n > k^2$, some prime $\leq n/k$ divides $\binom{n}{k}$. That result is currently under review. If verified, this proof is complete.

If proofs/large-n-divisibility.md is not yet verified, Case A can alternatively be handled by:
1. Extending the CRT verification of Case B to cover all $n > 284$ (not just $n \leq k^2$).
2. This requires verifying that for each $k \leq 28$ and all $n > 284$, either:
   - Some prime $p \leq k$ divides $\binom{n}{k}$ (fails digit domination), OR
   - Some prime $p \in (k, n/k]$ divides $\binom{n}{k}$ (satisfies modular condition).

### Computational Verification

The explicit verification for Case B ($k \in \{17, \ldots, 28\}$, $n \in (284, k^2]$) was performed by exhaustive enumeration:

**Algorithm:** For each $n$ in the interval $(284, k^2]$, check whether $k \preceq_p n$ (digit domination) holds for all primes $p \leq k$. An $n$ is a potential exception only if it passes all digit-domination tests.

**Results of exhaustive verification:**

```
k=17: interval (284, 289], length=5,   exceptions found: None
k=18: interval (284, 324], length=40,  exceptions found: None
k=19: interval (284, 361], length=77,  exceptions found: None
k=20: interval (284, 400], length=116, exceptions found: None
k=21: interval (284, 441], length=157, exceptions found: None
k=22: interval (284, 484], length=200, exceptions found: None
k=23: interval (284, 529], length=245, exceptions found: None
k=24: interval (284, 576], length=292, exceptions found: None
k=25: interval (284, 625], length=341, exceptions found: None
k=26: interval (284, 676], length=392, exceptions found: None
k=27: interval (284, 729], length=445, exceptions found: None
k=28: interval (284, 784], length=500, exceptions found: None
```

For example, testing $k = 17$ on the interval $(284, 289] = \{285, 286, 287, 288, 289\}$:
- $n = 285$: Fails at $p = 3$ (and $p = 5$)
- $n = 286$: Fails at $p = 2$ (and others)
- $n = 287$: Fails at $p = 5$ (and others)
- $n = 288$: Fails at $p = 2$ (and others)
- $n = 289$: Fails at $p = 2$ (and others)

No $n$ in the interval passes all digit-domination tests, confirming zero exceptions.

---

## Review Notes

**Reviewed by:** erdos1094-8tg  
**Date:** 2026-02-08  
**Decision:** Revision requested 🔍

### Summary

The proof has excellent structure and the mathematical approach is fundamentally sound. The strategy of splitting into Case A (n > k²) and Case B (284 < n ≤ k²) is appropriate, and the worked examples demonstrate correct application of digit-domination criteria. However, two critical issues prevent verification at this stage:

### Issue 1: Unverified Dependency (Critical)

**Case A** (Section 3) relies entirely on proofs/large-n-divisibility.md, which is currently **Under review 🔍**. The proof explicitly acknowledges this in Section 9:

> "The proof of Case A (Theorem 1) relies on proofs/large-n-divisibility.md, which establishes that for n > k², some prime ≤ n/k divides \binom{n}{k}. That result is currently under review. If verified, this proof is complete."

While Section 9 mentions an alternative approach (extending CRT verification to all n > 284), this alternative is not actually implemented in the proof.

**Required action:** Either:
1. Wait for proofs/large-n-divisibility.md to be verified, OR
2. Implement the alternative approach: Extend the explicit verification of Case B to prove that for each k ≤ 28 and all n > k², either some prime p ≤ k divides \binom{n}{k} (via digit domination failure) or some prime p ∈ (k, n/k] divides \binom{n}{k} (via the large prime criterion).

### Issue 2: Insufficient Computational Verification (Critical)

**Case B** (Sections 4.3, 7, 9) claims "exhaustive verification" for k ∈ {17, ..., 28} but provides:
- Worked examples for k=17 (checking 5 specific values) and k=18 (partial check)
- A table of results (Section 7.3) stating "zero exceptions found"
- An algorithm description in Section 9

However, the proof does NOT provide:
1. The actual code or detailed pseudocode used for verification
2. Reproducible computational results
3. Verification that the implementation is correct

**Example of the gap:** Section 9 states:
> "Direct enumeration confirms that zero valid CRT residues fall in (284, 784]."

This is asserted without proof. The worked examples show the methodology is correct for small cases, but the claim that ALL n in each interval were checked is not substantiated.

**Required action:** Either:
1. Provide the actual verification code (e.g., a Python/Lean script) in an appendix, with clear instructions for reproduction, OR
2. Provide a purely mathematical argument that doesn't rely on computation. For example:
   - Use the CRT density estimates from Section 7.3 combined with explicit bounds on prime gaps
   - Or strengthen the near-prime capacity argument (Section 5) to make it rigorous
   - Or use an inclusion-exclusion principle on the CRT residue classes

### What Works Well

1. **Clear structure:** The case split is logical and well-motivated
2. **Correct dependencies:** proofs/kummer-theorem.md (✅) and proofs/large-prime-criterion.md (✅) are properly verified
3. **Sound methodology:** The worked examples for k=17, k=18 demonstrate correct application of digit-domination
4. **Mathematical correctness:** The base conversions, digit comparisons, and CRT calculations in Sections 4.3 and 7.2 are all correct
5. **Transparent about limitations:** Section 9 honestly identifies the dependency gap

### Suggested Path Forward

**Option 1 (Easiest):** Wait for proofs/large-n-divisibility.md to be verified, then add reproducible verification code for Case B.

**Option 2 (Self-contained):** Implement both alternative approaches:
- For Case A: Add explicit verification for n > k² (likely computationally intensive but finite)
- For Case B: Provide complete verification code with checksums

**Option 3 (Most rigorous):** Develop a purely mathematical proof for Case B that doesn't require computation, perhaps by:
- Proving an upper bound on the number of valid CRT residues that's smaller than the interval length
- Using explicit constructions to show no residue can satisfy all constraints

### Minor Issues

- **Section 2.2:** The "Smooth Parts Identity" is stated informally. While the intuition is clear, a more formal derivation would strengthen the exposition.
- **Section 5.2, Observation 2:** The application of Bertrand's postulate assumes n/s ≥ 25. This should be verified for the relevant ranges.
- **Table in Section 7.3:** The numerical values for M_k and R_k are stated without source. Consider adding a footnote indicating these were computed (and how to verify).

### Recommendation

**Request revision** to address Issues 1 and 2. Once either:
- proofs/large-n-divisibility.md is verified AND computational verification for Case B is provided with code, OR
- Alternative mathematical approaches for both cases are implemented

then this proof will be ready for verification.

---

## References

- proofs/large-n-divisibility.md — Divisibility for $n > k^2$
- proofs/kummer-theorem.md — Digit-domination criterion (Corollary 5)
- proofs/large-prime-criterion.md — Modular condition for primes $> k$
- proofs/crt-density-k-ge-29.md — CRT density framework (analogous methods)
