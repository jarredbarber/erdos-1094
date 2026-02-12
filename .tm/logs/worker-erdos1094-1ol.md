# timtam Task: Prove or refute residual_case_vacuous axiom (erdos1094-1ol)

Role: explore
Agent: explore (google-antigravity/claude-opus-4-6-thinking:high)
Start Time: 2026-02-12T01:29:30.007Z

## Agent Interaction



> **Thinking:**
> Let me understand the task. I need to analyze an axiom called `residual_case_vacuous` in the Lean codebase and prove or refute it mathematically. Let me start by reading the relevant Lean file and understanding the exact statement, then check existing proofs.


```bash
$ cd /home/jarred/code/erdos-1094 && cat -n KGe29.lean | sed -n '300,330p'
```

```bash
$ cd /home/jarred/code/erdos-1094 && ls proofs/ 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-1094 && find . -name "*.lean" | head -20
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat proofs/dead-ends.md
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat -n Erdos/KGe29.lean | sed -n '295,340p'
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat -n Erdos/KGe29.lean | sed -n '340,360p'
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-1ol --status "Reading axiom and understanding constraints"
```
Now let me read the broader context around how this axiom is used, and the existing proofs:
```bash
$ cd /home/jarred/code/erdos-1094 && cat -n Erdos/KGe29.lean | sed -n '358,400p'
```

```bash
$ cd /home/jarred/code/erdos-1094 && cat proofs/large-n-divisibility.md
```
Now I have a thorough understanding of the context. Let me carefully analyze the axiom `residual_case_vacuous`:
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-1ol --status "Analyzing the mathematical constraints of residual_case_vacuous"
```
Let me understand the exact Lean statement precisely, including what the natural number division means:
```bash
$ cd /home/jarred/code/erdos-1094 && cat -n Erdos/KGe29.lean | sed -n '310,315p'
```
Let me now work through the mathematics carefully. The axiom states: there are no natural numbers $n, k$ with $k \geq 2$ and $n \geq 2k^2$ such that:

1. $\lfloor n/k \rfloor$ is $k$-smooth (all prime factors $\leq k$)
2. $n / \gcd(n,k)$ is prime
3. $n / k < n / \gcd(n,k)$

Let me think about this systematically. Condition (3) says $n/\gcd(n,k) > n/k$, which (for positive values) means $\gcd(n,k) < k$, i.e., $k \nmid n$.

Let me set $g = \gcd(n,k)$ and $d = n/g$ (exact division since $g | n$). Let $n = gm$ where $\gcd(m, k/g) = 1$ (since $g = \gcd(n,k)$ and $k = g \cdot (k/g)$).

So $d = n/g = m$. And condition (2) says $m$ is prime. Condition (3) says $\lfloor n/k \rfloor < m$, which in natural number division means $n/k < n/g = m$, meaning $g < k$ (since both are exact/floor divisions).

Now, $m$ is prime. We have $n = gm$ where $g | k$, $g < k$, $g | n$, and $\gcd(m, k/g) = 1$.

Condition (1): every prime factor of $\lfloor n/k \rfloor = \lfloor gm/k \rfloor$ is $\leq k$.

Since $g | k$, let $k = g \cdot q$ for some integer $q \geq 2$ (because $g < k$ and both are positive). Then $\lfloor n/k \rfloor = \lfloor gm/(gq) \rfloor = \lfloor m/q \rfloor$.

So condition (1) says $\lfloor m/q \rfloor$ is $k$-smooth.

And $n \geq 2k^2$, so $gm \geq 2g^2 q^2$, meaning $m \geq 2gq^2$.

Since $m$ is prime and $m \geq 2gq^2 \geq 2 \cdot 1 \cdot 4 = 8$, so $m \geq 8$.

Now, $\lfloor m/q \rfloor$. Since $m$ is prime and $m \geq 2gq^2 \geq 4q$, we have $\lfloor m/q \rfloor \geq 4$. Since $q \geq 2$, $\lfloor m/q \rfloor \leq m/2 < m$.

The key question: can $\lfloor m/q \rfloor$ be $k$-smooth (= $gq$-smooth) when $m$ is a large prime?

Let me think about what $\lfloor m/q \rfloor$ looks like. Write $m = aq + r$ where $0 \leq r < q$. Then $\lfloor m/q \rfloor = a$, and $m = aq + r$.

We need every prime factor of $a$ to be $\leq k = gq$. And $a = (m-r)/q \geq (m - q + 1)/q$.

Since $m \geq 2gq^2$, we have $a \geq 2gq - 1 + 1/q > 2gq - 1 \geq 2g \cdot 2 - 1 = 4g - 1 \geq 3$.

Can $a$ actually be $gq$-smooth? Sure, for instance if $a$ is a power of 2. But we also need $m = aq + r$ to be prime. Let me look for concrete examples or impossibilities.

Let me try a small case: $k = 2$, so $g = \gcd(n, 2) < 2$, meaning $g = 1$. Then $q = k/g = 2$. $n = m$ (prime), $n \geq 2 \cdot 4 = 8$.

$\lfloor m/2 \rfloor$ must be $2$-smooth (power of 2). So $\lfloor m/2 \rfloor = 2^j$ for some $j$. Since $m$ is an odd prime (as $g=1$ means $n$ is odd... wait, $g = \gcd(n,2)$. If $n$ is even, $g = 2$, but $g < k = 2$ is impossible. If $n$ is odd, $g = 1$. So $n = m$ is an odd prime.)

$\lfloor m/2 \rfloor = (m-1)/2$ (since $m$ is odd). We need $(m-1)/2 = 2^j$, so $m = 2^{j+1} + 1$. We need $m$ prime and $m \geq 8$.

$j = 2$: $m = 5$ (prime, but $5 < 8$, fails $n \geq 2k^2$).
$j = 3$: $m = 17$ (prime, $\geq 8$ ✓). Check: $n = 17, k = 2$, $g = \gcd(17,2) = 1$, $d = n/g = 17$ (prime ✓), $\lfloor 17/2 \rfloor = 8 = 2^3$ (2-smooth ✓), $8 < 17$ ✓, $n = 17 \geq 2 \cdot 4 = 8$ ✓.

**This is a counterexample!** $(n, k) = (17, 2)$ satisfies all four conditions and the conclusion $\text{False}$ fails.

Wait, let me double-check the Lean natural number division carefully.

- $k = 2$, $n = 17$
- `hk : 2 ≤ k` → $2 \leq 2$ ✓
- `hn : 2 * k * k ≤ n` → $2 \cdot 2 \cdot 2 = 8 \leq 17$ ✓
- `n / k = 17 / 2 = 8` (Nat division)
- `hsmooth : ∀ p, p.Prime → p ∣ 8 → p ≤ 2` → prime factors of 8 are just {2}, and $2 \leq 2$ ✓
- `n.gcd k = gcd(17, 2) = 1`
- `n / n.gcd k = 17 / 1 = 17`
- `hprime : 17.Prime` → ✓
- `hlarge : n / k < n / n.gcd k` → `8 < 17` ✓

All conditions satisfied! $(n, k) = (17, 2)$ is a counterexample to the axiom.

Let me also check $j = 4$: $m = 33$ (not prime). $j = 5$: $m = 65$ (not prime). $j = 6$: $m = 129$ (not prime). $j = 7$: $m = 257$ (prime!). So $(257, 2)$ is another counterexample.

Actually, these are Fermat primes! $m = 2^{j+1}+1$ being prime means $j+1$ must be a power of 2 (Fermat prime). But actually that's a necessary condition for primality only for the form $2^n + 1$ to be prime. Known Fermat primes: $F_0 = 3, F_1 = 5, F_2 = 17, F_3 = 257, F_4 = 65537$.

So $(17, 2)$, $(257, 2)$, $(65537, 2)$ are all counterexamples for $k = 2$.

Now let me also check some other values of $k$. For $k = 3$: $g = \gcd(n, 3) < 3$, so $g \in \{1, 2\}$.

If $g = 1$: $q = 3$, $n = m$ prime, $m \geq 18$. $\lfloor m/3 \rfloor$ must be 3-smooth. $m \equiv 1$ or $2 \pmod{3}$ (since $m$ is prime $> 3$). $\lfloor m/3 \rfloor = (m - r)/3$ where $r = m \bmod 3 \in \{1, 2\}$. We need $(m-r)/3 = 2^a \cdot 3^b$ for some $a, b \geq 0$.

$m-r$ must be $3 \cdot 2^a \cdot 3^b = 2^a \cdot 3^{b+1}$. And $m = 2^a \cdot 3^{b+1} + r$ must be prime with $r \in \{1, 2\}$.

Some examples: $a=3, b=0$: $m = 24 + 1 = 25$ (not prime) or $m = 26$ (not prime). $a = 4, b = 0$: $m = 48 + 1 = 49$ (not prime). $a = 1, b = 1$: $m = 18 + 1 = 19$ (prime! ≥ 18 ✓).

Check $(19, 3)$: $g = \gcd(19, 3) = 1$, $d = 19$ (prime), $\lfloor 19/3 \rfloor = 6 = 2 \cdot 3$ (3-smooth ✓), $6 < 19$ ✓, $19 \geq 18$ ✓. **Counterexample!**

If $g = 2$: $q = 3/2$... wait, $g | k$, so $g | 3$, meaning $g \in \{1, 3\}$. But $g < k = 3$ means $g \in \{1, 2\}$. And $g | 3$ means $g = 1$. So only $g = 1$ works for $k = 3$.

OK, so the axiom is **false**. Let me write this up properly, looking at how this affects the overall proof before I do.
```bash
$ cd /home/jarred/code/erdos-1094 && grep -n "residual_case_vacuous" Erdos/KGe29.lean
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-1ol --status "Found counterexample (17,2) to axiom. Writing up proof."
```
Now let me also understand the context better — the axiom is only used in the `prime_large_divisor_case` function at line 343, which is called at line 375 from `large_n_minFac_bound`. The key point: when this axiom is used, the additional hypothesis `hk29 : 29 ≤ k` is in scope, and also `hA` says all prime factors of $n/k$ are $\leq k$. Let me check whether the counterexamples satisfy $k \geq 29$.
```bash
$ cd /home/jarred/code/erdos-1094 && cat -n Erdos/KGe29.lean | sed -n '316,344p'
```
So the axiom `residual_case_vacuous` takes $k \geq 2$ (not $k \geq 29$), but it's only *called* from a context where $k \geq 29$. This means the axiom as stated is too strong (it claims False for all $k \geq 2$), but what we actually need is the statement for $k \geq 29$. My counterexamples at $k = 2$ and $k = 3$ refute the axiom as stated, but the *usage* only needs $k \geq 29$.

Let me think about whether counterexamples exist for large $k$. For $k \geq 29$, the constraints are much tighter. Let me analyze:

With $g = \gcd(n, k)$, $g | k$, $g < k$ (from $\lfloor n/k \rfloor < n/g$), $n = gm$ where $m$ is prime, and $\lfloor n/k \rfloor = \lfloor gm/k \rfloor$ is $k$-smooth.

For $k \geq 29$, $n \geq 2k^2 \geq 1682$.

Let's set $k = gq$ and look at $\lfloor m/q \rfloor$. We need this to be $k$-smooth, and $m \geq 2gq^2$. Since $m$ is prime, $m$ itself is NOT $k$-smooth (as $m > k$ since $m \geq 2gq^2 = 2kq \geq 2k \cdot 2 = 4k > k$).

Now, $\lfloor m/q \rfloor \approx m/q = m \cdot g / k$. Since $m$ is a large prime, $\lfloor m/q \rfloor$ is "almost arbitrary" — it can be any value around $m/q$. There's no obvious reason it can't be $k$-smooth for $k \geq 29$.

Actually, for $k = 29$: possible divisors $g$ of 29 with $g < 29$ are just $g = 1$ (since 29 is prime). So $q = 29$, $n = m$ prime, $m \geq 2 \cdot 29^2 = 1682$.

$\lfloor m/29 \rfloor$ must be 29-smooth. $m \geq 1682$ means $\lfloor m/29 \rfloor \geq 58$.

We need a prime $m \geq 1682$ such that $\lfloor m/29 \rfloor$ is 29-smooth. Write $m = 29a + r$ with $0 \leq r < 29$. We need $a$ to be 29-smooth and $29a + r$ to be prime.

Take $a = 58 = 2 \cdot 29$. Then $m = 29 \cdot 58 + r = 1682 + r$. We need $1682 + r$ prime for some $r \in \{0, 1, \ldots, 28\}$.

$1682 + 1 = 1683 = 3 \cdot 561 = 3 \cdot 3 \cdot 187$. Not prime.
$1682 + 7 = 1689 = 3 \cdot 563$. Not prime. 
$1682 + 11 = 1693$. Is this prime? $1693 / 7 = 241.8$, $1693 / 11 = 153.9$, $1693 / 13 = 130.2$, $1693 / 17 = 99.6$, $1693 / 19 = 89.1$, $1693 / 23 = 73.6$, $1693 / 29 = 58.4$, $1693 / 31 = 54.6$, $1693 / 37 = 45.8$, $1693 / 41 = 41.3$, $\sqrt{1693} \approx 41.1$. Need to check primes up to 41.

Let me just compute this:
```bash
$ python3 -c "
from sympy import isprime, factorint

# k=29 (prime, so g=1, q=29)
k = 29
for a in range(58, 200):
    # Check if a is 29-smooth
    factors = factorint(a)
    if all(p <= 29 for p in factors):
        for r in range(29):
            m = 29 * a + r
            if isprime(m) and m >= 2*k*k:
                print(f'n={m}, k={k}, n/k={m//k}={a}, gcd={1}, n/gcd={m}, COUNTEREXAMPLE')
                break
        else:
            continue
" 2>/dev/null | head -20
```

```bash
$ python3 -c "
from sympy import isprime, factorint

# k=29 (prime, so g=1, q=29)
k = 29
count = 0
for a in range(58, 500):
    # Check if a is 29-smooth
    factors = factorint(a)
    if all(p <= 29 for p in factors):
        for r in range(29):
            m = 29 * a + r
            if isprime(m) and m >= 2*k*k:
                print(f'n={m}, k={k}, floor(n/k)={m//k}, gcd(n,k)=1, n/gcd(n,k)={m} (prime)')
                count += 1
                if count >= 10:
                    break
        if count >= 10:
            break
" 2>/dev/null
```

```bash
$ python3 << 'EOF'
from sympy import isprime, factorint

k = 29
count = 0
for a in range(58, 500):
    factors = factorint(a)
    smooth = all(p <= 29 for p in factors)
    if smooth:
        for r in range(29):
            m = 29 * a + r
            if isprime(m) and m >= 2*k*k:
                print(f"n={m}, k={k}, floor(n/k)={m//k}, gcd=1, n/gcd={m} (prime)")
                count += 1
                break
    if count >= 10:
        break

if count == 0:
    print("No counterexamples found for k=29 in range")
EOF
```

```bash
$ python3 << 'EOF'
import math

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True

def is_k_smooth(n, k):
    if n <= 1: return True
    for p in range(2, k+1):
        if not is_prime(p): continue
        while n % p == 0:
            n //= p
    return n == 1

def prime_factors(n):
    factors = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.add(d)
            n //= d
        d += 1
    if n > 1: factors.add(n)
    return factors

# k=29 (prime, so g must be 1)
k = 29
count = 0
for a in range(58, 2000):
    if not is_k_smooth(a, k):
        continue
    for r in range(29):
        m = 29 * a + r
        if m < 2 * k * k:
            continue
        if is_prime(m):
            g = math.gcd(m, k)
            d = m // g
            if is_prime(d) and m // k < d:
                pf = prime_factors(m // k)
                if all(p <= k for p in pf):
                    print(f"COUNTEREXAMPLE: n={m}, k={k}, n/k={m//k}, gcd(n,k)={g}, n/gcd(n,k)={d}")
                    count += 1
                    break
    if count >= 5:
        break

if count == 0:
    print("No counterexamples found for k=29 in range a=58..1999")
else:
    print(f"Found {count} counterexamples for k=29")
EOF
```
The axiom is definitively **false**, even for $k = 29$. There are many counterexamples. Let me verify the simplest one more carefully:
```bash
$ python3 << 'EOF'
import math

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True

# Verify n=1693, k=29
n, k = 1693, 29
print(f"n = {n}, k = {k}")
print(f"hk: 2 <= {k}? {2 <= k}")
print(f"hn: 2*{k}*{k} = {2*k*k} <= {n}? {2*k*k <= n}")
print(f"n / k = {n // k}")

# Check smoothness of n/k
nk = n // k
print(f"n / k = {nk}")
print(f"  58 = 2 * 29. Prime factors: 2, 29. All <= {k}? True")
print(f"  is 2 <= 29? True. is 29 <= 29? True.")

g = math.gcd(n, k)
print(f"gcd(n, k) = {g}")
d = n // g
print(f"n / gcd(n,k) = {d}")
print(f"Is {d} prime? {is_prime(d)}")
print(f"hlarge: n/k < n/gcd(n,k)? {nk} < {d}? {nk < d}")
print()
print(f"All conditions satisfied → axiom claims False, but we have a valid (n,k).")
print(f"The axiom residual_case_vacuous is REFUTED.")
print()

# Now let's also check: does C(1693,29) actually have a small prime factor?
# This is relevant to understanding whether the overall proof strategy is broken
from functools import reduce
def choose(n, k):
    if k < 0 or k > n: return 0
    if k == 0 or k == n: return 1
    k = min(k, n - k)
    result = 1
    for i in range(k):
        result = result * (n - i) // (i + 1)
    return result

c = choose(1693, 29)
# Find smallest prime factor
p = 2
while p * p <= c:
    if c % p == 0:
        break
    if p == 2:
        p = 3
    else:
        p += 2
else:
    p = c  # c itself is prime

print(f"C({n},{k}) smallest prime factor: {p}")
print(f"max(n/k, k) = max({n//k}, {k}) = {max(n//k, k)}")
print(f"Is minFac(C(n,k)) <= max(n/k,k)? {p <= max(n//k, k)}")
EOF
```
So the axiom is false, but importantly, $C(1693, 29)$ still has a small prime factor (3 ≤ 58), so the *overall theorem* is fine — the proof strategy just uses a wrong intermediate lemma. The axiom over-claims: it says these conditions are *impossible*, but they're not — they just don't constitute exceptions to the Erdős conjecture.

Now let me understand why the axiom exists. It's used to handle "Case 2B" where $n \geq 2k^2$, $d = n/\gcd(n,k)$ is prime and $d > n/k$, and $n/k$ is $k$-smooth. The proof claims this case is vacuous, but it's not — we need to prove $\text{minFac}(\binom{n}{k}) \leq n/k$ by other means in this case.

Let me write up the refutation now:
🛠️ **Executing tool: write**

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-1ol --status "Proof written to proofs/residual-case-vacuous.md. Axiom REFUTED with counterexamples."
```
```json
{
  "status": "completed",
  "summary": "Refuted residual_case_vacuous axiom. Published to proofs/residual-case-vacuous.md",
  "details": "Confidence: Certain. The axiom is FALSE — counterexamples exist for all k ≥ 2, including k ≥ 29 where it's actually used.\n\nKey counterexamples:\n- (n=17, k=2): ⌊17/2⌋=8=2³ (2-smooth), gcd(17,2)=1, 17/1=17 (prime), 8<17\n- (n=19, k=3): ⌊19/3⌋=6=2·3 (3-smooth), gcd(19,3)=1, 19/1=19 (prime), 6<19  \n- (n=1693, k=29): ⌊1693/29⌋=58=2·29 (29-smooth), gcd(1693,29)=1, 1693 (prime), 58<1693\n\nThe axiom claims these conditions are contradictory, but they're easily satisfiable: take any prime n>2k² coprime to k such that ⌊n/k⌋ is k-smooth. Such primes are abundant.\n\nCritically, the overall theorem (minFac(C(n,k)) ≤ n/k) is still TRUE at these counterexamples — e.g., minFac(C(1693,29))=3 ≤ 58. The axiom's proof strategy (using d=n/gcd(n,k) as witness) fails when d is prime and large, but other primes ≤ k still divide C(n,k). The proof needs restructuring, not the theorem."
}
```

## Final Result

```json
{
  "status": "completed",
  "summary": "Refuted residual_case_vacuous axiom. Published to proofs/residual-case-vacuous.md",
  "details": "Confidence: Certain. The axiom is FALSE — counterexamples exist for all k ≥ 2, including k ≥ 29 where it's actually used.\n\nKey counterexamples:\n- (n=17, k=2): ⌊17/2⌋=8=2³ (2-smooth), gcd(17,2)=1, 17/1=17 (prime), 8<17\n- (n=19, k=3): ⌊19/3⌋=6=2·3 (3-smooth), gcd(19,3)=1, 19/1=19 (prime), 6<19  \n- (n=1693, k=29): ⌊1693/29⌋=58=2·29 (29-smooth), gcd(1693,29)=1, 1693 (prime), 58<1693\n\nThe axiom claims these conditions are contradictory, but they're easily satisfiable: take any prime n>2k² coprime to k such that ⌊n/k⌋ is k-smooth. Such primes are abundant.\n\nCritically, the overall theorem (minFac(C(n,k)) ≤ n/k) is still TRUE at these counterexamples — e.g., minFac(C(1693,29))=3 ≤ 58. The axiom's proof strategy (using d=n/gcd(n,k) as witness) fails when d is prime and large, but other primes ≤ k still divide C(n,k). The proof needs restructuring, not the theorem."
}
```

End Time: 2026-02-12T01:33:01.427Z
