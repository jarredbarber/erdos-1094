# timtam Task: Prove exceptions with k ≤ 28 satisfy n ≤ 284 (near-prime capacity) (erdos1094-w0p)

Role: explore
Agent: explore (anthropic/claude-opus-4-5:high)
Start Time: 2026-02-08T09:42:32.067Z

## Agent Interaction



> **Thinking:**
> Let me start by understanding the task. I need to prove that for k ∈ {1, 2, ..., 28} and n > 284, there exists a prime p ≤ max(n/k, k) that divides C(n,k).
> 
> First, let me check the existing literature in the proofs/ directory to understand what has already been established.


```bash
$ cd /home/jarred/code/erdos-1094 && ls -la proofs/ 2>/dev/null || echo "No proofs directory yet"
```

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-w0p --status "Reading existing literature and understanding the problem"
```
Good

> **Thinking:**
> , there are several existing proofs. Let me read the dead-ends first, then the exploration for the strategy, and finally the large-prime-criterion and large-n-divisibility which seem relevant.


🛠️ **Executing tool: read**

🛠️ **Executing tool: read**


> **Thinking:**
> Good, I now have a lot of context. Let me also read the large-prime-criterion and large-n-divisibility proofs which seem to be relevant to this task.


🛠️ **Executing tool: read**

🛠️ **Executing tool: read**


> **Thinking:**
> Now I have a thorough understanding of the context. Let me also look at the kummer-theorem.md proof to understand the digit-domination conditions better.


🛠️ **Executing tool: read**

```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-w0p --status "Developing near-prime capacity argument for k ≤ 28"
```
Now

> **Thinking:**
>  I have a good understanding of the context. Let me also check the crt-density-k-ge-29.md to understand how the CRT density analysis works for large k, which may provide insights for handling k ≤ 28.


🛠️ **Executing tool: read**
Now

> **Thinking:**
>  I have a thorough understanding of the context and the existing proofs. Let me now write the proof for the specific task at hand: proving that for k ≤ 28 and n > 284, there exists a prime p ≤ max(n/k, k) dividing C(n,k).
> 
> The key insight from the exploration is the "near-prime capacity" argument:
> 
> For C(n,k) to have all prime factors > max(n/k, k):
> 1. Each of the k consecutive integers {n-k+1, ..., n} must factor as s·q where s is k-smooth (all prime factors ≤ k) and q is either 1 or a prime > n/k.
> 2. For q > 1: s = m/q < m·k/n ≤ k (since q > n/k means q > n/k, so s < k)
> 3. So each integer m uses a "channel" s ∈ {1, 2, ..., k-1} for its smooth part
> 4. The product of all smooth parts must equal k! exactly
> 5. For large n, there are too many integers to fit in the channels
> 
> Let me develop this argument more rigorously. The key question is:
> 
> For a fixed k ≤ 28 and n > 284:
> - Case 1: n > k². Then by large-n-divisibility.md (once verified), there exists a prime p ≤ n/k dividing C(n,k).
> - Case 2: n ∈ (284, k²]. This only matters for k ≥ 17 (since 16² = 256 < 284).
> 
> Actually, wait. For k ≤ 28, we have:
> - k = 17: k² = 289, so (284, 289] could have exceptions
> - k = 18 through k = 28: k² ranges from 324 to 784
> 
> 
> - For the remaining cases, I'll split the analysis: when n exceeds k², the large-n result applies directly. When n falls in the intermediate range (284, k²], I need to verify that the near-prime capacity argument eliminates all potential exceptions through explicit checking.

Now I have a comprehensive understanding of the context. Let me develop the proof for exceptions with k ≤ 28 satisfying n ≤ 284.
```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-w0p --status "Writing proof for proofs/bound-n-for-small-k.md"
```
Now let

> **Thinking:**
>  me write the proof. The key elements are:
> 
> 1. For k ≤ 28 and n > k², the result follows from large-n-divisibility.md (once verified)
> 2. For k ≤ 28 and n ∈ (284, k²], we need to analyze each k in the range where k² > 284, which is k ∈ {17, 18, ..., 28}
> 
> For case 2, I'll use:
> - The digit-domination constraints (Kummer's theorem)
> - The CRT density framework similar to crt-density-k-ge-29.md
> - Explicit verification for the small intervals (284, k²]
> 
> Actually, let me reconsider the structure. The task description suggests using "near-prime capacity analysis". Let me think about this more carefully.
> 
> The near-prime capacity argument works like this:
> - For C(n,k) to avoid all primes ≤ max(n/k, k), each integer m ∈ {n-k+1, ..., n} must factor as s·q where:
>   - s = smooth part with all prime factors ≤ k
>   - q = 1 or a prime > n/k
> 
> - If q > n/k, then s = m/q < k·m/n ≤ k
> - So each m uses a "channel" s ∈ {1, ..., k-1} (or s is k-smooth and < k)
> - The product of all smooth parts must equal k! (this is the smooth parts identity)
> 
> The key constraint is that the smooth parts {s_m : m ∈ {n-k+1, ..., n}} must have product k!.
> 
> For large n, the "capacity" of channels to accommodate near-primes becomes insufficient.
> 
> However, I think for the small k case (k ≤ 28), the cleanest approach combines:
> 
> 
> 1. The large-n case (n > k²) handled by large-n-divisibility.md
> 2. The medium-n case (284 < n ≤ k²) requiring explicit CRT analysis for each relevant k value
> 
> Let me construct a comprehensive proof addressing both regimes.


🛠️ **Executing tool: write**


> **Thinking:**
> Let me review the proof I wrote and fix a few issues I noticed:
> 
> 1. In Section 7.2, I got confused about the density calculation. Let me correct this.
> 2. I should also provide more explicit worked examples for the verification.
> 3. The computation for |S_p(28)| needs verification.
> 
> Let me also double-check the base representations and calculations.

Let me verify and fix some calculations in the proof:
```bash
$ python3 << 'EOF'
# Verify base representations and S_p calculations for k=28

def to_base(n, p):
    """Return digits of n in base p (LSB first)"""
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % p)
        n //= p
    return digits

def count_valid_residues(k, p):
    """Count valid residues mod p^L for digit domination k ≤_p n"""
    digits_k = to_base(k, p)
    L = len(digits_k)
    count = 1
    for d in digits_k:
        count *= (p - d)
    return count, L

# Check for k = 28
k = 28
primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]

print(f"Analysis for k = {k}")
print("-" * 60)

M = 1  # CRT modulus
R = 1  # Number of valid residues

for p in primes:
    digits = to_base(k, p)
    count, L = count_valid_residues(k, p)
    mod = p ** L
    M *= mod
    R *= count
    print(f"p={p:2d}: {k} = {digits} (base {p}), L={L}, |S_p|={count}, mod={mod}")

print()
print(f"CRT modulus M = {M:,}")
print(f"Valid residues R = {R:,}")
print(f"Density = R/M = {R/M:.6f}")
print(f"Interval (284, {k**2}] has length {k**2 - 284}")
print(f"Expected count in interval = R * (k^2 - 284) / M = {R * (k**2 - 284) / M:.6f}")

# Check some specific k values
print("\n" + "=" * 60)
for k in [17, 18, 19, 20, 28]:
    M = 1
    R = 1
    for p in [p for p in [2, 3, 5, 7, 11, 13, 17, 19, 23] if p <= k]:
        count, L = count_valid_residues(k, p)
        M *= p ** L
        R *= count
    interval_len = k**2 - 284 if k**2 > 284 else 0
    expected = R * interval_len / M if M > 0 else 0
    print(f"k={k:2d}: interval ({284}, {k**2:3d}], len={interval_len:3d}, M={M:15,}, R={R:12,}, expected={expected:.6f}")
EOF

```
The

> **Thinking:**
>  calculations look better. The expected counts are all much less than 1, which is good. Let me now verify that indeed no actual valid residues fall in these intervals by doing an explicit enumeration for a few cases.


```bash
$ python3 << 'EOF'
# Explicit verification for k=17: check all n in (284, 289]

def to_base(n, p):
    """Return digits of n in base p (LSB first)"""
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % p)
        n //= p
    return digits

def digit_dominates(k, n, p):
    """Check if k ≤_p n (every digit of k ≤ corresponding digit of n)"""
    digits_k = to_base(k, p)
    digits_n = to_base(n, p)
    # Pad with zeros
    max_len = max(len(digits_k), len(digits_n))
    digits_k += [0] * (max_len - len(digits_k))
    digits_n += [0] * (max_len - len(digits_n))
    
    for dk, dn in zip(digits_k, digits_n):
        if dk > dn:
            return False
    return True

def check_all_primes(k, n):
    """Check if k ≤_p n for all primes p ≤ k"""
    primes = [p for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] if p <= k]
    failures = []
    for p in primes:
        if not digit_dominates(k, n, p):
            failures.append(p)
    return len(failures) == 0, failures

# Test k=17
print("Testing k=17, interval (284, 289]:")
print("-" * 50)
for n in range(285, 290):
    passes, failures = check_all_primes(17, n)
    status = "✓ PASS" if passes else f"✗ FAIL at p={failures}"
    print(f"  n={n}: {status}")

# Test k=18
print("\nTesting k=18, interval (284, 324]:")
print("-" * 50)
exceptions = []
for n in range(285, 325):
    passes, failures = check_all_primes(18, n)
    if passes:
        exceptions.append(n)
print(f"  Exceptions found: {exceptions if exceptions else 'None'}")

# Test k=28
print("\nTesting k=28, interval (284, 784]:")
print("-" * 50)
exceptions = []
for n in range(285, 785):
    passes, failures = check_all_primes(28, n)
    if passes:
        exceptions.append(n)
print(f"  Exceptions found: {exceptions if exceptions else 'None'}")

# Test all k from 17 to 28
print("\n" + "=" * 50)
print("Summary for all k in {17, ..., 28}:")
print("-" * 50)
for k in range(17, 29):
    k_sq = k ** 2
    if k_sq <= 284:
        print(f"k={k:2d}: k² = {k_sq} ≤ 284, no interval to check")
        continue
    exceptions = []
    for n in range(285, k_sq + 1):
        passes, _ = check_all_primes(k, n)
        if passes:
            exceptions.append(n)
    print(f"k={k:2d}: interval (284, {k_sq:3d}], exceptions found: {exceptions if exceptions else 'None'}")
EOF

```


> **Thinking:**
> Excellent! The explicit verification confirms that there are no exceptions in the intervals (284, k²] for any k ∈ {17, ..., 28}. This validates the proof.
> 
> Now let me update the proof with corrected calculations and clearer verification details.

The explicit verification confirms the proof. Let me update the document with corrected calculations:
🛠️ **Executing tool: edit**


> **Thinking:**
> Good. Now let me update the explicit verification section to add the computational results.


🛠️ **Executing tool: edit**


> **Thinking:**
> Now let me also verify that the proof correctly handles the k=1 and k=2 cases, which are trivial but should be mentioned.


🛠️ **Executing tool: edit**


> **Thinking:**
> Let me also add a small section clarifying that we've checked the known exceptions fall within n ≤ 284, and add some final polish.


🛠️ **Executing tool: edit**


> **Thinking:**
> Let me also fix a small issue in the table at Section 4.3 where I listed incorrect interval lengths, and make sure the verification details are complete.

Let me verify the interval length calculations:
```bash
$ python3 -c "
for k in range(17, 29):
    length = k**2 - 284
    print(f'k={k}: interval (284, {k**2}], length={length}')
"
```


> **Thinking:**
> The lengths look correct - they match what's in the proof. Now let me read the proof once more to verify everything is in order.


🛠️ **Executing tool: read**


> **Thinking:**
> The proof looks good. Now let me update the task status and provide the completion summary.


```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-w0p --status "Proof complete, verifying final details"
```
Let

> **Thinking:**
>  me provide a final verification that the proof file is complete.


```bash
$ cd /home/jarred/code/erdos-1094 && wc -l proofs/bound-n-for-small-k.md && head -30 proofs/bound-n-for-small-k.md
```


> **Thinking:**
> The proof looks complete and comprehensive. Let me now complete the task by providing the JSON summary.

The proof is complete. Let me provide the final task completion:

```json
{
  "status": "completed",
  "summary": "Proved that for k ≤ 28 and n > 284, there exists a prime p ≤ max(n/k, k) dividing C(n,k). Published to proofs/bound-n-for-small-k.md",
  "details": "Confidence: High. The proof splits into two cases:\n\n**Case A (n > k²):** References proofs/large-n-divisibility.md which establishes that primes in (k, n/k] force divisibility via the Interval Divisibility Lemma.\n\n**Case B (284 < n ≤ k²):** For k ∈ {17,...,28}, uses explicit CRT density analysis. Computed that all k in this range have expected exception count < 1 in the interval (284, k²]. Verified by exhaustive enumeration that zero n in any such interval satisfy the digit-domination conditions for all primes p ≤ k.\n\nKey results:\n- Trivial cases k=1,2 handled directly\n- For k ∈ {3,...,16}, we have k² ≤ 256 < 284, so Case A applies immediately\n- For k ∈ {17,...,28}, exhaustive verification confirms no exceptions in (284, k²]\n- The 14 known exceptions all satisfy n ≤ 284, with (284,28) achieving the boundary exactly\n\nDependencies: proofs/large-n-divisibility.md (under review), proofs/kummer-theorem.md (verified), proofs/large-prime-criterion.md (verified)"
}
```

## Final Result

The proof is complete. Let me provide the final task completion:

```json
{
  "status": "completed",
  "summary": "Proved that for k ≤ 28 and n > 284, there exists a prime p ≤ max(n/k, k) dividing C(n,k). Published to proofs/bound-n-for-small-k.md",
  "details": "Confidence: High. The proof splits into two cases:\n\n**Case A (n > k²):** References proofs/large-n-divisibility.md which establishes that primes in (k, n/k] force divisibility via the Interval Divisibility Lemma.\n\n**Case B (284 < n ≤ k²):** For k ∈ {17,...,28}, uses explicit CRT density analysis. Computed that all k in this range have expected exception count < 1 in the interval (284, k²]. Verified by exhaustive enumeration that zero n in any such interval satisfy the digit-domination conditions for all primes p ≤ k.\n\nKey results:\n- Trivial cases k=1,2 handled directly\n- For k ∈ {3,...,16}, we have k² ≤ 256 < 284, so Case A applies immediately\n- For k ∈ {17,...,28}, exhaustive verification confirms no exceptions in (284, k²]\n- The 14 known exceptions all satisfy n ≤ 284, with (284,28) achieving the boundary exactly\n\nDependencies: proofs/large-n-divisibility.md (under review), proofs/kummer-theorem.md (verified), proofs/large-prime-criterion.md (verified)"
}
```

End Time: 2026-02-08T09:47:45.978Z
