# timtam Task: Formalize crt_small_prime_divides in KGe29.lean (erdos1094-lth)

Role: formalize
Agent: formalize (anthropic/claude-opus-4-6:high)
Start Time: 2026-02-08T14:49:36.556Z

## Agent Interaction





> **Thinking:**
> Let me start by understanding the task. I need to close the `sorry` in `Erdos/KGe29.lean` at line 66 for `crt_small_prime_divides`. Let me first read the relevant files to understand the context.


```bash
$ cd /home/jarred/code/erdos-1094 && tm update erdos1094-lth --status "Reading task context: KGe29.lean, NL proof, and dependencies"
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**


> **Thinking:**
> Let me understand the task. The theorem `crt_small_prime_divides` says: for k ≥ 29 and 2k ≤ n ≤ k², there exists a prime p ≤ 29 with p | C(n,k).
> 
> The NL proof establishes this via exhaustive CRT verification for k ∈ [29, 10000]. The theorem in the Lean file is stated for ALL k ≥ 29, but the NL proof only covers k ∈ [29, 10000].
> 
> Wait, let me re-read. The NL proof says the rigorous part covers k ∈ [29, 10000]. 
> 
> But the theorem in Lean is for all k ≥ 29. This is a gap—the NL proof's density argument for large k is heuristic, not rigorous. However, the task suggests using either native_decide for finite verification if tractable, or a structural argument leveraging the Kummer criterion already available in Erdos/Kummer.lean. The key is figuring out whether I can extend the verification computationally or if I need to rely on existing structural results.
> 
> The issue is that native_decide won't work on an infinite range, so I'd need to either verify a finite subset and leave the rest as sorry, formalize just the finite part, or acknowledge that the NL proof doesn't actually cover the full statement. Looking at the NL proof more carefully, it provides rigorous results for k ∈ [29, 10000], but the asymptotic argument beyond that isn't formalized. So I'm deciding between a partial computational verification, a purely structural approach, or escalating the mismatch between what the NL proof covers and what the Lean theorem claims. δ_k × (k²−2k) < 1 for all k beyond some point. If we could make this rigorous... but the NL proof explicitly says it's not rigorous.
> 
> Actually, wait. Let me re-read the Lean theorem. It says the statement requires proving that for k ≥ 29 and n in the range [2k, k²], there exists a prime p ≤ 29 dividing C(n,k). The approach with `native_decide` would need to express this as decidable, but since k is unbounded, we can't directly decide it.
> 
> Though maybe there's a reduction here. For each k, the CRT modulus M_k exceeds k², so the interval [2k, k²] fits in one period, and we could enumerate the "good residues" where digit-domination holds for all primes up to 29. The real obstacle is that k ranges over infinitely many values.
> 
> Let me approach this structurally instead. For sufficiently large k, maybe there's a purely structural argument—the NL proof in Section 7.4 sketches an asymptotic argument based on Stewart (1980) showing...
> 
> Now I need to look at what's actually available in the Lean project. Let me check the Kummer.lean file to see what tools and lemmas are already there.

Let me explore the project structure and dependencies more thoroughly.
🛠️ **Executing tool: read**

```bash
$ cd /home/jarred/code/erdos-1094 && find . -name "*.lean" | head -30
```

🛠️ **Executing tool: read**


> **Thinking:**
> Now let me understand the situation:
> 
> 1. The theorem `crt_small_prime_divides` claims: for k ≥ 29 and 2k ≤ n ≤ k², there exists a prime p ≤ 29 with p | C(n,k).
> 
> 2. The NL proof establishes this rigorously only for k ∈ [29, 10000].
> 
> 3. The theorem as stated is for ALL k ≥ 29.
> 
> There's a gap. But let me think about how to approach this pragmatically.
> 
> Options:
> 1. Use `native_decide` for a decidable version (but the range is unbounded)
> 
> 
> 2. Split into a finite part (decidable) and leave the rest as sorry
> 3. Try to find a structural argument
> 
> Actually, the key insight is that for each k, checking whether some n ∈ [2k, k²] avoids digit domination for all primes ≤ 29 is a finite computation. So I could use `native_decide` to handle k up to some bound K, then use sorry for k > K.
> 
> But the theorem requires this for ALL k ≥ 29. The real question is whether there's a purely structural argument that works universally. For large k, the density of numbers that digit-dominate k across all small primes becomes vanishingly small—the product ∏(p - d_i) over the digit constraints gives us very few candidates. Making this argument completely rigorous for every k ≥ 29 without computation is the challenge.
> 
> I'm wondering if `native_decide` could handle a finite range. The issue is that for each k, I'd need to check all n in [2k, k²], which grows quadratically—at k = 10000, that's roughly 10^8 values to verify. Computing binomial coefficients directly at that scale would be prohibitively expensive. But I don't actually need the binomial coefficients themselves; I can use the digit-domination criterion as the decision procedure instead.
> 
> For each n, I need to verify that there exists a prime p ≤ 29 where some digit of k exceeds the corresponding digit of n in base p—that's the condition for p dividing C(n,k) by Kummer's theorem. This is decidable for finite ranges, and the computational cost per k value is roughly O(k² × log(k) × 10), checking each n against the digit condition across all relevant primes.
> 
> The challenge is scale: for k up to 10000, I'd be looking at around 10^8 values of n per k, and across all k values that's roughly 3.3 × 10^11 pairs total—far too many to compute directly. Instead, I should use the Chinese Remainder Theorem approach: for each k, compute which residues modulo M_k = ∏ p^{L_p(k)} are valid, then check if any of those residues fall in the range [2k, k²].
> 
> Since M_k exceeds k², the interval fits within a single period of the modulus, so I only need to verify whether the valid residues actually land in that range. The density of valid residues is quite low, which makes this tractable even though the modulus itself is enormous.
> 
> The key insight is that the Chinese Remainder Theorem enumeration doesn't need to check all residues—it uses a filtering strategy. Starting with candidates from the base-2 and base-3 constraints gives around 36 possibilities for k = 29, then the remaining primes filter this down further. This staged approach keeps the computation efficient across different values of k.
> 
> However, running this verification in Lean for every k from 29 to 10000 using `native_decide` could still be prohibitively slow. I should consider whether `Decidable` instances could handle a reasonable subset of the range, or if I need to rethink the overall strategy. Looking at the statement itself, I have bounded quantifiers: for all n and k where k ≥ 29 and 2k ≤ n ≤ k².