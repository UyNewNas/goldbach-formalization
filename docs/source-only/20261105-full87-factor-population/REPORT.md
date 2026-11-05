# P1.4 run 3 — full-modulus factor-population payment candidate

2026-11-05. Baseline `3946b373c5191039c6e6541e2b533b756e18e010`.
**SOURCE ONLY / UNCOMPILED / UNEVALUATED / ZERO FORMAL CREDIT.**

## Concrete mathematical increment

The previous packet charged the actual changed original87 signed source for the modulus-prime exception by `pi_N * V_changed(1/phi)`. This loses nearly a factor `pi_N / omega(d)` on individual nonzero full moduli. The new Lean candidate works with the EXISTING original full modulus `d=a*selectedPrefix.prod`, not an invented rough-only modulus.

For `d != 0` it proves the exact finite set identity

```
{p <= N : prime p and p | d} =
  (Nat.primeFactors d).filter (p <= N).
```

Thus for `0<d<=N` its cardinality is exactly `omega(d)`, the number of DISTINCT prime factors. In general define a *natural-number* cap:

```
cap_N(d) = if d=0 then pi_N else min(pi_N, omega(d)).
g(d) = 1/phi(d).
```

The unmodified correction `modulusPrimeTerm(N,d)` satisfies
`abs(modulusPrimeTerm(N,d)) <= cap_N(d)*g(d) <= pi_N*g(d)`.
The first inequality remains valid for `d=0` (where primeFactors(0) is empty but all primes divide 0), as well as `d=1`, prime powers, `d>N`, and `N<2`. At `d=0`, `g(0)=0` in the totalized arithmetic. No full physical support nonzero assumption is silently introduced.

The new candidate also proves MONOTONICITY IN THE NONNEGATIVE ENVELOPE TEST `H` of:
- the full-modulus sign-selected absolute small-Rosser attachment;
- the absolute signed continuation recursion with unchanged branching;
- each actual old and new ordinary continuation;
- the SAME changedStates occurrence list, preserving each occurrence.

This is NOT monotonicity of the signed saving as the sieve level changes. Both actual own-sixth `actualParent` and saved eighth `finiteCap` are exactly as before, including fifth fallback. The new envelope is provably no worse than the preceding `pi_N*V_changed(g)` envelope over all changed owners and histories.

Let `F_N(d)=cap_N(d)*g(d)`, and `V_changed` denote the existing absolute variation over the real changed owner lists. The resulting finite same-rho ledger is:

```
|gain(receiverTest_N) - pi_N*gain(g)|
 <= changedAbsBudget(primitiveError_N)
  + V_changed(F_N)
  + omega_N * V_changed(1).
```

Here `omega_N` means `chenPrimeDivisorCount N N`, and all old/new signed coefficients and per-leaf beta attachments still occur on the same full-q source. This substitutes only a smaller nonnegative modulus-prime envelope; it never redefines the actual signed correction or drops a physical coefficient term.

## Limits and genuine remaining gap

This is a concrete strengthening of a finite bound, NOT a proof that `V_changed(F_N)` is negligible after normalization. For actual full moduli, an effective uniform bound on `omega(d)`, support size and beta-weighted variation is still required. The exact ordinary continuation to residual-integral asymptotic on the same source, target-prime deletion, signed sixth loss, complete saved numerical geometry/coverage, two separate reserves and final same-rho assembly remain unpaid.

No manuscript constants, owner/trim priorities, old/new policy, source prefix, physical full modulus, external input, upstream file, workflow, or toolchain pin changed. No numerical box archive replay, PNT/Mertens/BV, or remote CI.

## Evidence

- `audit_factor_population.py` was executed in a local Python 3.13 environment: **16,000** exact pointwise and totalized 0/1 boundary cases, plus **2,500** independent finite signed-envelope cases using `Fraction`. These are synthetic sanity tests, not Lean proof validation or an original87 replay.
- The newly created Lean blob was retrieved and checked for 18 declarations, balanced simple delimiters and absent forbidden proof-escape identifiers. This lexical check is not a Lean parser or elaborator.
- The actual Lean `Nat.mem_primeFactors` contract was read from pinned mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, module `Mathlib/Data/Nat/PrimeFin.lean` (Apache-2.0). It asserts `p ∈ n.primeFactors ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0`. This is an existing verified-library interface, not a new manuscript theorem or new analytic input.
- No Lean executable, complete dependency/fixture closure, kernel replay, transitive axiom inspection or independent reviewer was used. The math proof bodies remain `UNEVALUATED`, not `COMPILED`.

## Next exact action

1. Verify how the complete physical modulus `a * selectedPrefix.prod` is bounded on the actual `changedStates` (not only in synthetic examples); use that to replace the per-modulus factor cap with a uniform/payload-specific `omega(d)` and estimate the beta-weighted `V_changed(F_N)` relative to the SAME density normalization.
2. If the bound remains too coarse, prioritize the signed ordinary continuation → residual-integral bridge and actual target-prime deletion without adding a surrogate external assumption.
3. Submit leaf and dependency-closure build requests only through the project's existing accepted validation gate; this source packet is deliberately `[skip ci]`.
