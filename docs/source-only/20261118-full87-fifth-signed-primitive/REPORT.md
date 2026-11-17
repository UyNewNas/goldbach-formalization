# P1.4 — actual fixed fifth signed primitive/density decomposition (candidate)

Baseline: **ad81b2bbe0d6c534bc7efd4eaac3262c62b7a48e** on `chatgpt/p1-full87-sixth-root-receiver-20261118`. Independent branch `chatgpt/p1-full87-fifth-signed-primitive-20261118-0213`. The prior packet's full receiver co-prime quotient invoice is retained unchanged. New source: `P4AOriginalFull87FifthSignedPrimitive.lean`.

## Concrete new manuscript-side mathematical work

The existing exact full-modulus arithmetic primitives give, for **every** `d : ℕ`, including d=0 with Lean total-division semantics,

```
receiverTest N d
 = primeMass N * densityTest d
   + primitiveError N d
   - modulusPrimeTerm N d
   - chenCentrePrimeAPCount N N d.
```

Here the centre correction removes actual prime divisors of N in the same residue class; the modulus-prime correction is not dropped. `primitiveError N d` is the **actual** inclusive prime AP count minus the **exact** coprime mean, not an independent estimated sieve bound.

The new proof traverses the original high-q PLUS-beta attachment at the complete `d = a * (p :: selectedAfter).prod`, then the ordered sixth `remainingAfter` List, and finally the RAW-only / LICENSED-only signed event cases. It proves linearity of these actual finite kernels in the arithmetic test.

**Crucial protection against a hidden source change:** `actualFixedSignedFifthTail` constructs the actual fourth parents and fifth/sixth events **only once**, using `actualFifthSixthWithoutBoth ... (receiverTest N)`. When evaluating density/primitive/modulus/centre contributions, the event population, signed fifth admission, selected/remaining history, occurrence multiplicities and original PLUS beta are held **fixed**. The external arithmetic test is changed inside the common sixth kernel only. No density-generated policy, altered parent, independent sieve inequality, generic tail-smallness structure field, or arbitrary mask is introduced.

The resulting local theorem is an **exact signed equality** for the SAME actual stopped difference:

```
rawStopped(receiverTest) - licensedStopped(receiverTest)
 = primeMass * T(densityTest)
   + T(primitiveError)
   - T(modulusPrimeTerm)
   - T(chenCentrePrimeAPCount).
```

`T` is the fixed **actual** filtered fifth/sixth event population, not a replacement source. Taking absolutes only **after** this signed equality gives

```
|stoppedDelta - primeMass * T(densityTest)|
 <= |T(primitiveError)| + |T(modulusPrimeTerm)| + |T(centrePrime)|.
```

This specifically identifies three distinct, still-unpaid **manuscript-side** error amounts. It avoids the earlier gross coprime-quotient invoice's premature triangle bound but does **not** assert that signed cancellation actually saves a positive fraction of H_N.

## Checks performed

- Connector successfully created the isolated branch from the exact baseline and wrote the source. The complete source is >300 lines and its final blob is recorded in REGISTRY.
- Static source readback and forbidden-proof-escape scan: no `axiom`, `sorry`, `admit`, `native_decide`, or `unsafe` tokens.
- Separate finite Python verification of the literal receiver/AP/exact coprime mean/modulus-prime/centre correction equation for **N=1..200** and **d=0..N+5**: **21,300** pairs, no numerical failures. It only tests finite arithmetic, not the event producer, Lean elaboration, or the saved87 archive.
- Local environment: `lean --version`, `lake --version`, `elan --version` each returned **127** (not found). The fixed local Lean/mathlib/native dependency closure and source-only import staging are unavailable. **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. The new use of `simp`, recursion and linearity has not been kernel checked and may still contain type/tactic errors.
- No local Lean build, kernel replay, transitive axiom audit, independent review, or original87 certificate replay; no new CI, Codex, user machine, parameter change or master/main write.

## Accurate remaining boundary

No claim that `T(primitiveError)`, `T(modulusPrimeTerm)`, or `T(centrePrime)` is `o(H_N)`; no fixed full-q `theta<1` or smooth-singleton PP license, and no identification of `T(densityTest)` with the original ordinary residual integral. The three prior physical outside/producer/licensed-outside invoices are **distinct from these** and are not silently paid or counted twice. Both independent compiler and density reserves remain unpaid. Unfiltered sixth BOTH, RAW eighth, actualParent, saved87 certification, rank9, changed/tagged and final same-rho bridge remain yellow.

Frozen manuscript: `chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`, c=`49044063/25000000`, K=`8452171/1250000`, unchanged.

Next real derivation: on the **same frozen event population and complete a*b moduli**, obtain a quantitative bound for the signed `T(primitiveError)` (or identify its exact unlicensed PP input), separately control modulus/centre corrections, prove density-to-residual-integral and retain all physical invoices. Once the exact pinned environment is available, first typecheck the source and repair errors before any COMPILED credit.
