# Historical two-long rough comparison: finite source reuse

**Source-only; not elaborated, not kernel checked, and not a completed rough
invoice.** This packet preserves the existing generic finite E3 proof blocks
and records the exact historical assembly. No new terminal theorem was written
after the source-availability check found a missing direct core provider.

## Preserved finite interface

`EXTRACTION_BINDING.json` binds six unchanged source intervals, containing
36 declarations, to three shared owners in `support/`. Their original namespaces,
statements and proof bytes are preserved. Each old provider has an exact
complementary version under `postimages/`, consisting only of the interval
deletion and a new import. These are future provider selections, not additional
active owners to compile together with the original archived providers.

| Shared source | Original finite declarations supplied |
| --- | --- |
| `P1HistoricalTwoLongBrunSubstitutionData` | Divisor indicator and change of variable, exact residue-kernel identity, literal Brun coefficient/polynomial, and `smoothBrunTupleCore_eq_expansion` |
| `P1HistoricalTwoLongExactPairMeanData` | `pairMean`, its nonunit-sensitive factorization, the fixed logarithmic density bound, and the original per-modulus E1 norm bound |
| `P1HistoricalTwoLongFiniteRoughData` | The original `gapPairMean_point`, positive rough-pair comparison, literal `roughOneSlot` dictionary, and finite envelope-polynomial P2 bound |

The six generic Brun-support declarations remain owned solely by
`../p1-historical-two-long-p2/support/Part3TwoLongBrunSupport.lean`.
This packet imports that owner and does not copy those declarations.

The selected copies of `P4BOriginalCoprimeSmoothE1` and
`P4BOriginalPositiveLongEnvelope` under `selected-api/` only change one import
each. Their entire declaration bodies are original bytes. The changes avoid
the unrelated old P4 two-mother provider at those two import boundaries; they
do not establish complete transitive source availability.

## What the finite proof must preserve

For the historical physical channel, use exactly

```text
Q = remainingModuli B N (trueDDeltaSupport old fresh N cap w z)
rho q = (trueDDeltaRho old fresh N cap w z L q : Complex)
alpha m = shortSequence bs Z y xi rs m
m in shortSupport bs
```

The upper polynomial expands with the original two Brun supports
`brunSupport Z (2*j+1)` and the original signed `brunPairCoefficient`.
Only the upper/upper case `b₁ = false`, `b₂ = false` is compared with the
rough pair. Its exact expansion is the adjacent packet's
`historicalRowCore ... j false false ...`; no equality between rough masks
and upper polynomials is asserted.

The two positive gap terms have flags `(true,false)` and `(false,true)`.
They are evaluated at the constructed positive Schwartz envelopes, with
coefficient `norm (alpha m)`. This does not replace the signed historical
coefficient on the left. Norms enter only when summing the finite comparison.

The complex long profiles retain all three labels:

```text
leftMellin  delta U t1 label log1 = profile (decide (label = 1)) log1 ...
rightMellin delta V t2 label log2 = profile (decide (label = 2)) log2 ...
```

Thus label `0` is upper/upper, label `1` has the left endpoint gap, and
label `2` has the right endpoint gap. These transition-profile labels are
separate from the two Brun gap flags. The original log flags and Mellin
frequencies remain in every profile.

## Exact positive gap and twice-mean step

The existing pointwise `actual_pair_E3` proves

\[
\left|\Delta(\alpha f g\,r_1r_2)
       -\Delta(\alpha f g\,U_1U_2)\right|
\le
\left|\Delta(|\alpha|EJ\,G_1U_2)
       +\Delta(|\alpha|EJ\,U_1G_2)\right|
+2|\alpha|\,\operatorname{gapPairMean}(E,J).
\]

Here `G` is the positive upper-minus-lower Brun polynomial and `r` is the
actual rough indicator. The proof uses the original sandwich and bounds
the absolute count-minus-mean expression through positive count-plus-mean.
The mean on the right retains exactly one totient inverse and the full
test `Coprime (m*u*v) q`. It is not the product of two independently
normalized means. `pairMean_factor` retains the zero branch when
`m` is not coprime to `q`.

`gap_density_B2` supplies the actual factorial gap

\[
\varepsilon(j,Z)=
\frac{\bigl(\sum_{p\le Z}p^{-1}\bigr)^{2j+1}}{(2j+1)!}
=\texttt{brunEpsilon j (smallPrimes Z)}.
\]

The unchanged `gapPairMean_point` also requires `epsilon ≤ 1` and
`Z^(2*j+1) ≤ x`, with `x ≥ 1`. The former is **not true for arbitrary
`j,Z`**. It is a concrete scalar gate for an intermediate finite payment;
the actual half-order/cutoff choice must later obtain it from the existing
small-gap supplier. This packet neither assumes the desired rough error
nor turns an exact mean estimate into a premise of the final theorem.

## Remaining finite assembly, once the core source is accessible

The exact recipe is:

1. Apply `actual_pair_E3` for every `q in Q` and `m in shortSupport bs`.
   Multiply by `norm (rho q)` only in the norm inequality. Sum both positive
   cross terms and retain the factor `2` on the exact mean.
2. Apply original `polynomial_P2` to each cross term. The adjacent historical
   P2 packet supplies positivity, squarefreeness, `Coprime N q`, the unit
   norm bound, and its already derived `historical_modulus_moment`.
3. Specialize the existing finite `actual_tau_moment` argument to `Q,rho`
   for orders `0,1,2`, using the same canonical fourth-divisor moment.
   This pays the original per-modulus `gapPairMean_point` after E1 is
   applied, not a product of two aggregate signed E1 errors.
4. Use existing `shortSequence_mass` on the actual signed ordered
   pushforward. Invoke `smoothBrunTupleCore_eq_expansion` to identify
   the upper/upper term with `historicalRowCore`, and then reuse the
   adjacent P2 bound for that core.
5. Take `D = floor (N^(599/1000))`; `historical_modulus_floor` removes the
   level premise from the physical-channel version.

Writing `mu = sum_m norm (alpha m)`, `Y = Z^(2*j+1)`,
`R(D) = (4*(1+log(max 1 D)))^16`, and `Lx = densityLog x`, the resulting
finite comparison budget should be

\[
2\,\operatorname{p2Price}(E,J)\,Y^2\mu\,
  (D\sqrt D+1)R(D)
+2\mu\,\operatorname{meanPrice}(\delta,U)
       \operatorname{meanPrice}(\delta,V)R(D)
\left(2UV\varepsilon L_x+2L_x(U+V)Y+2Y^2\right).
\]

This is a proof recipe, not a Lean theorem or a claim of compilation.

## Concrete source stop

The directly required provider `ImbalancedChen.Part3TwoLongFixedMRectangularCore`
has no path in the current canonical/source-only filename index. The exact
existing import chain is

```text
P1HistoricalTwoLongFiniteRoughData
P4BOriginalPositiveLongEnvelope
Part3TwoLongQuantitativeTransitionProfiles
Part3TwoLongLiteralMellinModes
Part3TwoLongFixedMRectangularCore
```

The last importer is the unchanged
`docs/source-only/20261028-resume-30/pp_twolong/Part3TwoLongLiteralMellinModes.lean`,
SHA256 `2fce2a53febab40154a9e136882da2c334cbefb65fa662b7369fa7201f750e26`.
The missing provider supplies the exact `fixedMCore` interface used by the
substitution and squarefree P2 routes. Its absence is a source/access problem;
no conclusion about a manuscript mathematical gap follows from it.

The importer's existing `pp_twolong/REGISTRY.json`, entry `imports[1]`,
provides an exact recovery locator:

```text
goldbach-proof-continuation\.lake\proof-continuation\source-reviews\drafts\20261028-PrimeProducts-PhaseB5-TwoLong-Rectangular\Part3TwoLongFixedMRectangularCore.lean
SHA256 2be2789f712144fc7411849340caafe2c5caa2dc6de9ad96125590a9e9374b8b
```

That record marks the dependency as source-only and gives no Git blob or
normal/kernel/full-owned acceptance. The parent has now completed the bounded
P1 read-only metadata check in `job_e86dac8253cd430cabc4c4fac9c7b62e`
(`succeeded`). All three exact paths below were reported absent:

```text
/workspace/blue-member-build/ImbalancedChen/Part3TwoLongFixedMRectangularCore.lean
/workspace/goldbach-formalization/ImbalancedChen/Part3TwoLongFixedMRectangularCore.lean
/workspace/goldbach-formalization/goldbach-proof-continuation/.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-PhaseB5-TwoLong-Rectangular/Part3TwoLongFixedMRectangularCore.lean
```

No file hash could be read at those three paths. The expected source SHA256
remains the historical registry value above. This is a bounded observation
about those paths only; it does not establish absence throughout P1, other
members, archives or repositories. No source was reconstructed and no Lean
or kernel check was run for this packet. This route stops here; no further
fixed-M search or proof replacement is part of the task.

The full historical Mellin-profile provider also imports the old normalized
HB/Fourier graph and reaches previously known absent sources. Its generic
profile/core prefix is a plausible further source-layering boundary, but that
would not supply the missing fixed-M core. No old missing source was rebuilt,
no new search for those historical missing files was undertaken, and no
arithmetic proof was substituted for the absent core.

The fixed manuscript is `UyNewNas/chen-imbalanced-semiprimes`
at `a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en/coefficient-appendix.tex`, SHA256
`267af54481f344e806d4cb3ad602aa7f32020b930845e2aa152b7daaa2f9a440`.
Its positive rough-pair comparison and `coef:two-rough-error` justify the
finite recipe. Sharp strips, original singleton Fourier reconstruction
(whose fixed-order budget has exponent 72), outer graph/HB counting,
actual selector attachment and eventual logarithmic payment remain outside
this packet. The P4 two-mother terminal is not transferred.

## Follow-up: exact Core source metadata in P2 and P3

The additional fixed-basename query is recorded in `EXACT_CORE_P2_P3_METADATA.json`.
It concerns only `Part3TwoLongFixedMRectangularCore.lean`, whose expected source
SHA-256 remains `2be2789f712144fc7411849340caafe2c5caa2dc6de9ad96125590a9e9374b8b`.
The earlier nine-owner missing-source searches were not repeated.

P3 task `f15a2a5b1f744f3a8bdcdfbcb0df90bb` finished with exit 0 in 4.088 seconds;
its 494-byte output was read to EOF without truncation. The bounded `/workspace`
source-tree search found zero exact-basename paths and zero metadata errors.
Git objects, build products, logs, private evidence, toolchain caches and symlink
directories were excluded, so this is not a claim of global absence.

P2 reported a full queue (one running and eight waiting, with a waiting limit of
eight). No P2 query was submitted or retried; availability there remains UNKNOWN.
No source body, private archive, owned types or raw logs were exported. No Lean
or Lake command was run, and no project file or queue entry was modified. The
fixed Core source remains unavailable to this adoption package; no replacement
proof was reconstructed and no new formal acceptance is claimed.
