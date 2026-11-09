# P1.4 — original87 quantitative cap-gap to source integral (SOURCE_ONLY)

## Recovery
- Exact verified predecessor: `8d6d3703f0e388a72349c927a2739771be2c1c2c` on `chatgpt/p1-full87-kernel-positive-source-20261109`.
- Isolated branch: `chatgpt/p1-full87-quantitative-gap-integral-20261109`; source commit `b623b814aea12d14f911130dc3c2f0d122898aaf`, source Git blob `881afdf6473024c6e8f53cf6a8431a77651da844`.
- Read previous REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and the entire corrected kernel-positivity Lean source; earlier archive-cell-loss handoff and registry; original source dictionary and kernel-control blobs, original 20261105 eighth-arithmetic report, real Chen prime-source supplier, fixed lake manifest and toolchain. Root, docs, source-only and predecessor-packet AGENTS.md checks returned 404.
- Pinned manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, verified Git blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Read lines 397–505 including (current-eighth-saving), the coefficient/reserve normalization and the strict source cutoff. No manuscript switch.

## Actual new proof-body content
New `P4AOriginalFull87QuantitativeGapIntegral.lean` (155 lines). It uses the same ORIGINAL `Source`, `comparison`, `newCap`, `kernel` and `sourceSet` for all 87 original `Cell` constructors. It does not introduce a surrogate parent, mask or new witness.

Let `S=total t`, `P=comparison c t`, `M=newCap c t`, `J=product t`, and `mu` the ORIGINAL first-coordinate upper cap. Original source semantics imply `0<P-S<M-S<3*t₇`, `0<tᵢ≤mu`, `0<J≤mu^8` and `0<M-P`. Consequently
```
0 < D := (P-S)(M-S)J ≤ 9 * mu^10,
4*(M-P)/(9*mu^10) ≤ kernel c t = 4*(M-P)/D.
```
The denominator bound, not merely positivity, is the actual new mathematical step. There is no signed-saving monotonicity claim.

The source-cap gap `M-P` is continuous and bounded by `3*mu` on the original finite-measure source. The Lean candidate therefore also supplies an `IntegrableOn` proof with no new integrability hypothesis. By `setIntegral_mono_on`, the candidate derives the source integral comparison:
```
∫ t in sourceSet c, (4/(9*mu^10)) * (newCap c t - comparison c t)
  ≤ ∫ t in sourceSet c, kernel c t
```
for every original Cell. This is an exact real-source reduction of a prospective quantitative residual-integral lower estimate to an original cap-gap integral. It is not an original numerical endpoint certification; no lower bound for that gap integral is established here.

## Real checks and limits
- Remote readback: Lean blob `881afdf6473024c6e8f53cf6a8431a77651da844`; 155 lines; token scan found no sorry/admit/axiom/native_decide/unsafe; simple delimiter scan found no unmatched delimiters. Neither scan is Lean parsing.
- Executed 4,000 independent exact Fraction *synthetic* denominator comparisons under abstract original-source consequences `0<tᵢ<mu, 0<P-S<M-S<3t₇`: 4,000/4,000 pass. NOT a replay of 87 saved originals, and not a Lean check.
- Actual local environment: `lean`, `lake`, `elan` not found (127). No local pinned mathlib/native packages. No elaboration, kernel replay, transitive-axiom check or independent review.
- Validation: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. Do not use a source-only proof body as an accepted formal theorem.
- Source-only imports require correct logical staging into `ImbalancedChen/` with earlier source-only dependencies before a matching Lean build. No CI dispatch, Codex, new resource, user workstation, main/master edit, merge, forced push or toolchain change.

## Remaining exact manuscript-internal obligations
1. Authenticate original saved87 simplex/quadrature witness bytes and prove that each archived selected rational endpoint is a lower bound for the intended ORIGINAL same-source integral, not merely an earlier finite ledger value. The pinned compact manifest contains hashes for original *.witness.json but explicitly does not assert those bytes are present; the inspected pinned verification/data tree does not contain those files.
2. **Quantify** the original cap-gap integral on each source and, crucially, relate the ideal comparison `P` to the actual N-dependent `actualParent` with identical fourth/fifth history. This is necessary before applying the result to actual physical signed occurrences.
3. Connect the full-q original Rosser beta, retained lists and multiplicity-preserving arithmetic `states` to the same parameterized ordinary continuation and original density integral. Separate primitive discrepancy, modulus-prime and centre-prime corrections; one physical W_N and legitimate PP X; same H_N; raw/finite/filtered/rank9/changed/tagged; distinct compiler and density reserves.
4. Stage fixed imports, compile, replay finite certificates, audit transitive axioms and seek independent review.

External manuscript §4 PP remains REGISTERED_NOT_PROVED / NOT_CALLED. Fixed c=49044063/25000000 and K=8452171/1250000. P1.4 remains YELLOW.
