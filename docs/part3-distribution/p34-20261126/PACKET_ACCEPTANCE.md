# P3.4 literal packet and actual cusp acceptance — 2026-11-26

## Accepted source and scope

P3 cloud task `e4814f72e2ff4589bc57b69f5df2e4fc` completed with exit 0 on the exact clean GitHub source **`145be87ff0a88914b607baa2a330bc88105a08d6`**. Its tree is `9effc51d3ce49d4aa29c9b2aa811d1f18373ee03`. The local reviewed commit `7d9d146c100a64dc4c7ce0abec014314e5be37e4` has the same tree.

All **70 stages** passed: 13 strict module compilations, 13 bundled `leanchecker` replays, 14 parsed dependency inventories, fixed dependency and tool checks, import-scope regressions, complete declaration/axiom auditing, and the final clean-tree check. The 13-module inventory contains **167 constants**, including **124 theorem constants**. These totals include reused cusp results and private/generated declarations; they are not counts of newly proved manuscript theorems. The transitive axiom union is exactly `Classical.choice`, `Quot.sound`, and `propext`.

The checked modules, in dependency order, are:

1. `Part3FourierModeIndex`
2. `Part3CoprimePacketCore`
3. `Part3CuspPhaseCore`
4. `Part3Gamma0ActualCusps`
5. `Part3CuspScalingMatrices`
6. `Part3ActualCuspWidthNormalization`
7. `Part3CuspTranslationFourierPhase`
8. `Part3ActualCuspFourierSection`
9. `Part3SignedCuspFourierSection`
10. `Part3CoprimePacketCoefficients`
11. `Part3ActualCuspScalingSourceOnly`
12. `Part3ActualCuspPacketPairing`
13. `Part3OldformCuspPhase`

The strict flags remain `-t0 -j1 -M6000 -DwarningAsError=true`. Lean is the frozen `4.33.0-rc1` toolchain, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`; Mathlib is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. All eleven package checkouts match their immutable manifest pins and were clean. Actual resolved project imports must belong to the previously rebuilt portion of this scope. This receipt does not claim a fresh replay of the entire external Mathlib closure.

## What this closes

The original `CoprimePacket` structure, transformed coefficient, coprimality gate and beta are unchanged. The existing signed coefficient and mode packet identities retain both physical Fourier phases, at coordinates `k 2 / 64` and `k 3 / 64`, including the coprimality-false zero branch. Their finite norm identities and the genuine old/new cusp-section pairing now have a small independently checked import closure.

The manuscript's scalar phase cancellation is checked for both signs:

\[
e(-\eta A\nu n/z)\,e(\eta n(A\nu-1)/z)=e(-\eta n/z).
\]

The final phase theorem pairs that product with the existing fixed-height Haar Fourier coefficient of an actual Gamma0-invariant function. It preserves a positive level, positive height, the invariance predicate and the signed integer frequency.

Fifteen original public declarations were moved with unchanged signatures. Fourteen complete declaration bodies are byte-identical; the moved `norm_e` proof computes the norm directly to avoid the original large reconstruction import. The two staged cusp modules retain their original public statements. Compiler repairs and exact donor hashes are recorded in `DECLARATION_MOVES.json` and `PACKET_IMPLEMENTATION.md`.

The frozen manuscript reference is `UyNewNas/chen-imbalanced-semiprimes` commit `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`, `paper/release-20261106/en/analytic-appendix.tex`, Appendix B, the cusp/packet paragraphs around lines 951–982.

## A failed candidate was retained and repaired

Published candidate `88aba6a6d0276bd25e893958252b11fe07a1f05f` (local tree-equivalent commit `40a5b28303c652450da65e740fd5a4e70c902391`) passed its 13 strict compilations and 13 individual kernel replays but failed the complete declaration audit. It receives no acceptance credit.

Three identical generated declaration names had been serialized by independent consumer modules: `cuspPhase.eq_1`, `oldFourierCoeff.congr_simp`, and `newFourierCoeff.congr_simp`. The audit correctly refused to identify those serialized inventories with the environment's single-owner map. The repair materializes the unfolding equation in the shared definition module using a local attribute, and uses explicit rewrites in the pairing proof to avoid generating duplicate congruence lemmas. Neither the full inventory comparison nor the transitive-axiom gate was weakened.

`failed-40a5b283-inventory.json.gz` preserves the diagnostic source, both complete types and proof values of each duplicate, owner indices, all 13 inventories, and the original object hashes. `packet-failed-cloud-report.json`, `packet-failed-cloud-task.json`, and `packet-failed-axioms.log` preserve the independent cloud failure. The fresh repaired run passed every gate. `PACKET_INITIAL_REVIEW.md` and `PACKET_FIX_REVIEW.md` retain both independent review outcomes.

## Reproduction and evidence

At the exact accepted source, with the frozen package checkouts and toolchain available:

```sh
python3 verification/verify_p34_cusp_packet.py \
  --expected-head 145be87ff0a88914b607baa2a330bc88105a08d6 \
  --output-dir .lake/p34-packet-cloud-acceptance-attempt2
```

The durable evidence is `packet-cloud-report.json`, `packet-cloud-task.json`, and `packet-cloud-verification.zip`. The archive contains all 73 original output files and has SHA-256 `57a8c24f8a4bfa7f2d76d5acdde07660ff3117b967be900abdcb6d67efde9a00`. `packet-cloud-archive-manifest.json` binds each archived file. `PACKET_REUSE_AT_PRIMARY_SOURCE.json` checks all 22 source/configuration/verification bindings against the subsequent primary source without recompiling this unchanged scope.

## Remaining P3.4 obligations

This receipt closes the literal packet, mode identities, fixed-height cusp pairing and scalar phase product. It does not identify fixed-height Fourier coefficients with the height-independent spectral coefficient `R(n)`, prove an oldform dilation law, supply the missing original `FixedBlock`/`OriginalData` definitions, or close the four archived original row consumers. In particular, coefficients at frequencies `A*nu*n` and `n` have different radial factors; the scalar cancellation does not justify cancelling those factors.

The 1106 manuscript's external ABL, Frobenius, spectral-gap and trace inputs remain explicit boundaries. P3.5's already accepted continuous Cauchy/exhaustion work is reused rather than reimplemented. **P3.4 as a whole is not marked complete by this receipt.**
