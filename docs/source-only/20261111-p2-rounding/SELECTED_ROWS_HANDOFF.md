# P2 selected-row actual-integral bridge (2026-11-11, second round)

SOURCE ONLY; UNCOMPILED. Parent cc7da5cf6e78dfac313f8b66d7a302c009a2448c.
No CI or workflows, no user computer, no Lean/lake/Elan, no new dependencies.

## Freshness and duplicate-work checks
- Remote chatgpt/p2-integral-rounding-20261111 still at cc7da5c when work began; sealed codex/yellow-closure-20261110 still at 3a46b3f.
- Current pinned manuscript 9731290e8f53cffda44129906cde6a965eaa869b certificate JSON still blob 49499697cca96de5f7b779e95077874ce5f9d119. Reuse 186 strips /17572 rows, no sampling or checker rerun.
- Read existing P2PairedSemanticGainEnclosure: it already supplies full-mask actual semantic gain, half-baseline identities and actual fourfold integrability. Reuse, do not reproduce it.
- Existing P2SemanticGainSetIntegral supplies partialSemanticIntegral_eq_sum; existing restriction error supplies full-minus-retained identity. This round supplies their missing finite-row-selection/complement binding, not another implementation of Fubini or continuity.
- Reuse previous round's reviewed pointwise factor-ten upper comparison and the exact original row checker via row_actual_enclosure.
- P2 branch search found old chen-p2-certificates and this branch; P4 branch remains separately owned. Code search for rowUnion had no matches, a bounded check rather than proof of absence everywhere.
- No user-local source access, no full87/history, All22/tail, P3 or P5 route edits. Inaccessible unpublished work is not deemed absent.
- Toolchain/dependencies unchanged: Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, goldbach 09b97db5764ade1246bfb77206baa1b124760958.

## New source and statements
File: ImbalancedChen/Certificates/P2PairedSelectedRows.lean (129 lines).
All sets are genuine subsets of Fin 4 -> Real with product volume.
For any finite selection s of the adopted Row:
1. rowUnion(s) is measurable and contained in original region.
2. removed(rowUnion(s)) = rowUnion(complement s), proved from actual grid supports' disjointness, not ordinal labels.
3. Each actual semantic row integral lies between its checked L_r and 10 U_r. Original K/4 semantic weight and K/80 minorant are preserved.
4. Integral on rowUnion(s) lies between sum_s L_r and 10 sum_s U_r, by the existing genuine finite-union integral theorem.
5. Actual omitted semantic gain <= 10 sum_complement U_r.
6. Retained actual gain >= full certified L - 10 sum_complement U_r.
7. Therefore the adopted rounded floor survives if that finite omitted-row budget fits the previous exact rounding reserve.

No volume estimate is assumed in the new loss estimate. It replaces a coarse full-box density majorant with actual per-row certified integrals for this particular measurable finite-row deletion. It does not cover arbitrary partial-row cuts; the previous volume/collar interface still handles those.

The finite-budget premise in item7 is NOT discharged for a concrete deletion. No parent/history membership, saved-estimator identity, arithmetic injection, or terminal lower coefficient is inferred. Ten U is deliberately coarse; U alone bounds only the constant-minorant integral. Paired gains belong to the lower ledger and are not new All22 savings.

## Validation and limits
- Independent read-only review found no mathematical direction error or definite Lean naming/type error. Definitional unfolding may still need adjustment during elaboration.
- Eight exact-rational finite-subset model regressions passed (empty/full and all intermediate subsets), checking complement coverage, lower/upper directions and omitted-loss accounting. These are regression tests of algebra, NOT Lean theorem validation or a recheck of all 17572 numerical certificates.
- Source lexical guard passed (no sorry/admit/new axiom/native_decide/unsafe).
- Lean compilation, kernel replay, axiom audit: NOT RUN. Imported source candidates remain unaccepted here.
- No green/blue promotion or whole-P2 closure claim. Commit uses [skip ci].

## Next entry / compilation handoff
Compile the exact new module with the existing repair flow and fixed imports, not a P2-launched workflow. Gate its true dependencies through P2PairedRoundingLedger and the 3a46b3f Fubini/semantic chain.
Next substantive binding needs the actual finite row selection chosen by the owning historical route; instantiate its complement budget from existing endpoints, do not manufacture a history selection or repeat P1 work. Other adopted P2 integral obligations and P4 complete tails remain open.
