# P2.9: one ordinary-mass comparison for the complete selected profile

**SOURCE_ONLY_UNCOMPILED. Formal credit = 0; kernel credit = 0.**

The original all-depth selected physical-profile mass is bounded by the original all-depth marked `ordinaryBad` mass plus one absolute normalized error. The sharp base coefficient remains one. A single positive smoothing parameter is selected before the large-target threshold; that threshold is uniform over every allowed root parameter and original selected subfamily.

This is the ordinary finite marked-mass comparison. It is not a construction of the global smooth selected-history mask, an original `J` identification, a PP licence, or a W1/W2 result.

## Exact public theorem

The new module `ImbalancedChen.P2FiniteMarkedGamma5ActualProfileMassComparison` has one public theorem:

```lean
theorem actual_selected_profile_le_original_plus_epsilon
    (n : ℕ) (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    {ε : ℝ} (he : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧
      ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 12 →
        ∀ (B : (dep : Fin 431) → (p : ℕ) →
          Finset (LevelIndex N n .U4 t p dep.val)),
          norm N * allDepthSelectedProfileMass N n t h B ≤
            norm N *
              (∑ dep : Fin 431, ∑ p ∈ originalBand N .U4,
                ∑ l ∈ B dep p,
                  levelMark l *
                    ordinaryBad N (rootQ N n .U4 t p) (wordProduct l)) +
            ε
```

The normalization is the existing `P2FiniteMarkedGamma5RadialRoughMass.norm`, namely `log N / N`. The profile mass is the existing `allDepthSelectedProfileMass`. The right-hand base is displayed literally in the theorem and retains the original `originalBand`, `rootQ`, `LevelIndex`, `B dep p`, positive `levelMark` and `wordProduct`. No new mass function or `J` is introduced. The proof's local `originalMass` is merely an abbreviation for that displayed finite sum.

The `Fin 431` sum is the existing finite remaining-depth budget. It preserves every depth's original selected subfamily and does not assert that all generations form one simultaneous original arithmetic source.

## Quantifiers and proof

The order is:

1. Fix the original refinement parameter `n` satisfying `hn` and an arbitrary `ε>0`.
2. Use the existing all-depth radial payment at `ε/3` to select one `h∈(0,1/8]`.
3. Intersect the radial, noncoprime and proper-strip eventual estimates, together with `N≥2`.
4. Only then quantify over `t∈[0,1/12]` and every original family `B dep p`.

Thus the width precedes `N`, and the common threshold precedes the moving root parameter, every root prime and every selected position. No estimate is paid separately at each moving prime or history occurrence.

The calculation uses exactly the existing identity

```text
allDepthSelectedProfileMass
  = allDepthSelectedInnerMass + allDepthSelectedOuterMass.
```

The existing actual inner comparison bounds the inner term by the literal marked ordinaryBad sum, the original weighted noncoprime mass and the literal weighted proper-strip mass. Multiplication by the nonnegative normalization is justified by `N≥2`. The three supplied normalized errors are at most `ε/3` each, and their sum is at most `ε`.

No shape, root-cell, rank, depth-cardinality or product-fibre factor is multiplied into the ordinaryBad base. The fixed finite factors needed for the errors were already charged within their independent payment suppliers.

## Three reused payment suppliers

| Error | Existing supplier | Uniformity used |
| --- | --- | --- |
| Radial outer mass | `P2FiniteMarkedGamma5ActualRadialAggregate.absolute_all_depth_selected_outer_payment` | Chooses one `h` before `N`, then controls the complete `Fin 431` outer sum for all `t,B`. |
| Complete-product noncoprime mass | `P2FiniteMarkedGamma5ActualTargetExclusion.absolute_all_depth_selected_noncoprime_payment` | One eventual threshold works for all `0<h≤1/8`, `t` and complete original `B`. |
| Proper-strip mass | `P2FiniteMarkedGamma5ActualProperPayment.absolute_all_depth_cell_proper_payment` | One eventual threshold at fixed `n,hn` works for all allowed `t,h` and complete original `B`. |

The proper payment has a raw root-cell target. The exact `allDepthSelectedProperStripMass_eq_cells` dictionary rewrites the original weighted proper mass to that target, retaining every `dep,c,p,l,s` index. This is an equality of the same finite sum, not an estimate or a new quality assumption.

The whole-product noncoprime allowance may include tail factors allowed by the original sharp source. It remains a positive allowance; it is never asserted to equal the fresh-only exclusion condition. No tail-coprimality or distinctness restriction is added to the ordinaryBad base.

Empty old/tail blocks, repeated coordinates, the inclusive bad-square boundary and the inclusive inner cap are handled by the existing source, support and count dictionaries. This summary proof does not alter any of them.

## Exact source inputs

Direct imports:

- `P2FiniteMarkedGamma5ActualInnerComparison`, blob `028bf39f1ba608fc993411a34501397927340668`, unchanged 204-line actual marked comparison.
- `P2FiniteMarkedGamma5ActualProperPayment`, blob `2735523e5245e96614b43d3b047b14158460bdf3`, unchanged 258-line full proper-payment supplier.

Further exact reused sources include:

- ActualRadialAggregate: `93062adda7fdc87780a9c684c046652c567558d9`.
- ActualTargetExclusion: `510d3c6bb031ece73d15adb60da4121434f01700`.
- Shared ActualHistoryScale: `c2ef1b809fcc311813464dac4d71577075f3e7bb`.
- Original ordinaryBad owner: `dfd20b345e55f6a5820a6facf300d6c739cd867d`.

`REGISTRY.json` records exact UTF-8 hashes and the inherited source-owner/header selection. No supplier is edited or reproved by this file. No old native closure is rebuilt or automatically qualified.

## Manuscript scope and remaining work

The fixed manuscript is [1106 release, commit a988cba584d803ae2856a0de50efb582f4f3dd6a](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en).

The original common-query finite family appears in [sieve-appendix.tex 494–552](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L494-L552); the marked pair/cofactor expression in [634–660](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L634-L660); and the inclusive bad-region upper cost in [763–776](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L763-L776). [argument.tex 400–407](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex#L400-L407) requires the target limit to be taken after fixing the positive approximation. The theorem has that fixed-width-before-target order.

The source increment closes this ordinary-mass error combination using genuine supplied radial, arithmetic-exclusion and proper-wall bounds. It does not infer a radial payment from a null exponent-coordinate wall, and does not infer a total error from separate moving-position errors.

The actual globally admitted smooth selected-history function, the original `J` cost identification, the common-`rho` PP licence and the remaining original analytic receiver obligations are separate. The 29 H247/native-Wu native-binder compatibility conditions are not asserted to be necessary manuscript mainline obligations.

## Validation boundary

The complete 99-line source has passed independent static mathematical/interface review: one width, one eventual threshold, all three full-depth errors, exact proper-cell identity and base coefficient one were checked. Its exact source blob is read back and hashed.

There is no normal compilation, kernel replay or full-owned declaration audit for this new source yet. The mixed historical receiving closure remains a separate gate. Previously accepted thin suppliers do not confer automatic acceptance on this module. Source-only formal/kernel credit remains zero. This author created Git blobs only and changed no accepted/queued source, commit or ref.
