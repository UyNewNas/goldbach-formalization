# Independent review of the actual singleton medium window

Decision: **ALLOW the exact U02 postimage for source-level mathematics and local applicability**, SHA-256 `2c2da3d3a40695ec78ecdc055acc3d66378b65ed46b1946b71fa1a0533db202a` (9569 bytes, blob `aa0b580baf5ede66e5043c45b82409fcf064cc43`), bound to U02 freeze `eab7f841fd6ab2d75e9eb98c0e3a1635c6375ac66bb2b6f4c7e3142d6a630193`. It supplies a manuscript-internal local geometry lemma, not a signed medium estimate. The original T06 freeze `fd1c611e77107eb4bb9220ecdf5109e6c03b41a0b70ee01f9791a1d3b68938c3` and its source SHA-256 `2c4c8bf58fd305013b4d66801cca4ffeeb9d592676c2fd2cf5c3eb62ca7c806b` (9561 bytes, blob `831cf9642283ad3511fe3b8fec1942013369ec43`) remain unchanged. The original mathematical route passes; its separate API spelling issue is preserved below and is not hidden by the new source approval.

## Actual source and finite geometry

`ActualLowerNormalizedAtlasOccurrence.integerProfile` is exactly `scalarProfile` at `completeProduct n`. Its normalization is the actual log-collar singleton licence, not an abstract desired weight or the two-group P4B profile. `scalarProfile_eq_ambient` separates ambient, eta trim and the same chart's psi; `scalarProfile_support` gives the integer cap `p ≤ 2*N`. For a live tuple and positive N, eta nonvanishing gives the strict lower bound `N^(1-kap0) < p`. No conclusion is inferred from a merely displayed zero-weight tuple.

The generic `tuple_scale` uses the selected coordinate and the dyadic owner of its **entire** complementary product. Both factors lie between their lower endpoint and twice that endpoint, including the unit block, so

```
x ≤ p ≤ 4*x,       N^(1-kap0) < p ≤ 2*N.
```

Thus `N^(1-kap0)/4 ≤ x ≤ 2*N`. `psi_window` gives `R cj / 2 < p < 2 * R cj`; together these imply `R cj ≤ 8*x` and `x ≤ 2*R cj`. The constants 4, 8 and 2 have the asserted directions. The argument needs neither a two-mother support bound nor an HB slot-count bound.

`fibre bs i C` filters the original ordered rectangle by `owner (complement i n) = C`. The complement is the product over all positions except i, with no deleted tail. Its quotient identity uses positivity of the selected coordinate. `same_scale` makes x equal to `lower(bs i) * lower C` for every tuple in this fibre. One live point therefore supplies the geometric parameters of the whole fibre; it does not make every other point live. Neither primality nor distinctness nor squarefreeness is assumed of the HB integers. Equal values at different positions remain distinct coordinates. Unit coordinates and a unit complement remain in the carrier. The derived eventual `1 < U` excludes an actual selected unit medium slot only when the live/selection premises already imply that exclusion; it is not an extra input.

`firstMedium_some` is the original ordered-position selector. Its conclusion is about `bs[i]`, and simplification of `List.ofFn bs` returns `bs i` at that same position. With `js = [cj]`, the two thresholds are exactly `X^(3*zeta)` and `X^(1/3+zeta/4)`, where X is the same `R cj` already read from the profile. Selection does not depend on the tuple, modulus, complementary owner, or sign of the arithmetic error. The proof never calls P4B's two-group `live_geometry` or two-group `eventually_window`.

## Power gaps, residue and rough cutoff

The private scale lemma is legitimate finite/asymptotic bookkeeping. Its hypotheses are the just-proved geometric inequalities, not the desired terminal window. The public terminal has only live-profile, original-selector and fixed-parameter premises.

For fixed `zeta > 0` with `zeta ≤ 1/400`, write `g = 1/3 + zeta/4` and `e = 1/3 + zeta/2`. Eventually:

- `2 ≤ x^(1/3)` and `x ≤ 2X` give `x^(2/3) ≤ X`; raising to the positive power `3*zeta` yields `x^(2*zeta) ≤ U`.
- `X ≤ 8x`, `0 ≤ g ≤ 1`, and `8 ≤ x^(zeta/4)` give `U ≤ X^g ≤ 8^g*x^g ≤ x^e`.
- Since `1-e > 0`, `2 ≤ x^(1-e)` gives `2U ≤ x`. Since `2 ≤ x^zeta` and `x/2 ≤ N`, it also follows that `x^(1-zeta) ≤ N`.

The existing `exists_manuscript_restrictedResidueScale_threshold`, applied with c = 1/4 and C = 2, gives `1 < x` and `x/2 ≤ N ≤ x^(1+kappa)` uniformly in every local x. The buffered `kap0 < kappa/(4*(1+kappa))` supplies a strict positive exponent gap; the physical target is N, not a residual quotient. The extra `kap0 < 1` makes the explicit power-growth threshold available. Lack of a lower positivity assumption on kap0 or kap does not invalidate this geometry: the actual caller has stronger positive choices; if an enlarged parameter range makes the live support empty eventually, the theorem simply has no live fibre there.

Set `D = 2^(6*K+3)` and `v = D*X`. `D ≥ 2` and `x ≤ 2X` give `x ≤ v`. For `x ≥ 8D`, `X ≤ 8x` gives `v ≤ 8Dx ≤ x^2`. The source requires `x ≥ exp(exp 3)` before using roughF monotonicity, so it supplies the actual positive log/loglog domain rather than extrapolating that monotonicity to small x. The original `roughF_mono` and `roughF_upper` then give

```
roughF x ≤ roughF v ≤ x^(2/(log(log x))^3).
```

`original_cutoff_singleton` identifies this exact `roughF v` with `beforeHBCutoff K [cj]`. The cutoff stays fixed by the same original chart before HB selection. It is not replaced by `roughF x`. The next rough-SW consumer's `roughZ` is defined by the same real formula, but applying its arithmetic conclusion to the normalized singleton roles remains a separate step.

## Threshold and actual final caller boundary

K, xMin, kap, zeta, kappa and kap0 are fixed before the eventual N threshold. The proof first chooses an x0 for finitely many fixed power requirements, then forces `N^(1-kap0) > 4*x0`; this works even if the witness x0 is negative. The residue-scale threshold is combined before N. Only afterwards are cj, slot count r, rectangle bs, position i and complementary owner C introduced. No threshold depends on a later label, live point or local x.

The actual final P1 schedule fixes its history, beta, aligned mesh k and K before N. K (the original HB bound) is not Params.k (the aligned mesh index). Its singleton licence is `actualLicence kap 6 N`, counted-prime cap is `2*N`, and physical target/residue is N. `MiddleTensor.singletonAtlas` uses this same licence and `products P/free P`. The new lemma is coefficient-independent geometry and is applicable to that profile without changing the coefficient, small beta, global collision mask or original owner/history. It does not establish a new identification of those coefficients.

`OneLongRectangle.actual_row_reindex:129–152` genuinely permits arbitrary Q and rho for this same singleton row and arbitrary fixed K, so the normalized profile is not tied to a lower-policy coefficient despite its historical namespace. This supplies a relevant row dictionary. It does **not** by itself supply a complete first-medium branch reindexing, role normalization, retained-frequency bound, reconstruction, restoring scalar sum or Atlas payment. No such implication is approved here.

The original PP text at lines 97–117 treats units, the complete complementary dyadic scale, the chart cutoff and the moving residue. Lines 173–175 use exactly the original and local medium exponents. This candidate proves that omitted scale conversion for the singleton family. The stronger numerical constants come from direct complete-product ownership, rather than from a new analytic assertion. The already existing two-group window has different live-profile hypotheses and is not a source that can be substituted for this singleton statement.

## Expression/API issue in the original bytes

Original candidate lines 92–95 spell four power-growth calls `Real.tendsto_rpow_atTop`. The inspected local Mathlib `Analysis/SpecialFunctions/Pow/Asymptotics.lean:36` declares this theorem at the root namespace, and the file has no `namespace Real`. Its whole-Mathlib declaration/alias search did not locate a `Real`-namespaced replacement. The existing P4B helper also uses the old spelling, which is not independent evidence of an available alias. This is a source-level name-resolution concern, not an executed Lean failure or a mathematical counterexample.

U02 subsequently bound this exact 19622-byte standard raw (SHA `004e4d6013b20f95feedfcb23b257c07eb1ee4c7645b9d81fd6e4cb684a116d6`, blob `40bde6d8539f88ebf65d15f623d6d521c578404c`) to the existing local Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` commit/tree path. This review read that frozen metadata, recomputed the raw leaf identity and checked the declaration. It did not independently reread all seven Git objects or audit the whole standard package. Local alias-search results must not be inflated into an exhaustive assertion about all custom dependency environments.

The real import path is candidate → RestrictedResidueScale → PanProductGridRanges → RealHalfProductMassSplit → PowerErrorBudget → Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics. The relevant import lines were independently read. The root API has the required type for all four positive exponents. Its explicit qualification is valid without relying on any global absence-of-alias claim.

The authorized U02 postimage changes only lines 92–95 to `_root_.tendsto_rpow_atTop`. Independent forward and inverse byte comparisons are exact. All four complete declaration headers, including the private scale theorem's `let v`, and all three imports are identical. Every other source byte is unchanged. Thus the reviewed mathematics and statement apply to the exact new source, with this explicit API use independently approved. No original frozen source or old transitive helper is modified, and no compilation result is asserted.

## Scope preserved

No uniform signed M, four whole-box inequalities, actual singleton role/restoration package, complete Atlas, RealB band, historical sharp-middle bound or P1.4 closure is established here. Existing half-J/Weil and OneLong conclusions keep their precise prior scope and status. An import, local window or absence of a newly found supplier does not settle any of those debts. No recursive source closure, environment, elaboration, axiom or kernel claim is made; no formal credit is awarded.

Review operations are local reads and in-memory text/hash/JSON only. No Lean, Lake, LSP, project helper, candidate execution, fixture, guard, network, download, Git mutation, quota call or subagent was used.
