# P3.1 next family-budget source audit

Date: 2026-11-27. Baseline accepted checkout: `e63206af301eb31c3518794fe5f9a1816e61f3b6`.

This is a targeted original-source and mathematical handoff. It records a genuine original smoothing-parameter choice and the remaining family connection. It is not a Lean compilation or acceptance receipt. The numerical cardinality supplier is separate; this document adds no polynomial family proof.

## 1. What the finite cardinality step supplies

For an admissible atom `e`, let

- `T := baseCarrier e (D / delta)`;
- `H := e.sharedSmoothFrequencyBound Z D`;
- `F := scaleF e D g`.

The finite calculation gives

\[
\operatorname{rawLabelBudget}(T,H,F)
\le (2F+1)\bigl((e.Q2+1)(2H)\bigr)^2.
\]

The actual quotient carrier is an image of a filter of the original factor window, so its cardinality is at most `Q2+1`, even when the quotient parameter is zero. The original signed nonzero h window has cardinality at most `2H`. The f interval is the full closed integer interval from `ceil(-F)` to `floor F`, including zero, hence the retained `+1`. Actual `F>=0` follows from admissibility and nonnegative natural casts, including zero total-division denominators.

The exact recovered counting declarations are:

| Full declaration | Original file | Lines |
|---|---|---|
| `ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment.card_nat_ceiling_floor_le_length_add_one` | S8 `Part3ElementaryE1RealEndpoint.lean` | 21-37 |
| `ImbalancedChen.Part3.GeneralDPhysicalTailCountSourceOnly.factorCarrier_card_le_add_one` | S5 `Part3ActualSeparatedRowFiniteMatcher.lean` | 885-890 |
| `ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly.frequency_card_le` | S7 `Part3ActualCompletedZeroDifferencePayment.lean` | 90-98 |

S7's private `signedF_card_le` at 118-132 is for the extra filter `f != 0` and does not bound the full raw f carrier without adding the missing zero point.

## 2. The original construction explicitly chooses Z = x^eta

The original `Part3SharedFirstFactorSmallCoreSmoothFrequency.lean` contains the public theorem

`ImbalancedChen.Part3.actual_smallSupported_smoothFiniteFrequency_log_payment`

at lines 722-809. Its exact statement is at 722-733. The fixed inputs are `B sigma kappa c0 A eta`, with `sigma>0` and `eta>0`. It chooses one threshold before the varying atom `d`, and sets

```
let e := d.cleanedAlphaAtom
let Y := d.scale ^ (sigma / 4)
let Z := d.scale ^ eta
```

It bounds

\[
\left(\sum_{n\in d.\mathrm{betaCarrier}}\|d.\beta(n)\|^2\right)
\left(\sum_{p\in d.\mathrm{primitiveFirstFactorCarrier}}\|d.\gamma_1(p)\|^2\right)
\left\|e.\mathrm{sharedSmallPairedSmallSupportedNonzero}(Y,Y)
-e.\mathrm{sharedSmallPairedSmallSupportedNonzeroSmooth}(Y,Y,Z)\right\|
\le \frac{d.\mathrm{scale}^2}{(\log d.\mathrm{scale})^A}.
\]

This is the earlier smooth finite-frequency approximation, with the original outside beta/gamma moments paid. It is not the later common completed-m hard tail. The proof chooses `r := Nat.ceil (11 / eta) + 1` before varying `d` (lines 735-745), and uses the concrete earlier tail bound in that file (624-630).

This provides a genuine original parameter choice, rather than an assumption that the desired later error is already small. The source must still be recovered and qualified in the current closure if its earlier smoothing conclusion is claimed.

### Required atom dictionary

The theorem uses `e := d.cleanedAlphaAtom`, not an independent atom silently identified with `d`. Its proof invokes `mediumAdmissible_cleanedAlphaAtom` for the cleaned atom. A final connection must retain this dictionary and the unchanged scale fields. The current actual coefficient/tail interfaces can be specialized at the cleaned atom, but that specialization does not itself prove the earlier row identity or smoothing payment.

### Do not conflate the two variables named Z

The Lean argument `Z` in `sharedSmoothFrequencyBound` is the physical smooth-frequency cutoff multiplier. In manuscript lines 673-674, `Z` instead denotes the later spectral level length in `z`. The manuscript's substitution `Z=S^2` at line 833 concerns that spectral level length; it is not a license to set the Lean smoothing multiplier to `S^2`.

## 3. Original geometry available for a subsequent polynomial estimate

In the same original smooth-frequency file, private theorem

`ImbalancedChen.Part3.SharedFirstFactorSmallCoreSmoothFrequency.geometry_le_scale`

at 142-189 proves

\[
e.U,\ e.V,\ e.Q1,\ e.Q2,\ e.Q3\le e.\mathrm{scale}
\]

from `MediumAdmissible ... e` and `sigma>0`. This latter condition is an original final-family gate. The proof uses the original monomial inequalities, not a new assumption on the total label budget.

Its two elementary public helpers are in `Part3TransposedPrimitiveUPayment.lean`:

- `ImbalancedChen.Part3.TransposedPrimitiveUPayment.one_le_scale`, lines 29-35;
- `ImbalancedChen.Part3.TransposedPrimitiveUPayment.V_le_scale`, lines 37-41.

These helper bodies use only the existing `U,V>=1` fields. Whole historical payment imports are unnecessary if only the small geometry slice is recovered.

The original physical scales in S6 `Part3ActualPositiveLatticeSmoothCover.lean` are:

\[
B=\frac{lUQ_3}{\delta},\qquad
C=\frac{UQ_3Q_2}{glD},\qquad
F=\frac{U}{gQ_1D}.
\]

Definitions are at lines 295, 297 and 299. The current owner already supplies `scaleF`; it must not be redeclared. The actual `scaleB` positivity proof at 301-315 derives `delta>0` from original slice membership. The original `scaleC_pos` proof at 317-327 uses positive actual `D,g,l`. A free positive `C` in the current consumer is not yet identified with this original scale.

## 4. A coarse sufficient polynomial calculation (not implemented here)

Write `x=e.scale`. With `sigma>0`, the original geometry above gives `x>=1` and each displayed factor length at most `x`. For the genuine choice `Z=x^eta`, `eta>0` gives `Z>=1`.

For nonnegative natural feature denominators, splitting the zero case from the positive case gives

\[
F\le x,\qquad C_{\rm actual}\le x^3,\qquad
H\le64Zx^5+1\le65Zx^5.
\]

No upper bound on `D,g,l,delta` is needed for these coarse per-mode bounds: nonzero natural denominator factors are at least one, zero denominators yield zero total quotients, and the quotient carrier is already bounded by its original factor carrier.

Therefore the explicit finite cardinality estimate implies

\[
\operatorname{rawLabelBudget}(T,H,F)
\le (3x)(2x\cdot130Zx^5)^2
=202800Z^2x^{13},
\]

and

\[
C_{\rm actual}^2\operatorname{rawLabelBudget}(T,H,F)
\le202800x^{19+2\eta}.
\]

These exponents are deliberately coarse and sufficient for choosing a fixed hard-tail derivative order. This display is a mathematical derivation for the next step, not a theorem added in this round and not a proposed target-shaped hypothesis.

After `R=x^epsilon/10`, a fixed order satisfying

\[
\epsilon(r-1)\ge19+2\eta+L
\]

would pay an `x^(-L)` one-mode tail. Any genuine additional outer loss must be included before choosing the order. The per-mode statement does not pay an infinite outer Fourier-mode sum.

## 5. Remaining original-family work

1. Instantiate the physical smoothing multiplier at the original `x^eta` choice and preserve the cleaned-alpha dictionary. Restore the original earlier smoothing payment only if claiming that full connection.
2. Identify the completed positive scales with original `scaleB/scaleC`, and obtain their positivity from the actual slice licenses.
3. Recover the small geometry slice and derive the polynomial label budget; do not introduce a premise saying the total mass is already small.
4. Pay the actual outer Fourier coefficients and label recombination. Existing original mode-l1 sources can be used, but a uniform bound for one mode is not a sum over all modes.
5. Reconnect to the original supported row and then the signed medium-error target. Keep all constants and derivative orders fixed before the varying atom.

This audit found a finite closure/integration task, with a concrete original source for the smoothing choice. It did not find a new manuscript-external analytic theorem needed for the numeric cardinality step. It does not settle Theorem J, Theorem A, spectral-height independence, or the complete original signed-error estimate.

## 6. Manuscript license

Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes` at commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`, file `paper/release-20261106/en/analytic-appendix.tex`, 45951 bytes, Git blob `7cf3bbb16cd8924565eb439e474e0674f04631da`, SHA256 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`.

| Lines | Relevant exact role |
|---|---|
| 27-35 | Initial Poisson truncation for polynomially bounded positive scales |
| 378-380 | Actual h-frequency scale and logarithmic factor |
| 449-453 | One-bounded sequences fixed before remaining summations |
| 559-585 | Positive-square block scales and genuine outside cost |
| 588-620 | Ordered coefficient product and positive tuple-count domination |
| 673-674 | Spectral Z denotes level length, distinct from the Lean smoothing multiplier |
| 686-687 | Indicators and unit phases do not increase coefficient norms |
| 700-703 | Common completed-m cutoff and fixed sufficiently large derivative order |
| 833-839 | Increasing scale substitutions; F and H bounds with selectable small powers |

## 7. Original-source identities and precise fragments

Original reference root: `/workspace/scratch/e5f883a2215a/reference/ImbalancedChen/`.

| ID | File | Bytes | Git blob | SHA256 |
|---|---|---:|---|---|
| S5 | `Part3ActualSeparatedRowFiniteMatcher.lean` | 116891 | `c90d4709b3dde3704006ddb8b959c5dc85bcb60a` | `c668788542424f65003dec6586af9aee814b4e9f4fd7246714eec7815b1f1fe0` |
| S6 | `Part3ActualPositiveLatticeSmoothCover.lean` | 24631 | `a094a3dcd2b43124f42e8219e2b1b6ef9ac26cb4` | `6e4dbe90aa13cdd346bb93589733d6469a96d60cdf50c6df33a5c46971821da9` |
| S7 | `Part3ActualCompletedZeroDifferencePayment.lean` | 33745 | `c9e790baf7e031b40fa5ed211c5f15b9e66d21d6` | `d492722a53eb3bf6a5e7cc5dd60fa7ebc50d4743ed56c7c9b00a883917cd05b6` |
| S8 | `Part3ElementaryE1RealEndpoint.lean` | 10764 | `a129f1583f9a5d5782bdc548491eb88f2c38e956` | `5c386ee17594c075b81b15d56143284fd0f77364f87129d0a96632f17064f8ad` |
| F1 | `Part3SharedFirstFactorSmallCoreSmoothFrequency.lean` | 40367 | `115d5ec4201f2967161d894eb84c859f251600aa` | `2c542a1aad86b505798e83cc1564ee751b763921c6f9dda6289750307328f9fd` |
| F2 | `Part3TransposedPrimitiveUPayment.lean` | 10090 | `f577230571987b258ad4aea8ab4fee25c1a83949` | `d4960bb71109729102df43dee6cad452937cbb73fae2c6b359828d74c5bc12a8` |

| Fragment | Zero-based byte offset | Bytes | Fragment SHA256 |
|---|---:|---:|---|
| S8 lines 21-37 | 834 | 776 | `fa247bee8d2394031b368bac4f735ac682375bd77bae18129a7ffd423bd882b5` |
| S5 lines 885-890 | 41620 | 337 | `8f019d748dcd5605d70c2869bd6e3010e525a53bdebb5c2868b395acb3971acc` |
| S7 lines 90-98 | 4631 | 668 | `fe0b93f8457566e399156494af83c0be10296e981098097bbd63d9502f31061f` |
| F1 geometry lines 142-189 | 6606 | 2081 | `1758226290108cacae3d2ef1733c1288aa409e09265c1e1f8270b84fec1e0c80` |
| F1 actual smoothing payment lines 722-809 | 35780 | 4556 | `c40d8209b04e56bd1006f99e386ca52e90ce5e1fab790c9a0825681695c0d04d` |
| S6 scale definitions lines 295-299 | 12764 | 233 | `894ab74b3883b4373ea9ea5c08b101be73835a7caee603ca8405e772d609d4ee` |

The lookup was limited to the known original counting/scaling donors and exact references to the smooth-frequency supplier and its small geometry helpers. No new remote audit or cloud job was run for this handoff.
