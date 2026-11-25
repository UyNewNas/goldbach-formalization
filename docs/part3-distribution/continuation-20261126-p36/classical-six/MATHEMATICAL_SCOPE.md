# Classical six: exact mathematical scope

The initial source and quantifier review used
`a65747d928f5d8110933ac14cb525e236680e189`. The final compatible source at
`d1db3a39797ec5e6427bce3e62c42b67c98b1492` has now passed the full six-owner
formal gate, with 85 complete inventory records and locally verified evidence.
See the [receipt](../accepted-classical-six/RECEIPT.json) and
[local evidence verification](../accepted-classical-six/LOCAL_VERIFICATION.json).
The mathematical statements and boundaries below are retained. Whole P3.6
remains open, including child-28 and child-30.

All namespaces below omit the common `ImbalancedChen.` prefix.

| Entry module | Main declarations and exact scope | Remaining boundary |
|---|---|---|
| `P5OriginalU5ScalarSmoothCutoffs` | `P5Z.ActualEtaPsiOccurrenceBudget.eta_smooth`, `eta_bounds`, `eta_zero`, `eta_one`; `P5Z.ActualSingletonPrimeTestFamily.chi_smooth`, `chi_bounds`, `chi_one`, `chi_zero`, `chiLog_smooth`. These give globally smooth scalar cutoffs, values in `[0,1]`, and the exact constant ranges at inputs at most 1 or at least 2. | No coefficient-family admission, common physical modulus carrier, positive mass, or PP error estimate. |
| `P5OriginalU5LogCollarBasic` | In `P5Z.ActualSingletonLogCollarFamily`, `profile_smooth` and `profile_bounds` are unconditional in the scalar parameters. With positive collar width and `N >= 2`, `profile_one_on_original_range` and `profile_support` locate the plateau and support. `profile_support_short` additionally uses width at most 1. `logWidth_bounds` and `logWidth_le_inverse_log` control the prescribed logarithmic width. `singletonLicence` constructs a rank-one `Licence`. | This licence supplies a smooth real ambient function and prime-input agreement; it does not contain every uniform derivative, mesh-payment, or high-rank `(S)/(F)` obligation. |
| `P5OriginalU5NarrowSingletonBasic` | In `P5CanonicalTentNarrowSingletonTransfer`, `upperWidth_le_original_endpoint` requires `N >= 2`. `original_middle` and `original_upper_tail` have their stated prime-window assumptions. `original_source_exact_reserves` holds for every real `kappa`, natural `B,N`, finite `Q`, and real coefficient `rho`: original error equals smooth error plus lower reserve plus upper reserve, at the same `N,Q,rho`. | The exact reserve identity does not estimate the three terms. In particular, `upperReserve` is a signed difference and is not asserted nonnegative or small by this identity. |
| `P5WordKernelSignedRow` | `P4BActualUpperTrimPayment.wordKernel_eq_signedRow`: for every finite `Q`, complex coefficient `rho`, natural `N`, and natural-number list `ps`, `wordKernel Q rho N ps = signedRow Q rho N ps.prod`. The complete product is retained, with no primality, rank, licence, or diagonal assumption. | This is an exact kernel identification, not a cancellation or logarithmic-saving estimate. |
| `P1SharpPrimeEndpointDefinitions` | `P1OriginalSharpFiniteReceiver.cut`; `P4AOriginalFull87EighthPrimeMeanLedger.primeMass`, `densityTest`; `P4AOriginalFull87SignedSharpReceiver.sharpPrimeError`. The file itself contains definitions/abbreviations and no explicit theorem. | Defining the signed sharp prime error does not bound it. |
| `P2OriginalU5PlateauRectangle` | In `P2GammaU5PlateauGeometry`, `plateauLevel_exact` identifies `90621/160000`; `original_level_on_box` applies to the stated real-coordinate box. The actual prime rectangle uses lower-closed, upper-open intervals and excludes prime divisors of `N`. For `N >= 2` and `t` in this rectangle, `rectangle_subset_pairSupport`, `rectangle_coordinates`, and `rectangle_rootQ` give inclusion, coordinate bounds, and `rootQ N t = N^(90621/160000)`. | This does not quantify over all of `pairSupport N`, pay the filtered complement, or construct a complete physical modulus `Finset Q`. `rootQ` is a real scale. |

## Child-28 and child-30 remain open

The rectangle result supplies equality of pair-dependent root scales on the
specified rectangle. A common physical `Q` still needs the original causal
coverage and filtered-complement payment. Positive cutoffs or an unsigned box
mass limit do not by themselves give the actual filtered signed-rho harmonic
mass or each required sparse positive-mass family. The missing positive-mass
supplier may be a pair-summed bound; this review does not impose rowwise
positivity.

The six entries do not assemble the complete actual U5/WT/high-rank/enhanced
classes, complete `(S)/(F)`, three-factor licences, or the same-rho uniform PP
conclusion. The actual count consumer `P3OriginalU5SelectedClassicalComplement`
is outside this six-owner scope.

## Existing suppliers are retained

`P5OriginalSingletonLowerTrimPaid.eventually_actual_lowerTrim_logAccuracy` and
`eventually_original_singleton_smoothing_paid` already provide conditional
lower-trim/smoothing estimates for `actualLowerSmallRoughRho`. Their hypotheses
include the original kappa range, modulus inclusion, size bounds, and smooth
weight conditions. The new exact reserve identity does not erase these
suppliers, and does not turn them into payment of all smooth and upper terms.

`ActualPrimeBoxMass.tendsto_actualPrimeBoxMass` already supplies the fixed
unsigned box limit under positive ordered endpoints. Its identification with
the actual filtered signed coefficient and required sparse families is a
separate remaining obligation.

## Counting rule

The six source files contain 58 explicit declarations: 34 `theorem`, 22 `def`,
and two `abbrev`. The accepted complete Lean inventory has 85 records:
61 theorem-kind and 24 definition-kind. Its 27 additional records comprise
seven generated equation theorems and 20 auxiliary proofs. The endpoint file
still has no explicit source theorem; its two extra inventory entries are
`cut._proof_1` and `cut._proof_2`. The exact comparison is preserved in
[DECLARATION_COUNT_REVIEW.json](DECLARATION_COUNT_REVIEW.json).

The 377 selected project sources form the dependency closure; acceptance
credit remains confined to the six specified owned modules. Earlier accepted
owners and reused dependencies receive no new credit from this run.
