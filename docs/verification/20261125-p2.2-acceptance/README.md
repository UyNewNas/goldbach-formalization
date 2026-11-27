# P2.2 — first-integral endpoint acceptance

P2.2 is complete for the exact source snapshot
`99c1f8ba1dc453b21f47e30b667db0de93d73387`, on
`codex/p1-final-acceptance-20261124`. The current branch consolidates that existing
acceptance under its actual progress-tree node. It introduces no new Lean proof
and repeats no successful Lean compilation.

## Proven statement

With `Theta = 299/500` and `rho = 19/96`, the existing theorem
`ImbalancedChen.P2OriginalFirstIntegralEndpointSourceOnly.originalFirstIntegral_literal_selected_bound`
proves the following literal statement, without an integral-value hypothesis:

```text
(4 / (299 / 500 : Real)) *
  (integral s in 2..((299 / 500 : Real) / (19 / 96 : Real) - 1),
    Real.log (s - 1) / s)
  <= (7179974843999672947 / 9444732965739290427392 : Real)
```

`originalFirstIntegral_le_budget_base_one` binds the same bound to
`P2OriginalCertificateBudget.baseUpper 1`. The selected upper endpoint is also
below the manuscript's upward-rounded displayed value `76020940667/10^14`.
The auxiliary exact-rational calculation in the verifier checks this comparison;
the mathematical acceptance rests on the existing Lean theorem and its receipts.

## Manuscript correspondence

The manuscript is `UyNewNas/chen-imbalanced-semiprimes`, 1106 version, frozen at
`a988cba584d803ae2856a0de50efb582f4f3dd6a`. Relevant English sources are:

- `en/argument.tex`, lines 207–211 and 1077–1086: parameters and the upper-density
  decomposition containing the first-integral cost.
- `en/numerical-appendix.tex`, lines 123–133, 198–231 and 286–300: sieve-factor
  recurrence, full-domain series/remainder method and displayed directed bound.
- `docs/part2/adopted-evidence-catalog.json` in this formalization snapshot:
  the exact selected `first_integral_upper_exact` endpoint.

The analytic proof retains the full interval. Translating `x = s - 2` gives
`[0, 51/2375]`; the finite logarithm and reciprocal polynomials each have 16 terms.
Their product therefore has **256 terms**, not order 256. The genuine analytic
remainder is `radiusQ 16 16`. Retaining this exact remainder matters: substituting
the looser bound `2^(-80)` is insufficient for this particular sharp endpoint.

## Existing proof and verification chain

| Module | Original batch | Owned | Public | Role |
| --- | ---: | ---: | ---: | --- |
| `P2FirstIntegralSeries` | 54 | 47 | 46 | Original integral, full-domain translation and series enclosure |
| `P2FirstIntegralPolynomialEnclosure` | 65 | 68 | 68 | Polynomial integral, rational center and analytic remainder |
| `P2OriginalFirstIntegralEndpoint` | 86 | 9 | 9 | Exact 16×16 comparison, literal integral bound and budget binding |
| **Total** | | **124** | **123** | Includes one private/generated declaration |

The original evidence directories are
`docs/verification/20261123-blue-compilation/member-repair-batch54`,
`member-repair-batch65` and `member-repair-batch86`.
Each contains normal compilation, independent `leanchecker` replay, full-owned
type/axiom audit, publication hashes and final release records. The three normal,
three kernel and three audit commands all exited with code 0. The declaration
audit uses only `propext`, `Classical.choice` and `Quot.sound`; there is no new axiom
or `sorryAx` in these 124 declarations.

All three accepted Lean source files are preserved byte for byte. Their historical
`SOURCE ONLY` comments and namespace names predate successful verification. Each
batch's `SOURCE_SELECTION.json` explicitly records the later validation externally;
editing those comments here would needlessly change the accepted source hashes.

## Reproduce the evidence check

From the repository root, with the frozen commit available locally:

```sh
python3 verification/part2/verify_p22_acceptance.py \
  --output docs/verification/20261125-p2.2-acceptance/verification-result.json
```

The verifier reads the original evidence from Git objects, so a sparse checkout
does not need to materialize the large historical logs. It checks the selected
source bytes, recorded command exits and log hashes, declaration inventories and
their full audit records, and the original source/receipt bindings. The compact
machine-readable selection is `acceptance.json`; the latest verification result
is `verification-result.json`.

## Scope

This acceptance closes **P2.2: the first-integral sharp endpoint and polynomial
enclosure**. It does not certify the separate Winner9 row archive, all P2 integral
certificates, downstream P4 assembly, or the final Goldbach theorem. The older
`work/p2-formal-proof` branch is not silently treated as the accepted snapshot:
its three first-integral files differ from the versions identified above.
