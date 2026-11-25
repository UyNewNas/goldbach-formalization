# P2.9: unit-tail complete-product saving

Status: **NORMAL COMPILE, INDEPENDENT KERNEL REPLAY AND FULL-OWNED AUDIT PASSED**.
The accepted module has 2 owned declarations, including one public theorem.
This is a physical product bound; full P2.9 remains open.

## Exact result and preserved coordinates

The theorem `ImbalancedChen.P2FiniteMarkedGamma5UnitTailProduct.unit_tail_product_le`
keeps every old coordinate and the two fresh slots of the unchanged
physical profile. The tail is empty. Put
\(d=\prod_i x_{\mathrm{old},i}\) and \(R=Q/d\).
For positive Q, floor parameter and width, nonzero original profile and
\(R^2\le N/d\), it proves
\[
 M\le \frac{\exp(2\,\mathrm{width})\,N}{R^{38/29}}.
\]

Both original upper gates give
\(q_i\le \exp(\mathrm{width})R^{10/29}\).
The exponent is exactly \(2-2(10/29)=38/29\).
The empty old product is 1. No prime, distinctness, target-coprimality,
history-weight, integer-count, J or distribution estimate is a premise.

## Existing actual-history connection

The unchanged original
`Part5OriginalH430SeedHistoryMass.scale_and_alpha`
is preserved in
`Part5OriginalH430HistoryScaleCore`, Git blob
`3c4acdfa049752a5b5ce7a23747d4c0c17c33ddd`,
SHA256 `48709f9924fe8c8f83c837ffa71907f0c9c0f7b3b00ab9d1957703d3576bd855`.
It applies for \(N\ge2\), \(0\le t\le1/12\),
\(1/(n+1)\le11/384\), an original U4 root prime p and one of its original
dependent level positions l. It provides \(d>0\), \(Q=dN^L\),
\(R\ge N^{\mathrm{frozenResidualFloor}}\) and
\(2\le\mathrm{trueAlpha}\).
The existing
`P2EnhancedUnitSourceMass.scale_identity`
gives \(R^{\mathrm{trueAlpha}}=N/d\), hence the required \(R^2\le N/d\).

Those state facts apply to a tuple only after matching its whole old
prefix with an actual p,l witness and its root cell. An arbitrary ambient
tuple has no automatic history witness. Turning the product saving into
an eventual integer count and aggregating the actual positive history
weights remain separate steps.

The old bad-unit and short-word results count sharp integer carriers.
They do not directly cover supported real tuples on the relaxed side of
the smooth bad-square wall. This new result supplies that precise product
bound without redoing their counting or power-decay proofs.

## Source and verification

The only project import is the existing PhysicalExtension. The final
source adds the explicit standard-library import
`Mathlib.Analysis.SpecialFunctions.Pow.Real`
needed for real powers; no theorem statement or proof body was changed
from the independently reviewed initial candidate.

Accepted source: Git blob
`eef9c2aa29099c944a49a9cc0519130dea34b448`,
SHA256 `890270815cc29529b121b122314a6ba64ea4eafe848a16456011af99843f10aa`.

Task `cbbac5a4ff9e4e309611265a971155eb`
passed with a six-module project closure, five reused inputs and only
this target newly compiled (4.037 seconds). Independent kernel replay
and the complete two-declaration owned/transitive-axiom audit passed.
Only Classical.choice, Quot.sound and propext were observed.

The 97,300-byte complete evidence archive in `verification/`
has SHA256
`46c060419a8c2796f1e355fd45df4584c1abb4002897c4f596c6ae70ee334ca7`.
It contains source, producer/import bindings and audit/replay records,
not .olean objects. The initial source-only review is retained separately
for provenance. No numerical rows or old native proof were rerun.
