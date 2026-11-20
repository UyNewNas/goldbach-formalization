# P3.5: original two signed Fourier modes on one chart

## Baseline and packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`143baa01dd63c51269b3b02bc0baf47a00a9ae54`. The containing commit is the
new SHA. Adds `Part3OriginalSignedExceptionalMode.lean` and this report
under `docs/source-only/20261120-p35-signed-exceptional-mode/`. Lean
source SHA-256:
`77a9c651f6b38acbf0945d6ba670d2ec82f3c62af7912e0a7168ddece3e8d29a`.

## Exact proposed candidate

Fix the actual data D, key k, one physical chart `upper`, original m
cutoff J and dyadic j, real outer M, positive N and original Fourier
mark ell, with nonzero original residue. Let `Z=fixedZ D upper`,
`V=2^j`, `W=max(V,Z²/V)`, and use exactly the existing original test
scale `Y0=chartY0 D k upper j N`. For b=false,true define the selected
finite strict-exceptional chart mode

    E_b = actualCoeff(V*M/N, if b then -1 else 1, ell)
          * (M sqrt(Z))
          * sum_{(z,i) in Slots} signedRawSlot(D,r,k,upper,b,J,j,ell,Y0;z,i).

The signed slot uses the original composite sign to select either the
actual positive native transform or the actual `8*kTransform` opposite
branch. `Slots` is the exact occupied chart union and strict exceptional
native indices from the parent candidate. The scalar, the test Y0, and
the **two different** Fourier coefficients are those appearing in the
existing chart/block source. The definition here selects the finite
exceptional terms; an equality with the full chart spectrum, including
regular/continuous terms and any indexing bridge, is not claimed.

The candidate `signed_exceptional_two_modes` obtains B>=0 and one m
phase omega before the residue mark r and states

    |E_false+E_true|² <=
      2 (|actualCoeff(V*M/N,1,ell)|² +
         |actualCoeff(V*M/N,-1,ell)|²)
      * (M² Z) * B²
      * (2+log(4V+1))² * (J_(Z/2)(W,omega)+J_Z(W,omega))/4
      * 2 C_sieve (1+|a|nu L/Z) sum_{z in levels} B_z².

The source retains its parenthesized form exactly. The same B and omega
serve both b values because `signed_chart_with_raw_sieve` is quantified
before the sign. The proof uses positivity of the **actual** chartY0,
the triangle inequality on the finite slots, the exact identity
`|(M sqrt Z : C)|²=M² Z`, and `(x+y)²<=2(x²+y²)`. The two occurrences
of actualCoeff are not replaced by a generic common coefficient.

The bound has a raw n loss `1+|a|U/Z`, unevaluated J sums, and B may
depend on the actual chart scale and ell. It only combines two nonzero
Poisson signs on **one** chart for the finite strict-exceptional discrete
component. It does not identify this selected piece with the full
spectral trace, sum the other physical chart or six scales, or prove the
full (24), sharp J, ABL, regular/continuous return or all-cost 7/32.

## Sources and boundary

* Parent `Part3OriginalSignedExceptionalChart.lean`, blob
  `292f96931d23fb22545681824276ee576f468c51`: simultaneous two-sign
  original raw slot bound and the shared phase; its positive transform
  and raw fixed-level sieve dependencies are UNEVALUATED.
* `Part3OriginalPrescribedChartSpectrum.lean`, blob
  `fc79ad8d2de109d661b52ba0e9bb83c3c8315e5a`: the actual chart scalar,
  `chartY0`, and the original `actualCoeff` arguments in the opposite
  block; its exact full trace equality is not asserted for this selected
  exceptional sub-sum. Existing positive-sign and opposite-sign trace
  summands are referenced by the parent report.
* Manuscript pin rechecked:
  `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, distribution
  module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`, §7 (24) and
  §10(vii). No new external theorem is introduced. Pascadi v3 Theorem J,
  ABL v1 Lemmas 3.1–3.2, and the numerical gap retain their prior exact
  range/normalization and missing-supplier registrations in
  `AVGJ_APPLICABILITY.md` and the parent chain.
* Pinned mathlib `Mathlib/Algebra/Order/Ring/Abs.lean` was read at
  `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` to check `sq_abs`.

## Verification and remaining obligations

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including all inherited proof bodies. `command -v lean` and
`command -v lake` returned no path; the exact import closure is not
staged. No compiler ran, so no compiler exit code or log exists.
Rechecked configuration pins: Lean `leanprover/lean4:v4.33.0-rc1`,
mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot
be checked. Stack 8192 KiB, virtual-memory limit unlimited; unchanged.
`sha256sum` gave the above hash; `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1 (no
matches). Neither is compilation; no CI was started.

Next stage exact frozen imports and compile/replay, then audit transitive
axioms. Connect the finite selection to the actual trace decomposition;
control both test budgets and pay or replace the raw n loss, and supply
full-range J. The other chart, six-scale aggregation, regular and
continuous terms, two zero lanes, actual truncation tail, 14eta/28eta,
128C and original N-threshold/reserve order remain open.
