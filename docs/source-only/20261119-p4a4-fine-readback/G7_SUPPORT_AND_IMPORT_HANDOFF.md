# P4A.4 G7 support and Fine import handoff — 2026-11-19

SOURCE_ONLY. COMPILED: NO. KERNEL_REPLAYED: NO. TRANSITIVE_AXIOMS: NOT CHECKED. INDEPENDENT_REVIEW_THIS_RUN: NO. FINITE_CERTIFICATES: UNEVALUATED. No Lean proof body was added or changed.

Baseline: aaece2da42be17a82e19c63920fa0e001858ac56, parent of this handoff. Continue from this branch head, not from the older yellow publication. Previous handoff: docs/source-only/20261119-p4a4-fine-readback/HANDOFF.md.

## G7 precise source readback

Read complete bodies of ChangedSupport, OrderedLocal, OrderedTestLower, OrderedSum, selected repaired OrderedPayment, ElevenUpperDispatch, SectorTransport, All22RawLedger and Full87UpperDispatch. These are already-authored proof candidates, not newly proved or checked theorems.

- In ChangedSupport (Git blob 79c6e8d498c118243eb1e6a5ce40ae79832cff01), a strict actual stage-1-to-2 cap change forces a member of the original finite maximum and derives its PhysicalCell, in both raw and rounded branches. The whole admitted word lower-error theorem treats equality as exactly zero and the strict case with the closed quotient bound. Its quantified range is all admitted words, including words outside a compact trim.
- OrderedTestLower (selected repair blob cb21a4440433599154962c06204ae5cdec4b5979) splits the nonzero-test case from zero tests. The former uses the derived common historical owner, admission and actual residual; the latter retains the possibly negative actual admitted residual and pays the uniform negative error. It uses uniqueness away from comparison ties rather than asserting independent summands.
- OrderedSum (blob 1d0ba2e7168a862b756f32b787b62ad3ea64c833) proves residual_zero_outside_box by deriving an original winning PhysicalCell, then reindexes the complete admitted signed sum onto the actual target-deleted prime box. The weight is the original product of 1/(p_j-1); the fixed-box mass pays the error.
- OrderedPayment (selected repair blob 854528d31fb418fd0abc769ef16f7046230e1f00) consumes those actual test sums with an n/e/q/a/omega/N schedule and uses the original G7 replacement floor 1208544915921356327515701/2^96. The Q96 floor is a candidate finite certificate input, not evaluated here. Exact integer arithmetic gives replacement minus older 1201130581437641342320905/2^96 as 7414334483714985194796/2^96 > 0. The older floor is replaced, not charged again.
- ElevenUpperDispatch (blob ead6cd2fa1975bd87706d7488d043613ae4db1a8) uses the same winning-cell bound to establish equality of the two actual policies above mu, including each frozen sixth ancestor. SectorTransport.local_increment (blob f4f9ac604b3e3b2a9f647325ef35e9903cde0181) transfers their signed raw difference under the stated even-retention hypotheses. All22RawLedger.lowerEleven_eq_paid_source (blob 88a37861a9d5bdfaec4cdb34196cc0fe5f91afe2) specializes the upper rule to fresh, using its positive/empty-bank identity, so the actual lowStage1-to-lowStage2 saving is the same G7 gain. PaidSixth uses its zero-based slot 6 once; the following Nineteen/Fine chain retains the rest of the telescope.
- Full87UpperDispatch (blob cb03a817c4b133777d3429a3df59047d8d889ef0) has a separate high-word equality for the eighth action and transfers its eight-slot ordinary R17 saving. This is not a proof that the separately compiled eighth parent CI includes the Fine or complete All22 closure.

The 34 entries in the corrected G7 selected install manifest, blob 3233d121561f2b579379f1aacf651d578d7d004e at 19c7759d496bb527cc8546cfeb17f8579f10bfed, were read at the baseline branch: 34/34 returned Git blobs equal the corresponding selected manifest entries. This verifies source identities, not a staged graph, certificates, Lean types or axiom dependencies. The prior independent mathematical source review is G7_SELECTED34_ORDERED_PAYMENT_REVIEW.md blob b6fc5442638c1eb4954346907fb0ccb7471b6be8; it is not a fresh independent review.

## Concrete Fine installation boundary

The baseline includes the Fine candidate under docs/source-only, not at its canonical ImbalancedChen module path. Its first import is P4AOriginalFiniteAll22CofinalCoefficient, blob dcbc30e0069583297b47c661580be2f112a53636, whose first import is P4AOriginalFiniteAll22EarlyDefectCounting. The latter is not present at the baseline branch in the P4 source directory or canonical module location. It is readable at immutable P4 source eea9486f7b101d484e2938e97499c1d77cc1a67a:

1. docs/source-only/20261111-p4-nineteen-count/P4AOriginalFiniteAll22EarlyDefectCounting.lean, blob fb3aa5371d57b599fac9726603aaf3d179dd38db; imports Nineteen and FiniteFallbackCanonical.
2. docs/source-only/20261111-p4-nineteen-count/P4AOriginalFiniteAll22Nineteen.lean, blob abadf4d9fbbec16085deb732f4e3388e35500218; imports PaidSixth, Full87UpperDispatch, FiniteFallbackJointGain, and OriginalKLedger.
3. docs/source-only/20261111-p4-dispatch-paid-sixth/P4AOriginalFiniteAll22PaidSixth.lean, blob cdef0be4f600a2cb88be6acd756e3d451c9eb40a.

All three are source-only dependencies. Neither the two expected P4 archival paths nor the canonical Nineteen path exist on the baseline branch; its registered reused/P4 path and the two checked reused/required_api staged paths also returned 404. These API observations do not establish that blobs are missing globally: the above immutable sources are readable. Fine itself calls the raw Nineteen theorem and early payment, yet importing the ordinary module still requires EarlyDefectCounting to resolve. An installer must preserve all direct imports even if an imported existential is not called.

This is a demonstrated *installation* gap, not evidence of a new mathematical gap. A safe installer must resolve the cross-commit P4 files above, the other exact selection/overlays and the full transitive closure by module name and byte identity. Do not glob-install same-name G7 variants: the selected repaired Payment is 854528d3, and two List scopes plus the FullPolicy/R17 selection remain necessary. No complete graph or staged postimage is certified here.

## Verification and remaining work

The shell environment returned no path for lean, lake or elan using command -v (shell completed, output empty). No toolchain was installed, no pins or resource limits changed, no CI or user machine was used. Python exact rational subtraction exited 0; it is not evaluation of the Q96 Lean certificate. Source audit does not establish correctness of each transitive mathematical proof.

Manifest pins and manuscript provenance remain as in the immediately preceding handoff: Lean leanprover/lean4:v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, native goldbach 09b97db5764ade1246bfb77206baa1b124760958; manuscript source tree 4df4763ce4d22730fb3c30b816244e9c51c04a19, manuscript-body blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79. Existing external inputs are reused by the selected proof sources; this handoff neither implements nor newly verifies PNT/Mertens or other external supplies.

Next verify a coherent same-source installation and remaining individual actual four-positive and saving endpoint chains, chronological occurrence, exact Q96/rounding fixtures and their finite guards; then elaborate the precise Fine endpoint and downstream consumer, audit expanded types and transitive axioms, and perform fresh kernel replay. No unsupported All22 green promotion. Signed PP and whole hUpper remain outside the scope of this packet.
