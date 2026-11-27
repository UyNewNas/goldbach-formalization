# P3.5: bounded recovery and existing-work audit, 2026-11-27

This is a read-only source audit. It does not claim that an unrecovered source
never existed. It did not contact any of the four remote compiler services,
start a Lean build, modify a remote branch, or replace any historical proof.
The later Drappeau-envelope implementation has a separate verification scope.

## Anchor and accepted components

The GitHub branch `codex/p3-5-full-kernel-20261125` was read at
`ce38b7e8a5a2e7d501afe3a0213e08641dfbc777`. Its last commit retains the
acceptance evidence for mathematical commit
`0ef2ad29bfa30917b3b9ec7008cb831ad1af9408`.

The earlier mathematical commit
`94cff537f2e60173aaf936c2345d5af0ee5e6585` and evidence follow-up
`5285d4f5d8c40eddf92c108b492c909de8b43cef` accept the whole-height
component only. The three owned modules have 81 serialized declarations:
46 in `Part3RegularCumulativeShellPayment`, 31 in
`Part3RegularPositiveMeasureExhaustion`, and 4 in
`Part3ContinuousTraceExhaustion`; 72 theorem records and 9 definitions.
The exact-commit strict compile, bundled kernel replay, complete owned type
inventory and transitive axiom gate observed only `propext`,
`Classical.choice`, and `Quot.sound`. The receipt records 37 successful
stages and 51 source/configuration hashes. Its seven historical suppliers
(378 declarations) and the five-declaration continuous Cauchy core were
reused, not reaccepted as owned targets.

The `0ef2ad29` component accepts 27 declarations in
`Part3ActualSpectralTestJets` and 13 in
`Part3ActualSpectralTestSeminorm`: 32 theorem records and 8 definitions,
including private/generated helpers. Its receipt records 35 successful
stages, 107 source/configuration hashes, the same three allowed/observed
axioms, and 55 unchanged project dependencies under normal imported
environment trust. It selects 22 historical written declarations and adds
11 written declarations for the per-mode supremum derivation. It does not
accept the full historical M/R20/S22 files or an actual Bessel estimate.

These are the retained receipts, not a fresh recompilation performed by this
audit:

- [Whole-height receipt](../../continuation-20261125/continuous-height/RECEIPT.json).
- [Actual test-seminorm receipt](../../continuation-20261126/test-seminorm/RECEIPT.json).
- [Actual-row reuse manifest](../../../source-only/20261125-p35-continuous-trace/REUSE.json).

The whole-height theorem takes separate cumulative energy bounds and low/high
test bounds and proves global L1, its absolute-integral estimate, and signed
cutoff convergence. Global L1 or the target bilinear bound is not an input.
The test-seminorm theorem proves actual per-mode suprema and weighted
summability, with its constant preceding `rho`, `sigma`, and `Y`. It
does not provide the Bessel-transform input. Neither receipt closes P3.5.

## Six registered sources

All names below have the module prefix `ImbalancedChen.`.

| Source basename | Registered bytes | Registered SHA-256 |
| --- | ---: | --- |
| `Part3NativeCuspAllowedRowRightAction.lean` | 3939 | `30526477182739aa5b30fdf90768db1794d1d0e493c6decd0a66e4f2e305e6e6` |
| `Part3NativeAllCuspEisenstein.lean` | 5217 | `43f0110880087df79b0faccc8f57b5218bcbbd3e3ed509b7488903b5cbe3b31a` |
| `Part3NativeAllCuspEisensteinSpatialConvergence.lean` | 6366 | `71ab5c0d4579f8629c46b6be0e91e25404e4da17d106bc98974aa5e3bc71774b` |
| `Part3OriginalCharacterPairDilation.lean` | 6909 | `c35493a2a803c72472e9ab70cfc0bdffb615dafb994c2688b58b68e2fe86131e` |
| `Part3NativeAllCuspFrameCovariance.lean` | 7678 | `8522119e88e35f168f4965f028204ecfe16c21a8f02313090f9c4851703b88b9` |
| `Part3CharacterPairDivisorAmplitude.lean` | 9365 | `99deabe8782b6626f2fc9dbc73cf4b9589442b7b5c46bf34de6e8c8755741fb8` |

The original four native sources were registered under the author's
`goldbach-proof-continuation/.lake/proof-continuation/source-reviews/drafts/`
folders `20261026b-NativeAllCuspAutomorphy` and
`20261026b-NativeAllCuspEisenstein`, including content-addressed
`frozen/<sha256>/` paths. Some receipts preserve the corresponding Windows
path. The dilation and divisor-amplitude sources were registered under
`docs/source-only/20261102-resume-30s/S/s21_full_spectral_classes/`.
These historical path records are locators, not recovered bytes.

The exact registration was read in Y04's
`Y04_SPECTRAL_SOURCE_SELECTION.json` and in T08's
`CRITICAL_CUSPS_REGISTRY.json`, `SCATTERING_REGISTRY.json`,
`UNITARY_SCATTERING_REGISTRY.json`, and T10's
`SUPPLEMENT_REGISTRY.json`, under the source-only history at
`fa22a56829ee880404516a36d498ce27dcb32f92`.

Two registries also preserve Git blob identities:

- `Part3CharacterPairDivisorAmplitude`:
  `6718b15de8e38f8c6c322d861e1e27e68749eff2`.
- `Part3OriginalCharacterPairDilation`:
  `3bb31578a560a37d4ce72e6c038423756681e371`.

Direct read-only GitHub blob requests for both returned HTTP 404 during this
audit. No substitute bytes were installed.

## Current local files and archives

The local check used `rg --files --hidden /workspace/scratch`, excluding
`.git`, `.lake/packages`, and `node_modules`. It included other visible
scratch checkouts as read-only inputs and preserved source-review directories.
It did not follow a remote compiler filesystem.

1. Exact basenames were searched first, then filename patterns allowing any
   suffix, including `.lean.txt`. None of the six exact source names was found.
2. The resulting snapshot contained 123,650 files. The six registered byte
   lengths selected 28 current files. Each selected file was hashed; none
   matched any registered SHA-256.
3. The same visible snapshot contained 68 ZIP and 25 TAR/TAR.GZ archives.
   Their 11,805 member records were inspected. Two archive members matched a
   registered byte length and were hashed. Neither matched a registered hash.
   No archive was extracted or modified, and the scan reported no read errors.
4. Similar names `Part3NativeAllCuspEisensteinVerticalBound.lean` and
   `Part3NativeAllCuspEisensteinC2Maass.lean` occur in existing archives.
   They are different suppliers and do not recover any member of the six.

This check covers the visible filenames, bytes and archive members at the
time of the scan. It does not cover every local Git object, nested archives
inside archive members, Library attachments (not searched in this audit), or
any unavailable remote service. Earlier bounded object/archive searches are
recorded in the existing continuation receipts and were not relabeled as new
findings.

## Separate P2 filename inventory receipt

The parent session subsequently recovered the completed result of the
pre-existing P2 task `53e14470214e497a90db4f45c79a23e1`. This was not a new
compiler task or a repeat search requested by this audit. The task succeeded
with exit code 0 in 26.403632 seconds, reporting 16,601,088 bytes peak memory.
Its 2,680-byte output was complete (`eof=true`, no truncation).

The inventory's recorded completion time is
`2026-11-25T18:28:05.706097+00:00`. It traversed 29,068 directories and
331,053 files under `/workspace`, excluding `.git`, `.lake/packages`,
`node_modules`, and generated build trees, while retaining
`.lake/proof-continuation`. For the six exact `.lean` basenames it returned
`candidates=[]` and `errors=[]`.

The raw result is retained separately as
[P2_SOURCE_RECOVERY.json](P2_SOURCE_RECOVERY.json). Its negative result is
limited to exact filenames in that recorded inventory: it did not test
arbitrary suffixes, archive members, content hashes, or Git objects. It neither
changes the historical receipts nor establishes that the sources do not
exist elsewhere.

## GitHub branch and tree scope

GitHub's branch collection was read through five populated 100-item pages
and an empty sixth page: 484 branch heads. The selected scope was every one
of the 30 branch names containing `p3`, plus `master`,
`codex/yellow-closure-20261110`, `storage/goldbach-repair-20261028`,
and `ci/resume-compile-repairs-20261111`.

The selected heads are listed below. Their `ImbalancedChen`, tracked
`.lake`, and `docs/source-only` trees were deduplicated by Git tree SHA.
The resulting 130 recursive subtree responses were all untruncated and
contained 11,127 distinct file blobs. No exact source basename, including
an extra suffix, matched. The artifact-only `p36` branch has none of
those three source directories; its branch identity is included in the
inventory, not as a scanned source tree.

| Branch | Head read |
| --- | --- |
| `artifacts/p36-normalized-density-20261126` | `59cf6341935bc0b8b780526e2d9d2f12d5f1a893` |
| `chatgpt/chen-p3-distribution` | `688f495a56d29ad250bd0719ef2cb8c18d5f722c` |
| `chatgpt/p3-5-bounded-chart-20261119-1734` | `082e55b2b0a82c422b3b9391f41ec21d1f2cbad9` |
| `chatgpt/p3-dyadic-head-family-20261103` | `2d4e1355be2c5f4ae663c8ab7a7fada95b6d0ccc` |
| `chatgpt/p3-internal-chart-budget-20261104` | `d296beb2ef371ed1bcef330867c82489154ac2e3` |
| `chatgpt/p3-internal-hb-log-budget-20261105` | `de582e6ff4ba430a30889f7c7366a9cf7faa9da4` |
| `chatgpt/p3-internal-original-w-20261105` | `585523dc2c047ca39551ba32985d24a797130832` |
| `chatgpt/p3-internal-product-chart-20261104` | `6e5a634075431c33497e93374a28b8c3e8d17d35` |
| `chatgpt/p3-internal-root-atlas-20261103` | `f0f55d7b3d12b2b892978f63ef63988961edfca0` |
| `chatgpt/p3-internal-smooth-atlas-20261103` | `317fe75ebe3f9ee4735fe392e810c931b00d7519` |
| `chatgpt/p3-joint-complement-20261103` | `b12b805d6ea7c7b3253ad8eefce91f2e5c4e825f` |
| `chatgpt/p3-joint-discarded-payment-20261103` | `17813c8649f564a4c960c6ea26c81f04fa643fcc` |
| `chatgpt/p3-joint-log-assembly-20261103` | `153bb09ba934c5d5b76451f9df11006149e1e54b` |
| `chatgpt/p3-joint-order-payment-20261103` | `2638981ed317e4fa11fc1bf91d2ece442c41dd38` |
| `chatgpt/p3-rank-scaled-upper-20261103` | `b538b42d3ddecb1a562488cc6af8575fcaa0fa4b` |
| `chatgpt/p3-retained-same-rho-20261103` | `0632f2e1839bbdba1604c546bbc3be46b7536d47` |
| `chatgpt/p3-selected-theta-20261103` | `f1bcf37b6fe3f0a5a4b6c4c48b166a6119f9f784` |
| `chatgpt/p3-u5-plateau-theta-20261103` | `f91eadb8e329a3ffce7d91a6ab78500d41a86c24` |
| `ci/resume-compile-repairs-20261111` | `356c3782e9428098a2fcbfb18c689bef264d84fa` |
| `codex/p3-5-full-kernel-20261125` | `ce38b7e8a5a2e7d501afe3a0213e08641dfbc777` |
| `codex/p3-continuation-20261124` | `ef1479c272bdd6b24800fa10409d793f0a2fe95c` |
| `codex/p3-formalization-20261123` | `c509267dc630d91df33033abde1c484ec86b96ae` |
| `codex/p34-kernel-20261125` | `2110a6170401bfc0dcaee46f689ee5f705507683` |
| `codex/yellow-closure-20261110` | `fa22a56829ee880404516a36d498ce27dcb32f92` |
| `integrate/p3-closed-nodes` | `9f19669376b16eb538aea8da9089dc2ec43a85a3` |
| `master` | `980068c76fef46adf5974552e51f95625af7e4c0` |
| `storage/goldbach-repair-20261028` | `fe6117bbcefb33cc6296214d307c2b507366dfe5` |
| `work/p3-1-interface-20261125` | `eac59fac68a389eee5d15c3c44eb9dd487049ab9` |
| `work/p3-1-proof-20261126` | `2a6b7b7473a31aaa3175ce2b8c3ef1b57c6af254` |
| `work/p3-2-proof-20261125` | `30e2a96b601458d59116517ca478c496a68a39c9` |
| `work/p3-3-formal-proof-20261125` | `4cc60c677fed62f626b6208d3aeecb40c821bad7` |
| `work/p3-6-classical-20261125` | `ff84f0706527fff718e3be59c448a4cc592d44fc` |
| `work/p3-6-original-u5-20261125` | `102c46c652fd10138071582aab083d7e3c0140dd` |
| `work/p3-6-warm-payment-20261126` | `525747fe88f8a6847c479bfe4a5bcc15aa13003a` |

The three distinct remote blobs matching one of the six byte lengths were
read back and SHA-256 checked:

| Candidate | Bytes | Observed SHA-256 |
| --- | ---: | --- |
| `P3HBMarkedFixedProductMassBound.lean` | 6366 | `2636453a9284cafc5083bf384d99bac3fcaf4ec77983bd4cd9ec49df3d63a502` |
| `OriginalAscendingThirteenCellOwnership.lean` | 9365 | `665206e0e766283e3efbc575e35a74d196965021d6ce775b8f829018209aee80` |
| `Part3ActualCommonMaskPhysicalHeightTail.lean` | 6366 | `a7a35ea20f1a21511be976e53b089f256585282916b43f6671c637b8b393b3af` |

All differ from the registered sources. This was a branch-specific tree
search, not a default-branch-only code search. It does not claim to exhaust
the other 450 branch heads, all historical/unreachable Git objects, or all
files outside the selected source directories.

## Existing work and the continuation frontier

The following existing material must be reused with its actual status.

- Y04's `Part3OriginalPrintedContinuousTrace.printed_continuous_large_sieve`
  derives the printed `dt/pi` normalization from the actual regular
  three-measure supplier. `Part3OriginalGeometricWindowEnergy.original_two_cumulative_windows`
  derives the two original cumulative windows and keeps the divisor-square
  cost on the unremoved source. These source-level statements do not assume
  the desired paired return. Their selected import closure still lacks the
  six sources above. They are not accepted build artifacts in the anchor.
- The later `Part3OriginalRegularThreeMeasures.manuscript_regular_three`
  exists in `20261113-resume/resume-balance-policy/r14_04/regular-sieve-full-next/maass-transport-next/revision-2/`.
  Therefore the earlier `r13_09/REGULAR_SIEVE.md` statement that a source
  proof of the cumulative forms had not been found is not the latest source
  inventory. No new proof of that supplier is required by this audit.
- `Part3ActualPrescribedPositiveJ.regular_transform` identifies the actual
  same-sign transform, including height zero, with a Schwartz function.
  `fixed_regular_decay` chooses its constant after the mode and scale.
  This does not supply the uniform constant needed for the full Fourier sum.
- `Part3OriginalSwitchedUniformRegularTransform.mode_uniform` is a genuine
  source proof with its constant before the parameters. Its test family is
  the switched inverse scale `spectralTest (mode k) Y⁻¹`, `Y>=1`,
  one integer Fourier axis, and a `1+log(2Y)^2` cost. It does not establish
  the requested arbitrary-positive-scale, four-coordinate regular envelope.
- The bounded-chart branch at `082e55b2b0a82c422b3b9391f41ec21d1f2cbad9`
  contains `Part3OriginalTwoChartRawMass`,
  `Part3OriginalAllKeysRawMass`, and
  `Part3OriginalSixScaleReturnAdapter`, absent from the small current
  P3.5 source set. They give useful finite mass identities or scalar return
  adapters, and are explicitly source-only/uncompiled. Their weighted
  terminal estimates still require per-key scalar prices; they do not
  supply the actual spectral estimates or close the full `7/32` result.
- The existing `Part3SpectralReturn25` supplies the scalar
  spectral-polynomial-to-returned-polynomial algebra, including `7/32`.
  It does not instantiate the missing original spectral inputs.

The next independent manuscript-side derivation is the actual C4 test
normalization and the cubic-envelope-to-existing-shell adapter. Its
lower-level transform envelope is an explicitly retained external input;
passing that envelope as a hypothesis must not be counted as proving the
actual Bessel theorem. Actual positive/negative transform identification,
the missing Y04 closure, the uniform physical-family applications and the
full spectral/level/Fourier/six-scale assembly remain separate obligations.

PR #12 was read as an open Draft at
`integrate/p3-closed-nodes@9f19669376b16eb538aea8da9089dc2ec43a85a3`.
It lists the closed P3.2, P3.3 and P3.7 secondary nodes. It explicitly lacks
a fresh joint-branch Lean replay and does not include P3.5. This audit made
no PR or board changes.
