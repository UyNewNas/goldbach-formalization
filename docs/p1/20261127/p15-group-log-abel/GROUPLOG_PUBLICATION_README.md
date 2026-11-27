# Original HB group logarithm: Abel variation source package

## Publication status

This source publication concerns `ImbalancedChen.P5OriginalGroupLogAbelVariation`
only. **The exact v5 no-output probe passed; formal normal/kernel acceptance
is pending.** The publication parent is `7296a9659fbf34773ec03f437860c14073b3a638`. The existing Partition
canonical source stays at `19f59a09107d934a8230d58a11afd256dd6134d7e2bba958a4144331f191249c`.
The only canonical path added by this packet is the GroupLog module.

Selected v5 source: **10005 B / `dc2870dd9a94a2f6f1dfe3e8872e8c4ba3c541cb58ec3595fd406f1910db7f73`**.
Actual successful task: `job_82e632e67a414c9487d3f1512f4c950e`. Inner Lean, outer serializer and
completed lane all report exit 0. The exact original result is 4108 B /
`e021795904c208a227df7241b2723c253c716a0502558576c20cb1d700b98ecc`, its driver is 6158 B /
`3e402aedbd4c923499813ac9ec7c5ed7992f996d81d2e431b5726716cc3914a6`, and its raw Lean log is 1739 B /
`72cb0e44496fcda72b53492e745f580bb7b2ec2a781581b0d75657c36c524a85`. Warnings remain in the immutable original log.

All five attempts retain all 14 original files. The four earlier failures
have inner/outer/lane exit 1, and their exact predecessor links are preserved
through v5. The ten original preservation snapshots are byte-identical:
76025 B / `b3d9a52670b4414c6d1dc433600d8e41612f5e40d1780c18d00095d8062b08e1`. No probe built a dependency module
or requested an output object. The raw export manifest and task identities
are preserved in `GROUPLOG_RAW_EXPORT_MANIFEST.json` and `TASK_IDENTITIES.json`.

The original P1.5 registry remains **18/21** and the complete goal remains
open. No new owned/public count or axiom list is prefilled. Current source,
repair and static-review files are indexed in
[GROUPLOG_PUBLICATION_REVIEW_INDEX.json](GROUPLOG_PUBLICATION_REVIEW_INDEX.json).
The earlier v4 preparation README/index remain immutable under
`reviewed-unbound/`; they describe their original preparation-time state.

## Mathematical object and exact scope

The namespace is `ImbalancedChen.P5Z.OriginalGroupLogAbelVariation`.
The varying coefficient is the literal original-group logarithmic normalization
of the accepted physical Mellin profile:

\[
 G(y)=\frac{\Phi(y/U)\exp\!\left(i t\log(y/U)\right)}{H\log(Ay)}.
\]

In the intended HB application, `A` is the product of the other occurrences in
the same original HB group, and `H` is the product of the logarithms of the other
original groups. The logarithm therefore remains attached to its complete
original group. The Lean definition uses multiplication by the totalized
inverses `(H : ℂ)⁻¹` and `(Real.log (A*y))⁻¹`.

The final theorem, `normalizedProfile_variation_le`, has these assumptions:

- `Phi : ℝ → ℝ` is `ContDiff ℝ 1`.
- `M,D ≥ 0`, with `|Phi x| ≤ M` and `|deriv Phi x| ≤ D` for `x ∈ [1,2]`.
- `U,A,ell > 0`.
- `U ≤ u ≤ v ≤ 2*U`.
- `ell ≤ log(A*U)`.
- `t` and `H` are arbitrary real numbers.

Its conclusion is exactly

\[
 \|G(v)\|+\int_{(u,v]}\|G'(y)\|\,dy
 \le |H|^{-1}\left(\frac{M+D}{\ell}+\frac{M}{\ell^2}\right)(1+|t|).
\]

There is no added hypothesis `H ≠ 0`. At `H = 0`, the totalized inverse makes
both the coefficient and the displayed upper bound zero. The support and log
floor assumptions ensure that the varying factor `log(A*y)` is positive on the
relevant interval. The final public statement is unchanged from the original
source; its recorded statement SHA256 is
`9f78786947ed7f3b7b044c451347e85f271f08c11d76de2aaf28cab8236b727e`.
See [GROUPLOG_SOURCE_REVIEW.json](GROUPLOG_SOURCE_REVIEW.json) and
[GROUPLOG_ORIGINAL_INTERFACE.json](GROUPLOG_ORIGINAL_INTERFACE.json).

The proof computes

\[
 \frac{d}{dy}\frac1{\log(Ay)}=-\frac1{y\log^2(Ay)}
\]

and combines this with the accepted Mellin-profile derivative estimate. The
pointwise derivative budget is

\[
 \frac{|H|^{-1}}{U}
 \left(\frac{D+M|t|}{\ell}+\frac{M}{\ell^2}\right).
\]

The interval length is at most `U`, and the endpoint budget is
`|H|⁻¹*(M/ell)`. The final calculation adds the already nonnegative quantity
`|H|⁻¹*(D/ell+M/ell^2)*|t|` and proves the exact displayed budget by a ring
identity. These are analytic variation estimates. They do not supply a
Siegel–Walfisz estimate or cancellation of arbitrary coefficient prefixes.

## Manuscript and original source provenance

The manuscript reference is the 2026-11-06 version of
`UyNewNas/chen-imbalanced-semiprimes`, commit
`a988cba584d803ae2856a0de50efb582f4f3dd6a`.
The preserved local coefficient-appendix excerpt has SHA256
`267af54481f344e806d4cb3ad602aa7f32020b930845e2aa152b7daaa2f9a440`.
The source review records the corresponding passages on the original
`1/log n` attached to an HB group, logarithmic-coordinate Mellin separation,
partial summation, and retained original logarithms and profiles.

The original source path in `UyNewNas/goldbach-formalization` is

```text
docs/source-only/20261102-resume-30k/hb_group_sw/P5OriginalGroupLogAbelVariation.lean
```

Its canonical installation target is
`ImbalancedChen/P5OriginalGroupLogAbelVariation.lean`.
The exact original source is preserved as
[original-source.lean](original-source.lean):
9607 bytes, SHA256
`0cd74710f8ec890412e35e28e3985e9eceff6d52157b12a24c0873d9c50fe3d2`.
The original source-only manifest and registry are preserved in
[GROUPLOG_ORIGINAL_SOURCE_MANIFEST.json](GROUPLOG_ORIGINAL_SOURCE_MANIFEST.json)
and [GROUPLOG_ORIGINAL_REGISTRY.json](GROUPLOG_ORIGINAL_REGISTRY.json).
Their source-only status is historical evidence and is not changed in place.

The bounded prior-record review examined the original manifest, the original
source-only records, targeted later compilation summaries, and saved archive
indices. It found source-only copies but no same-source acceptance record for
this module in those inspected records. This is a bounded finding, not a claim
about every possible unrecorded environment. The fresh P1 inspection additionally
reported no target source, artifact, or owner at the selected runtime locations.
See [GROUPLOG_PRIOR_RECORD_REVIEW.json](GROUPLOG_PRIOR_RECORD_REVIEW.json),
[SAVED_ARCHIVE_INDEX_TARGET_SEARCH.json](SAVED_ARCHIVE_INDEX_TARGET_SEARCH.json),
and the main-thread readiness receipt from task
`job_f0705234f5e94214ae32cef092c39384`.

## Five preserved source revisions

| Revision | Bytes | Source SHA256 | Probe state at this preparation snapshot |
| --- | ---: | --- | --- |
| v1, exact original | 9607 | `0cd74710f8ec890412e35e28e3985e9eceff6d52157b12a24c0873d9c50fe3d2` | Actual exit 1; `job_82903d7db9f64614b58e4acf8bdcd896` |
| v2 | 9851 | `1f2dabefaaae151805ccf4e82b1f0d2695e8ee5d4859675c3e92aef8b1b367c5` | Actual exit 1; `job_d542ab673de745d6b66519f818c9bedf` |
| v3 | 9978 | `9f7063ffcf590a2a74e2613176489d725add60557a5458242a53f0aa71f631b7` | Actual exit 1; `job_f2e9daf032a4475687dc2c62942a2bac` |
| v4 | 9964 | `af2136380c1ef8010aedf97acf45f64c9a1453f751217dedf7cfe55b89238449` | Actual exit 1; `job_dbb5fffce613429ab41a8288ff6028ef` |
| v5 | 10005 | `dc2870dd9a94a2f6f1dfe3e8872e8c4ba3c541cb58ec3595fd406f1910db7f73` | Actual inner/outer/lane exit 0; `job_82e632e67a414c9487d3f1512f4c950e` |

The original failure exposed three independent issues: a non-progressing `simp`
step in the reciprocal-log derivative proof, an ambiguous real-derivative cast
in the normalized-profile helper, and final `nlinarith` normalization over
reciprocal denominators. The reported undefined-helper error was downstream of
the cast failure. v2 made the unfolding step optional, explicitly took the real
derivative before embedding it in `ℂ`, and replaced only the final tactic
calculation with endpoint-plus-integral inequalities, nonnegative slack and
`ring`. See [repair-v2/REPAIR_REVIEW.json](repair-v2/REPAIR_REVIEW.json).

The actual v2 failure then isolated composition normalization and conversion
side goals. v3 first stated an explicit `HasDerivAt` theorem for
`reciprocalGroupLog A`, normalized the composition, and used `convert!` for the
remaining scalar identity. It also adjusted the normalized-profile helper's
conversion. See [repair-v3/REPAIR_REVIEW.json](repair-v3/REPAIR_REVIEW.json).

The actual v3 failure showed a Real module-instance path mismatch in the first
helper and a remaining function equality in the second. v4 changes only two
lines from v3: the first `simpa` uses `using!`; the second helper ends with
`simpa only [normalizedProfile,Pi.mul_apply,mul_assoc] using! hh`.
See [repair-v4/REPAIR_REVIEW.json](repair-v4/REPAIR_REVIEW.json).

The actual v4 failure left a function equality because `normalizedProfile`
was folded on one side. v5 changes only that helper proof: `convert! hh using 1`,
function extensionality where needed, pointwise unfolding and the scalar ring
identity. The first derivative helper and complete final theorem remain
unchanged from v4. See [repair-v5/REPAIR_REVIEW.json](repair-v5/REPAIR_REVIEW.json)
and the exact successful original receipts under `probe/`.


All original declaration names, order and visibility are retained. The only
permitted declaration-header edit is

```lean
(deriv (reciprocalGroupLog A) y : ℂ)
-- becomes
((deriv (reciprocalGroupLog A) y : ℝ) : ℂ)
```

This is an explicit real derivative followed by its Complex embedding; the
original ambiguous header failed elaboration, so no equality to an already
elaborated original kernel declaration is claimed. No hypothesis or final bound
is added or weakened. All v2/v3/v4/v5 headers are byte-identical. The complete final
theorem statement and proof in v3, v4 and v5 are byte-identical to v2. Every original
and repaired source and every failed probe must remain preserved.

Each `REPAIR_REVIEW.json` is an immutable preparation record. Its `NOT_RUN`
field records the state when that candidate was authored; a later original probe
receipt is the evidence for its actual execution result.

## Accepted Variation dependency keeps its original identity

The new source has one direct project import:

```lean
import ImbalancedChen.Part3PrimeMellinProfileVariation
```

That dependency is already accepted under source commit
`f7e9219f4860a819758d52752c5a9309dd14a8c7`, source SHA256
`f57c040a86ad3bda56b21e5fe993a98157de89328862fd741523c3b00191263e`.
Its immutable acceptance adapter is
`docs/p1/20261127/p15-mellin-variation/run_variation.py`, SHA256
`1c132fefea799e8a3a3127defb07785138e3669e1f80beee2f5aa733b1914f50`.

The GroupLog operation must replay that original acceptance identity read-only.
It must not recompile Variation or rebind its receipt to the future GroupLog
source commit. The dependency graph for the new operation contains Variation and
GroupLog only; the unchanged accepted context supplies the existing Mathlib
stock. The direct-import preflight uses the original no-build helper for
Variation's `:olean` target and requires no newly built or failed module.
The preserved context and accepted objects are compared before and after the
operation. See the adapter review records indexed below.

## Probe completion and formal owner gates

The no-output source probe is independent evidence, not formal owner acceptance.
A successful worker `PROBE_RESULT.json` alone is insufficient: the worker can
finish before its serializer or outer dispatcher fails. The reviewed adapter
requires the original `serialized-probe-command.json`, `serialized-probe.log`
and `LANE.json`, and binds them exactly to their published bytes.

The checks require the original serializer and worker argv, original cwd,
successful outer exit, empty built/failed sets, correct log path/size/SHA256,
`VALIDATION_LANE_FINISHED`, the original state path and SHA256, and unchanged
serialization/guard flags. Original failure archives also bind their source
SHA256/size and the command's log path/size/SHA256. Existing evidence is replayed;
the probe is not repeated merely to replace missing outer-completion checks.

The independently reviewed unbound adapter, retained under `reviewed-unbound/`, has SHA256
`2d284fc343115aee2e1dc40fbca6c99030047f66032674ec824991102aeee448`.
Its earlier outer-completion and failed-archive binding findings are documented
in the immutable review progression:
[GROUPLOG_ADAPTER_REVIEW_B16C.json](GROUPLOG_ADAPTER_REVIEW_B16C.json),
[GROUPLOG_ADAPTER_REVIEW_8104.json](GROUPLOG_ADAPTER_REVIEW_8104.json), and
[GROUPLOG_ADAPTER_REVIEW_2D284.json](GROUPLOG_ADAPTER_REVIEW_2D284.json).
The bound adapter has SHA256 `9f618457ddd5dd25b251b153cf5f278bbf37ffead78247a034146efa95c49057` and differs only in the literal value of `INPUTS`.
The archived 5/5 local boundary-test report remains unchanged; those tests were not rerun.
Neither static review nor input binding is a formal acceptance receipt.

After actual exact-source probe evidence meets these gates, the proposed formal
scope is one new GroupLog owner. Fresh checks must reject an existing competing
owner, existing target artifacts or an unrelated installed source. Normal
compilation, kernel validation and the full owned/private/generated export audit
apply to GroupLog only. Actual audit counts and axiom lists must come from those
original receipts. The subsequent `--check` replays the immutable evidence
read-only without starting Lean or Lake.

The main thread must fill the following from actual evidence before claiming
formal acceptance:

| Evidence | Current publication value |
| --- | --- |
| v5 exact-source probe result and raw receipt hashes | Actual exit 0; exact original evidence bound above |
| Original probe serializer and lane terminal completion | Exit 0 and VALIDATION_LANE_FINISHED; raw evidence preserved |
| Original-evidence export completion | All 70 original files checked against their export manifests |
| Bound adapter SHA256 | `9f618457ddd5dd25b251b153cf5f278bbf37ffead78247a034146efa95c49057` |
| New source-publication commit | Pending root publication from parent `7296a9659fbf34773ec03f437860c14073b3a638` |
| New owner normal compilation receipt | Pending formal execution |
| New owner kernel-validation receipt | Pending formal execution |
| Full owned/private/generated audit, actual counts and axiom list | Pending formal execution |
| Protected source/object/context preservation | Pending original formal receipts |
| Read-only acceptance replay | Pending original formal receipts |

## Downstream consumers and remaining scope

The existing source-only consumer chain includes:

| Consumer | Intended use of this variation estimate | Acceptance carried by this package |
| --- | --- | --- |
| `P5ActualHBGroupLogLine` | Actual occupied row, original group/log dictionary and log floor | None |
| `P5ActualHBGroupLogAbelPrefix` | Exact Abel estimate against the computed finite prefix maximum | None |
| `P5ActualHBAuxiliaryGroupLog` | Auxiliary-coprime normalized prefix estimate with the exact coprime mean | None |

Their original source paths and use sites are recorded in
[GROUPLOG_SOURCE_REVIEW.json](GROUPLOG_SOURCE_REVIEW.json). Their own sources,
imports, prior acceptance status and formal checks remain separate obligations.

This estimate retains the original logarithms and pays the Mellin frequency
cost. Complete normalized HB SW still needs cancellation of the actual original
role prefixes, auxiliary-coprimality and divisor-loss bounds, separated mode and
profile accounting, full source-rank coverage, and the relevant reserve payments.
This package establishes no prime/rough SW claim, no Weighted/Scaled/Mellin
interval acceptance, no full `hSmoothSignedPP`, and no complete same-rho PP result.
The original P1.5 status remains **18/21**, with the complete goal open.
