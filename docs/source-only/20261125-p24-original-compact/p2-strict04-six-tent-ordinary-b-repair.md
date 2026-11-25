# Strict 04: ordinary six-tent and baseline B proof repairs

Status: **SOURCE_REPAIR_PREPARED / FRESH_LEAN_CHECK_PENDING**.

P2 task `1cd8f8cb588f4df1a9a9007c22fe7314` checked source `f5d007b8`.
Its complete `p2-strict-symbolic-04.log` is 20,768 bytes, SHA-256
`9e2e3ff4e18c6f1b2ee5f7e1efba1210a767aae9fe66b423913e65dbc7751096`.
The run finished with 276 of 319 symbolic modules successful. The previous
SixTent finite-index and rational-power errors were absent; the remaining
failures addressed here are proof presentation and explicit transport steps.

## Frozen semantics and existing proof work

The already frozen 1106 `certify_extended_prefix.py` was rechecked at its
ordinary rectangular mass, affine-cap candidate selection, and OLD/NEW
query/chord branches. Its SHA-256 is
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`,
from manuscript source `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.
The original B tuple remains `(153, 0, 0, -96, 256)`, giving the exact OLD
endpoint numerator `153*D - 256*x - 256*y - 352*z` and denominator `256*z`.
The ordinary geometry, residual positivity, `low >= 2` chord branch, full
mass and query clamps are unchanged. This is a semantic correspondence to
the frozen producer, not a new claim of byte identity with another historical
P160 script.

The scalar-inequality proof reuses the explicit multiplication-and-`ring`
pattern already passed in `ActualThirdOriginalPositive256LogIntegerGuards`
and reused in the recorded compact05 range32 repair. The NEW-query repair
uses the same rational-power normalization that removed SixTent's previous
query error. The historical 256-term logarithm and range-32 implementation
are unchanged.

## Local changes

| Proof site in input source | Change and classification |
|---|---|
| SixTent mass proof, line 87 | Run `field_simp` and then `ring` sequentially, matching the actual `unnecessarySeqFocus` report. |
| SixTent `ordinary_raw_not_symmetric`, line 106 | Preserve `hbBind` in the public header and use it to prove the upper-coordinate equality. Together with the lower-coordinate equality, transport `hab 0` to `a 1 < b 1`, then contradict `hyx`. Both stored-row bindings are used in the proof; no dummy reference or linter exception is added. |
| Ordinary B saved guards, lines 138/143 | Multiply each existing upper bound by nonnegative 128 and prove `128*((25/128)*D) = 25*D` by `ring`, retaining the existing `exact_mod_cast`. This supplies elementary algebraic transport that the failed `linarith` calls did not establish. |
| Ordinary B NEW query, line 197 | Add `Rat.cast_pow` and `Rat.cast_ofNat` to normalize the outer rational-to-real cast of the P160 denominator. The reader and unreduced query operands remain unchanged. |
| Ordinary B grid consumer, line 259 | Include `realBox` in the existing `simpa only` so that the coordinate is explicitly the real cast of the stored rational coordinate. This is definitional unfolding. |

The log also records the old B source's baseline-only
`unnecessarySeqFocus=false` exception. Editing that source removes its
eligibility for the exception. Its sole `field_simp <;> ring` in
`literalBEndpoint_eq_bLowQ` is therefore changed to the same sequential form;
this anticipates that recorded gate transition rather than claiming a new
compiler error. No runner, option, or gate was changed.

## Static preservation and identities

Comment-aware comparison against `f5d007b8` confirms unchanged imports,
20 public theorem headers, one private theorem header, and six complete
computational definitions. The two files retain their original EOF styles.
`git diff --check` passes. No hypothesis, admitted proof, axiom, native
evaluation, unsafe declaration or linter setting was added.

| File | Before SHA-256 | Candidate SHA-256 |
|---|---|---|
| `ActualThirdOriginalSixTentOrdinaryMassCeil.lean` | `6496f104ab08e8c3d177966f91f6d64c3850dff2c06de2b0fa31c851052b120d` | `49173ea1b67b9ae30c75507a40ed743aa0ed5daf179b4d185103ca6fc033a946` |
| `ActualThirdOriginalP4AOrdinaryBCandidateLeaf.lean` | `8197219a2a96f2cc8ca6cf8ed3b5eded45c7bd1460209fd726ff81d83a97b52b` | `7d4cb8638daca6d3d23210b5b874655511e085facc7e921356881da614146a8f` |

These candidates have not been compiled. No remote task, index operation,
commit, or running P2 input was changed. This record grants no new compilation,
kernel, finite-check, or endpoint-completion credit.
