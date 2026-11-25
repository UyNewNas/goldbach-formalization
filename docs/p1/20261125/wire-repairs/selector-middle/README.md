# Wire selector and middle-bin expression repairs

These are source-only repairs for two owners that failed their first actual
normal build in task `job_de5637e9cbe04bde8fbde4e259c08ff4`. The failed
sources were commit `220c14630ffd266f824bdbf0977147ecb740c0dd`; the caller used
catalog commit `4f7a975211bdbdccc76adc14734aa2de4a13b6ad` and the existing
accepted runtime configuration. No compiler was invoked for this repair,
and neither source is newly accepted by this note.

`REPAIRS.json` embeds all eight complete target-error sections, their exact
original log locations, the normal command outcomes and log hashes, donor
receipt scopes, manuscript references, and before/after source fingerprints.
The diagnostic input was the coordinator's complete
`p1-wire-complete-failures.json`, SHA256
`b342fa1e13a709d4433252232f66d023fe0e4df2defdf337327e31db0bfb4e4d`.
It is distinct from the shortened error excerpts in the streamed task output.

## Changes

| Owner and original line | Actual failure | Proof-expression correction |
|---|---|---|
| RawBoxSelectorEquivalence 80 | Eligibility metavariable unresolved in `finiteMax_row_le` | Give the decoded family, eligibility predicate, value function and inherited seed explicitly. |
| MiddleShellBinMoment 145 | Addition lemma places the fixed `1` on the wrong side | Use `add_le_add le_rfl`. |
| MiddleShellBinMoment 152, 165 | `ring` runs after `field_simp` has already closed the goal | Remove the two trailing tactics. |
| MiddleShellBinMoment 158 | `nlinarith` does not identify differently arranged products containing division | Compose the existing bound with `sub_le_self`, then the existing monotonicity inequality; prove only the final algebraic identity with `ring`. |
| MiddleShellBinMoment 167 | The target has `2*C` while the multiplication lemma expects `C*2` | Commute that terminal product before applying the existing inequality. |
| MiddleShellBinMoment 228 | Scalar extraction is still under a finite sum | Use `Finset.mul_sum`, `Finset.sum_congr` and a pointwise commutative identity. |
| MiddleShellBinMoment 229 | Five-factor normalization leaves a proposition containing a `True` disjunct | Reuse the accepted four-dimensional donor's `simp <;> ring_nf <;> simp` pattern with the unchanged five factors. |

The selector application follows `fifth_row_le_exponent5` in
`P1OriginalVariableFifthContinuation`, accepted with all 54 owned exports in
batch58. The finite-product normalization follows
`original_bin_boxMass_eq_prefix_cube` in `P1OriginalFourthFiniteBinBudget`,
accepted with 10 owned exports, including 7 public, in batch61. The scalar
extraction follows `weightedBinMass_le_prime_box` in
`P1OriginalFourthSmallBinWeightedMass`; its examined batch43 receipt proves
normal/kernel and 14 public exports. The imported moving-interval supplier
has the same normal/kernel/public scope in batch45. This note does not
upgrade either public-only receipt to full-owned acceptance.

## Manuscript and scope

The pinned 6 November manuscript is commit
`a988cba584d803ae2856a0de50efb582f4f3dd6a`. The reviewed passages are the
selected-branch licence and tent maximum, the fifth-rank saving and envelope
(`sv:branch-licence`, `sv:tent`, `sv:odd-gain`, `sv:fifth-envelope`), and the
finite-policy realization proposition and its cutoff/refinement proof
(`sv:finite-realization`). The upper-enclosure paragraph after the numerical
table records complete parent/child comparisons and telescoping.

The middle-bin bound is an existing internal finite helper; the manuscript
does not separately state its exact auxiliary formula. These changes only
express its existing interval and finite-sum/product steps. They introduce
no new analytic supplier, alternative policy, nontrivial omitted derivation,
or identified mathematical gap. Inherited decisions, all selected/decoded
rows, the original carrier, lower cutoff, strict ordering and geometric
conditions are retained.

## Static checks and next gate

All 7 selector theorem headers and 4 definitions, and all 4 middle-bin
theorem headers and 7 definitions/abbreviations, match source220 exactly.
Imports and options are unchanged. No `sorry`, axiom, admitted proof or
`native_decide` was introduced. The two-file patch SHA256 is
`4f9971ff384b14dacd17b15be434fa8506ed92b3d63edf5303db5b3dd5039c4f`.

| Source | Before SHA256 | After SHA256 |
|---|---|---|
| `P1OriginalFifthRawBoxSelectorEquivalence.lean` | `3707791879eee213ff78fb2ecd9cb6ddf1597216228a5238f944b455f49f008a` | `536842ff9f2a8104c35715e58ffd052c67dcefe6bdf40d669ee43e38fa7f232c` |
| `P1OriginalFifthMiddleShellBinMoment.lean` | `bad01bfe21b22ecacdcc70b0d9028d62bf7621c185e56d9a28609c1f1cabdc61` | `8420b482af86e46757d712a39ae7d83abd7f8a7c36356dcf392fe7dcff12182f` |

Root owns publication and the next normal/kernel/full-owned validation.
Shared dependencies, actual runtime configuration, resource limits and the
frozen Wire caller were not changed by this task.
