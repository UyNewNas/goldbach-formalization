# H430 causal smooth boxes — P deduplication and local moving-start repair

Status: **OPEN** for the original common arithmetic smooth-box realization and yellow node `P5.6.eight_suppliers`. One genuinely missing local dictionary and absolute error estimate is supplied in source form. `compiled=false`, `kernel_verified=false`, `formal_credit=0`, `task_complete=false`, `ready_to_install=false`. All finite proof bodies and guards are **UNEVALUATED**.

Only the assigned P directory was written. No Lean/lake/compiler, proof-guard evaluation, numerical replay, Git operation, CI dispatch, installation, or child agent was used. The O directory is unchanged. Its three Lean files were read in full; it contains no REPORT or REGISTRY to inherit.

## Deduplication and exact reuse

The BRIEF and PRIOR_TASK were read before writing. Searches of production and prior source-only files found no existing moving-start atom or moving-start L1 estimate for this graph. The existing O results and the M simple approximation are reused, not rewritten.

| Existing source (repository-relative) | Exact reused declarations | SHA-256 |
| --- | --- | --- |
| `docs/source-only/20261102-resume-30o/h430_smooth_causal_boxes/Part5OriginalH430CellMeasurability.lean` | `commonCell_measurable`:33; `fullCell_measurable`:80; `rootCell_measurable`:135; `measurable_frozenLevel`:160 | `8c5d0d4f4c817c8b16dccfaae4b0d2f62c633db099e1a892da1a8303d5db7072` |
| `docs/source-only/20261102-resume-30o/h430_smooth_causal_boxes/Part5OriginalH430NativeQueryPaths.lean` | `W1_components_exact`:43; `W2_components_exact`:48; `actual_child_query`:88; `nativeRank_exact`:148; `actual_ancestor_choice`:214; `occurrence_query_exact`:235 | `118c03b4a44068a8cbb696f39699d12ff83b84d95a46f6d77b07b109f440cdeb` |
| `docs/source-only/20261102-resume-30o/h430_smooth_causal_boxes/Part5OriginalH430RootGateObstruction.lean` | `source_U3_tail_not_fullGates`:36; `tail_no_full_square_realization`:81; `original_tail_open_interval`:92 | `d2897afbf9efc91f35a3d911dce5e826578daa5b967cf90ff49d37c74633f72b` |
| `docs/source-only/20261102-resume-30m/h430_common_approximation/Part5OriginalH430AbsoluteQueries.lean` | `data`:84; `atomSet`:120; `actual_query_integral`:142; `queryError_tendsto`:159; `queryError_zero_mass`:199 | `66f3223b1d05776561349063a48e00cd0cd90b54be2081c676565b729bd47b13` |
| `docs/source-only/20261102-resume-30m/h430_common_approximation/Part5OriginalH430GeometricWalls.lean` | `fullCell_keeps_equality`:132; `totalAbsoluteError_tendsto`:147; `exists_one_total_absolute_stage`:154; `exists_one_nested_absolute_stage`:170 | `2732c16e9b1c0b6d7d07cdbe59ae4073271dd8e639c38aacd609450aee966284` |
| `ImbalancedChen/P5PresievedRoughSmoothBoxAtoms.lean` | `cover_sandwich`:74; `contDiff_atom`:104; `exists_atom_derivative_budget`:132 | `17472a95606023fc7250f944a87a47ceac7bd81bd062773825b7a62709edb9e1` |

The M PhysicalRoots and FrozenRootRefinement sources, their REPORT/REGISTRY, and the N review were also inspected. Their root floors, cumulative common-Q mesh and retained clamp are already implemented. The existing smooth atoms are separated smooth functions with derivative budgets; this is not yet a theorem that those atoms realize the joint H430 physical query cells. REGISTRY pins the relevant concrete domain, kernel, node and transition sources as well.

## New source and eliminated local obligations

New source: `Part5OriginalH430MovingBuchstabAtoms.lean`; intended module `ImbalancedChen.Part5OriginalH430MovingBuchstabAtoms`.

The exact missing O premise is visible in NativeQueryPaths:96–128. For Buchstab queries, `StartMatches n q` requires the actual parent argument to equal `upperStart i` or `lowerStart i`. In contrast, PhysicalTransition:61–68 defines the literal local domain using the actual argument. M AbsoluteQueries:68–69,102–108 defines only fixed grid starts. Neither arbitrary continuous parents nor a preceding conservative transport are identified with those fixed starts by O.

The P file supplies these source proofs:

- `movingDomain`:34 keeps the actual Buchstab start from `n.argument`; W1/W2 domains, all profiles and density functions are exactly the existing ones. `actual_child_moving_domain`:67 and `actual_child_moving_atom`:95 need the literal `LocalDomain` only. They remove `StartMatches` from the local child-domain and table-atom dictionary, without postulating an arithmetic realization.
- `occurrence_moving_atom_exact`:112 uses the existing `realize` and `occurrenceInput` at `GraphVertex mesh 440`. Thus the parent is the actual computed Program prefix at any of the 441 labels. This does not select the immutable producer's history or prove that arbitrary Program paths are licensed arithmetic families.
- `movingDomain_measurable`, `movingAtomSet_measurable`, and `movingAtomDensity_measurable` prove measurability for each fixed physical parent. No joint physical-prefix measurability or smooth refinement is claimed by these fixed-parent statements.
- `startAtomDensity_difference_le`:159 bounds the difference of the two literal Buchstab atom densities by the indicator of the closed interval between their starts. Both atom densities and their absolute difference are proved integrable at lines 133 and 187. `startAbsoluteError_bounds`:194 then proves the actual absolute integral is at most the length of that interval. The density used is exactly `buchstabKernel w = 1 / max 1 w`, and its existing pointwise bound by one is used; the desired error is not a premise.
- `actual_upper_start_absolute_error`:213 and `actual_lower_start_absolute_error`:226 specialize that estimate to the actual moving domain and the original fixed primitive, giving respectively `L1 error ≤ |n.argument-upperStart i|` and `L1 error ≤ |n.argument-lowerStart i|`. The upper proof includes the max-two start through its 1-Lipschitz bound.
- `upper_constant_start_exact`:236 proves exact equality throughout the constant upper-start branch, for every original closed table atom, without requiring equality of the two parent parameters. The separate U3 root clamp and its adjacent-cell minimum remain the reused M/O construction.
- `lower_start_two_open_strip`:247 identifies the nonempty interval `(1,51/50)` in the moving lower domain at start two and outside every old fixed lower primitive domain. This is an exact domain fact only. It is not a claim that every point in the interval occurs in a licensed arithmetic path, or a counterexample to the manuscript's conservative closed-cell construction.

These estimates are conditional-scale, normalized one-dimensional Buchstab estimates at a fixed physical parent. They are not an integral over the parent prime family. The old grid spacing is fixed at `1/50`; finer simple-function or root-Q labels do **not** make `|s-s_grid|` tend to zero. Consequently this source alone cannot supply an arbitrary prescribed `delta` for all continuous parents. A correct causal moving-domain refinement or a source-justified conservative table transport is still needed.

No new primed occurrence is added or merged: the existing `FeedbackQuery` label, Program and FloorAtom stay in the theorem. Identical masks with different labels are not summed as additional alternatives. The two W1 coefficients, nine W2 component entries, native prime arities, ancestor prefix choices, full/selected tests and scalar multiplicities are inherited unchanged.

## Governing evidence and remaining construction

The manuscript hash remains `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`.

- Lines 857–865 require preceding generations, maxima of alternatives, closed support minima and the seed-only430 history.
- Lines 867–877 require one nested finite refinement, transition norm12, root norm7/2, error factor `(12^441-1)/11`, a fixed positive leaf cutoff, and absolute treatment of zero-mass cells.
- Lines 887–895 retain the positive-measure root clamp and labelled positive switched costs.
- The original completion module, hash `8597fd1dc01d3fc49e5b31d28afeab3cf48e88ae23908fb6777a1c23f5b360e5`, lines 272–289 asserts the causal positive-parent refinement and its common table-graph extension. The new local estimate does not establish that assertion for all physical descendants.

The existing O root obstruction must retain its narrow meaning. M PhysicalRoots:40–43 stores the external selected root exponent `t` as the first chronological slot and sets total level `t+R(t)`. Existing `fullGates` then tests `2t≤t+R(t)`. On the original U3 tail `R(t)=1/2-t-tau`, this requires `2t≤1/2-tau`, whereas `t≥57/224>1/4`. O already proves this failure, its persistence under root lowering and descendant append, and a nonempty open interval. Repeating that proof would add nothing.

This is a **source-model interface obstruction**, not a manuscript counterexample. The original module lines 184–197 explicitly distinguishes enhanced states with full/selected squares from classical complete levels below half; lines 254–256 assigns the U3 tail the below-half limiting route. A corrected classical/enhanced root-source dictionary needs a real arithmetic licence. Merely dropping the failed full square would not establish it.

The following requested obligations remain OPEN:

1. Construct the joint physical-prefix pullbacks, including moving starts or justified conservative transports, as one finite nested smooth prime-box family chosen before N. Existing finite simple labels and generic smooth atoms do not give this association.
2. Prove causal ancestor ownership, all full/selected gates and literal equality/clamp branches on that family, including the justified classical U3 tail source. The P file neither changes the node model nor discards an old gate.
3. Supply the actual positive switched-leaf/source dictionary for D5-bad and Gamma9–21, including all multiplicities. These are not ordinary feedback children.
4. Integrate the local errors with the actual parent physical density and Jacobians, account for the finite query/atom/coefficient occurrences, and identify the resulting sum with the original recursion's `localBudget`. The M sum over `Fin441 × Primitive × FloorAtom` is not such an identity.
5. Bind that arithmetic family and error budget to the immutable seed-only430 predecessor history. The exact norm12, norm7/2, depth440 and factor `(12^441-1)/11` are neither changed nor claimed newly instantiated.

The local deduction is difficulty class **(2), fillable omitted deduction**, now supplied in source form. The complete common arithmetic approximation remains a potentially substantive missing construction at the formal source boundary, class **(3)**; no mathematical contradiction in the manuscript has been proved. The remaining Lean expression/API risk is class **(1)** because nothing has been elaborated or compiled.

## Static checks and review limits

All newly used integral APIs were inspected in local Mathlib source: `integral_mono`, `integral_indicator_one`, `Integrable.abs`, `Real.volume_real_Icc_of_le`, and `abs_max_sub_max_le_abs`. The interval-length proof explicitly splits the order of its endpoints, avoiding an orientation-sensitive max/min absolute-value rewrite. The parent-assigned reviewer independently checked the local mathematics and emphasized the fixed-grid limitation, which is recorded above; this is not kernel verification.

The intended toolchain is `leanprover/lean4:v4.33.0-rc1`, and the repository manifest pins Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Only source text was read. The new direct project import is still source-only at O; its intended `ImbalancedChen/Part5OriginalH430NativeQueryPaths.lean` installation path is absent. Existing M/O prerequisites must be handled before installation. Presence of any other production file supplies no inherited compilation credit.

Static scans found no admissions, new axioms, `native_decide`, evaluation directives or compiler invocations in the new file. Hash and declaration-line checks were performed without executing any proof. REGISTRY records the new file, direct imports, source provenance, hashes and all negative verification statuses.

