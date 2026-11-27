# P3.4 Existing Dyadic Source Assembly Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. This is a read-only implementation handoff. Root has now authorized Task 3 to proceed through its assigned worker. The author of this plan has not implemented or compiled this unit and has changed no project source.

**Goal:** Reuse the existing proofs that the actual finite source decomposes by primary multiplier, output sign and output dyadic scale, with exact beta-energy accounting and the genuine short-index endpoint.

**Architecture:** Prefer two lightweight modules, preserving every existing public qualified name and statement. Their inputs are Task 1's packet coefficient core and Task 2's finite primary/source core. Leave actual-mode specializations and common-completed-variable consumers in the old parent modules; this avoids moving or repackaging existing accepted common-interval interfaces.

**Tech Stack:** The repository's pinned Lean/Mathlib and root's strict-compilation / leanchecker / full inventory / transitive-axiom gate. No new analytic or spectral foundation.

**Spec:** Root's request for an exact, nonduplicative migration scope; `/workspace/scratch/dcb7c80f70a4/p34-after-primary-boundary.md`; the frozen manuscript `/workspace/scratch/dcb7c80f70a4/analytic-appendix-1106.tex` from manuscript commit `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`.

## Global Constraints

- All project paths below are under `/workspace/library-files/p34-proof-work/` unless absolute paths are given.
- Donor-source snapshot inspected at checkout HEAD `a2332ed58aea9ed41363c4366a96c301ef5d7989`. Root subsequently confirmed Task 2 source `2b284342fce23962a1b431d8003cb5cdffac8128` (the same source tree) passed both local and P3-cloud gates: 43 stages, four modules, 63 declarations; independent review also passed. This status was supplied by root and was not rerun by this plan author. It is prior evidence, not a substitute for the new joint import-closure gate specified below.
- Reuse an existing sound acceptance for the exact objects and source if the independent audit finds one. In that case do not migrate or reprove this unit merely to create another wrapper.
- Public qualified names, complete theorem types, source definitions and gates are preserved. Moved declarations must be removed from their old active defining module, which then imports the new module.
- The only proposed visibility change is the existing private `finite_singleton` helper, explained below. Its proof and type remain unchanged; report the change of defining/private name honestly.
- Do not change `CoprimePacket`, invent another source/packet structure, or add hypotheses expressing the desired support, coprimality, energy identity, or spectral conclusion.
- Do not modify or move the six accepted P3.1 owned declarations or the existing `CommonCompletedVariable` / `weight` definitions for this two-module scope.
- Do not compile the old large parent modules and claim that such a result follows from the new-core gate. Parent compatibility and actual-mode acceptance remain separate scopes.
- No `OriginalData`/`FixedBlock` reconstruction, actual M2 source closure, Fourier-to-`R(n)` identification, ABL spectral identity, spectral gap, Plancherel or whole-P3.4 claim.

## Review Focus

1. `|y|=1` belongs to dyadic key `j=0`, with scale `1/2`; strict lower and closed upper bounds must stay unchanged.
2. Negative `y` retains its sign flag; `signedY_div` recovers the natural quotient only after the positive multiplier is established.
3. Empty fibres and beta cancellation do not produce witnesses. Nonzero-beta endpoint bounds keep their original nonvanishing premise.
4. Distinct computed blocks partition joint **output** fibres. Exact beta-energy equality is not a triangle inequality and incurs no new block-cardinality factor.
5. The existing common variable and physical/spectral suppliers are not smuggled into the light closure or treated as proved by the generic finite identities.

---

## 1. Reuse audit before any migration

### Evidence already examined

The independent audit reports that:

- P3.2 source `34201be0` has neither donor among its 130 source paths, and its six target-module / 138-owned-declaration inventory contains neither donor namespace.
- P3.1's accepted `Part3CommonCompletedInterface` and the P3.5 accepted scopes do not own either donor namespace.
- The two exact donor files first appear in the checked history at `29a0717b23cbab3a4bfb5f9066b815c181b3efa4`, with explicit source-only / uncompiled status. A targeted search for any independent earlier sound receipt was being finalized by the audit agent; this plan does not claim universal nonexistence of other evidence.

Directly read local corroboration:

`docs/source-only/20261024-code-only/batch2/source-manifest.json`, entries beginning at lines 9047 and 9061, binds both exact SHA256 values below and marks both `SOURCE_ONLY_UNCOMPILED_ZERO_PROOF_CREDIT`.

| Donor | SHA256 of inspected file | Git blob at observed HEAD |
|---|---|---|
| `ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean` | `8d8f41a161cf423e3944863cdf7ae8304c1536315a72b198cd6ae4eab8b6dd10` | `7b3374576687df50307ef847aa51e9fef15dddae` |
| `ImbalancedChen/Part3ZActualPrimaryDyadicAssembly.lean` | `20fd20a906072b054fdfd65ba8cada3c1f8504a73d15b2455040dec0f346f935` | `3a12da5b72eeddd3558c4714eecd7754cd660a55` |

The assembly manifest also records an earlier draft ownership-source hash; use the deployed file hash `20fd...` above for this migration, not that different draft hash.

### The existing P3.1 common interface is not a replacement for these finite results

The inspected accepted interface source is:

`/workspace/scratch/e4b706aea1e3/goldbach-p31/ImbalancedChen/Part3CommonCompletedInterface.lean`

SHA256: `2d2b50e2547cbb98daf5b9cdd23892c9885cb42c1fa7fa49f02d1a60213d12a2`.

Its public source theorems are:

- `sum_weight_mul_eq_sum_inter`;
- `weight_weightedEnergy_le`;
- `packet_weightedEnergy_le`.

They supply common interval clipping and a weighted-energy bound from the explicit full-uniform energy input. They do not prove the computed primary/sign/dyadic partition, exact beta-energy identity or short-index endpoint. Reuse them when their consumers need those bounds; do not reproduce them in this new unit.

The interface imports `Part3DistributionTargets` and `Part3ExceptionalWeightExtension`. It therefore is not a lightweight import shortcut to the common-variable definition.

Its provider at P3.1 source `3624fefd` is:

`/workspace/scratch/e4b706aea1e3/goldbach-p31/ImbalancedChen/Part3DistributionTargets.lean`

SHA256: `a0b43f877bb7bcdf7606e19281521a0165538c08c0495a2a3e2d58b66aeb08cc`.

The `CommonCompletedVariable` and `weight` declaration text was compared directly with the current checkout and is identical. These are provider-owned objects, not two newly proved P3.1 owned declarations. The historical provider evidence and the six consumer-owned declarations should retain their existing ownership/provenance. No migration of these objects is necessary in the recommended scope.

### Stop rule

Before edits, root consumes the independent audit's final bounded conclusion. If a sound receipt covers either donor or the exact needed conclusions, replace that part of this plan with reuse of the accepted result and its real dependency closure. No new wrapper is justified simply because it would be easy to prove.

## 2. Recommended two-module topology

Root-authorized Task 3 worker should create:

1. `ImbalancedChen/Part3PrimaryDyadicShortEndpoint.lean`.
2. `ImbalancedChen/Part3PrimaryDyadicAssembly.lean`.

Neither path existed when checked. Preserve the **old declaration namespaces**:

- `ImbalancedChen.P3ZActualPrimaryShortEndpoint`;
- `ImbalancedChen.P3ZActualPrimaryDyadicAssembly`.

Expected project imports:

| New module | Necessary project imports | Why |
|---|---|---|
| `Part3PrimaryDyadicShortEndpoint` | `Part3FixedRhoPrimaryFiniteCore`, `Part3CoprimePacketCoefficients` | Literal `Source`, output/beta, primary fibres and gates; existing packet, mode, `D4`, cusp phase and its norm |
| `Part3PrimaryDyadicAssembly` | `Part3PrimaryDyadicShortEndpoint` | All finite source and packet definitions needed by the assembly and its endpoint consumers |

Expected pinned Mathlib imports are the existing `Mathlib.Tactic` for the first module and `Mathlib.Data.Nat.Log` / `Mathlib.Tactic` for the second. Narrowing tactics further is optional and must not distract from the actual project-closure goal.

Task 2's `Part3FixedRhoPrimaryFiniteCore` already imports `Part3PrimaryPrimeSupport` and `Part3LiteralReciprocalSource`. Its fourth module, `Part3LiteralPrimaryOldformArithmetic`, is **not** needed by these existing proofs; do not import it just to force an apparent dependency. Task 1's `Part3CoprimePacketCoefficients` already supplies its original `FourierModeIndex`, `CoprimePacketCore`, and `CuspPhaseCore` dependencies.

No core import of `Part3DistributionTargets`, `Part3CommonCompletedInterface`, `Part3ActualLiteralPacketIntegral`, `Part3FixedRhoPrimarySignedFiniteDecomposition`, or the actual-mode counting/Poisson modules is needed.

### Exact joint acceptance order: nine fresh project modules

The verifier permits only project modules rebuilt earlier in the same run, or the fixed external roots. Therefore the joint Task 3 gate must rebuild and replay all nine modules in this exact topological order, not just the two new files:

| Order | Module | Immediate project dependencies allowed at that step |
|---|---|---|
| 1 | `ImbalancedChen.Part3FourierModeIndex` | None |
| 2 | `ImbalancedChen.Part3CoprimePacketCore` | None |
| 3 | `ImbalancedChen.Part3CuspPhaseCore` | None |
| 4 | `ImbalancedChen.Part3CoprimePacketCoefficients` | 1, 2, 3 |
| 5 | `ImbalancedChen.Part3PrimaryPrimeSupport` | None |
| 6 | `ImbalancedChen.Part3LiteralReciprocalSource` | None |
| 7 | `ImbalancedChen.Part3FixedRhoPrimaryFiniteCore` | 5, 6 |
| 8 | `ImbalancedChen.Part3PrimaryDyadicShortEndpoint` | 4, 7 |
| 9 | `ImbalancedChen.Part3PrimaryDyadicAssembly` | 8 |

At every step, use actual Lean-resolved imports, not a source-text regex. All project-object paths resolved by that module must belong to the already-fresh portion of the list; fixed pinned Mathlib/Lean/package roots remain allowed. Reusing the old source and proof bodies is intentional. Replaying the new nine-module import combination is necessary verification, not duplicate proof development.

Perform nine strict compilations and nine leanchecker replays. The final audit inventories all nine defining modules against their serialized objects and transitive axiom dependencies. Do not restrict it to the newly authored source-level declarations.

**Generated names require explicit ownership checking.** The same public definitions keep their names after relocation, and Lean may generate or expose equation lemmas while compiling a later consumer. Record each serialized constant, its actual defining module and its type/source binding. In particular, do not retain an old heavy parent object to supply a same-named generated declaration, silently ignore a duplicate, or assume that the new serialized inventory is the sum of prior source-level counts. Include `CoprimePacket` generated declarations, `transformedCoefficient`/mode equation lemmas, aliases, and the newly public `finite_singleton` according to the actual inventory produced by the gate.

Exclude the six other cusp modules from the old seven-module acceptance:

- `Part3Gamma0ActualCusps`;
- `Part3CuspScalingMatrices`;
- `Part3ActualCuspWidthNormalization`;
- `Part3CuspTranslationFourierPhase`;
- `Part3ActualCuspFourierSection`;
- `Part3SignedCuspFourierSection`.

Also exclude `Part3LiteralPrimaryOldformArithmetic`, `Part3OldformCuspPhase`, `Part3ActualCuspScalingSourceOnly`, `Part3ActualCuspPacketPairing`, the full old endpoint/assembly parents, and the common-completed / actual-mode heavy parents. None is a dependency of the selected finite unit. The only old cusp-scope dependency used here is the elementary `Part3CuspPhaseCore` needed by the existing packet norms.

The acceptance runner must pin the exact **new joint source commit** containing the two added core modules. Prior Task 1/2 commit receipts cannot replace this same-run closure validation. A final inventory count is determined by the actual nine-module audit; do not publish an anticipated count computed from previous receipts.

## 3. Exact migration inventory: short endpoint core

Donor: `ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean`.

Move the following **20 source declarations**. Nineteen are currently public, and `finite_singleton` is currently private. Full binder lists and result types are copied from the donor, not reconstructed from this summary.

All are under namespace `ImbalancedChen.P3ZActualPrimaryShortEndpoint`.

| Declaration, donor line | Type/role to preserve | Immediate proof or definition dependencies |
|---|---|---|
| `signedY`, 24 | `Bool -> Nat -> Int`, returning the selected signed integer | Existing `if` and integer cast |
| `signedY_abs`, 26 | Real absolute value of the selected signed integer equals the natural input | `signedY`; two Bool cases and simplification |
| `signedY_natAbs`, 29 | Integer `natAbs` equals the natural input | `signedY`; two Bool cases |
| `signedY_div`, 32 | For `0 < nu`, signed `nu*n` divided by `nu` has `natAbs=n` | `signedY_natAbs`; `Int.mul_ediv_cancel_left`; casts |
| `dyadicSource`, 41 | Literal filter of `primaryFibre rho (nonzeroSource S) nu` by `U < |y| <= 2U` and the sign | Task 2 `Source`, `output`, `primaryFibre`, `nonzeroSource` |
| `dyadicBeta`, 47 | Existing beta on that filter at `(z, signedY negative y)` | `dyadicSource`, original `beta`, `signedY` |
| `dyadicSource_subset`, 51 | The restricted source is a subset of the original `S` | Three existing filter memberships |
| `dyadicBeta_source_witness`, 56 | Nonzero coefficient gives a genuine source member with the specified output | Task 2 `beta_ne_zero_mem_image`, `Finset.mem_image` |
| `dyadicBeta_support`, 62 | Nonzero coefficient has `U < y <= 2U` | The witness; `signedY_abs` |
| `dyadicBeta_multiplier_pos`, 70 | Nonzero coefficient implies `0 < nu` | The witness; actual primary-key equality; `rhoPrimaryNu_pos` |
| `dyadicBeta_coprime`, 77 | Nonzero coefficient at `nu*n` implies `n.Coprime rho.natAbs` | `primaryFibre_gate`, multiplier positivity, `signedY_div` |
| `nonempty_endpoint_bounds`, 90 | From `0<U` and nonzero beta at `nu*n`, obtain `0<nu`, `0<n`, `nu<=2U`, `1/2<=U/nu` | Actual support and multiplier positivity; elementary Nat/Real inequalities |
| `short_nonzero_index_eq_one`, 111 | With `U/nu<1`, nonzero beta at `nu*n` forces `n=1` | `nonempty_endpoint_bounds`, actual support and integer discreteness |
| `dyadicPacket`, 127 | Existing `CoprimePacket` constructor, with the actual `dyadicBeta` as its beta | Task 1 `CoprimePacket`; existing `hz : 0<z` and `hc : rho.natAbs.Coprime z` parameters |
| `short_signedCoefficient_zero`, 137 | At a short endpoint, the existing signed coefficient vanishes for `n != 1` | `short_nonzero_index_eq_one`; exact packet and signed-coefficient definitions |
| `short_modeCoefficient_zero`, 148 | Same vanishing for the existing mode packet, keeping every mode phase | Task 1 `signedCoefficient_modePacket`; preceding theorem |
| `finite_singleton`, 160, currently private | For any additive commutative monoid, a finite sum supported at `1` is the corresponding `if 1 in N` term | Existing `Finset.sum_eq_single` / `sum_eq_zero` proof |
| `short_mode_mass`, 179 | Exact finite sum of squared norms reduces to its `n=1` term | `finite_singleton`, `short_modeCoefficient_zero` |
| `modeCoefficient_one_norm`, 193 | Norm at `n=1` equals the norm of the actual beta at `nu` | Task 1 `norm_signedCoefficient_modePacket`, `signedCoefficient_false_eq_actual`, `norm_e`; exact packet definitions |
| `short_mode_mass_eq_beta`, 203 | Exact squared mass equals the actual beta norm squared at `nu`, or zero when `1` is absent | `short_mode_mass`, `modeCoefficient_one_norm` |

### Private helper visibility

`finite_singleton` is also called by `short_common_phase_packet`, which stays in the old parent under this two-module scope. Simply moving the private helper would break that retained proof's name resolution.

Recommended handling: promote the existing helper to the public name

`ImbalancedChen.P3ZActualPrimaryShortEndpoint.finite_singleton`

in the new core, with the **same type and proof body**, and remove its old private declaration. The retained common-phase proof then resolves the same unqualified helper name through the imported core. This reuses the proof once; it does not copy it or create an additional wrapper. Record that the old private serialized name is not being preserved and audit the new public constant.

No other moved declaration requires a statement or visibility change.

### Short-core terminals

The meaningful accepted endpoints would be the original names:

- `nonempty_endpoint_bounds`;
- `short_nonzero_index_eq_one`;
- `short_mode_mass_eq_beta`.

Their complete original hypotheses remain necessary, especially `0<U`, the actual nonzero-beta premise for index bounds, and `U/nu<1` for the singleton result.

## 4. Exact migration inventory: dyadic assembly core

Donor: `ImbalancedChen/Part3ZActualPrimaryDyadicAssembly.lean`.

Move the **28 existing generic source declarations** through `nonzeroSource_idempotent`. All are already public and retain namespace `ImbalancedChen.P3ZActualPrimaryDyadicAssembly`.

| Declaration, donor line | Type/role to preserve | Immediate proof or definition dependencies |
|---|---|---|
| `Key`, 23 | Existing alias `Nat × (Nat × Bool)` | No project object |
| `dyadicScale`, 26 | `2^j / 2` as a real number, so `j=0` gives `1/2` | Nat power and cast |
| `outputKey`, 28 | `(rhoPrimaryNu rho y, (Nat.clog 2 |y|, decide (y<0)))` | Task 2 primary multiplier; original `Output` |
| `sourceKey`, 31 | Computed key of the actual output of a source | `outputKey`, original `output` |
| `keys`, 33 | Image of the computed key on the actual nonzero source | `sourceKey`, original `nonzeroSource` |
| `block`, 36 | Filter of that same nonzero source by computed-key equality | `sourceKey`, original `nonzeroSource` |
| `dyadicScale_pos`, 39 | Every computed scale is positive | The actual scale formula |
| `power_step`, 43 | Exact predecessor power identity for positive `j` | Nat arithmetic |
| `clog_dyadic_bounds`, 49 | Exact strict-lower / closed-upper support of the ceiling-log key for `m>0` | Mathlib `Nat.le_pow_clog`, `Nat.clog_pos`, `Nat.pow_pred_clog_lt_self`, `power_step` |
| `clog_eq_iff_dyadic`, 71 | Converse uniqueness of that support convention | `clog_dyadic_bounds`, `Nat.clog_le_iff_le_pow`, `Nat.lt_clog_iff_pow_lt`, `power_step` |
| `sign_key_iff`, 95 | For nonzero integer `y`, key Bool equals the requested sign iff the original sign condition | Bool cases and integer order |
| `block_subset`, 102 | Block is a subset of the original nonzero source | Existing filter |
| `source_own_block`, 106 | Every actual source member belongs to its computed key and block | Image and filter membership |
| `block_key_unique`, 111 | A source member cannot belong to two distinct computed keys | Key equalities from the same source |
| `blocks_disjoint`, 115 | Distinct keys give disjoint actual source blocks | `block_key_unique` |
| `block_output_nonzero`, 121 | Every block member retains nonzero output | `block_subset` and the original nonzero filter |
| `keys_multiplier_pos`, 125 | Every occupied key has positive primary multiplier | Image witness and `rhoPrimaryNu_pos` |
| `block_eq_dyadicSource`, 132 | Computed-key block equals the existing literal primary/sign/dyadic filter | `clog_eq_iff_dyadic`, `sign_key_iff`, actual filter memberships and integer absolute-value casts |
| `finite_source_assembly`, 164 | Exact finite partition of every original complex source payload | `Finset.sum_fiberwise_of_maps_to` and computed keys |
| `beta_block`, 170 | At a fixed joint output, its beta belongs to its unique matching key, otherwise zero | Original `fiber`, `beta`, key depending only on output; finite filter identity |
| `beta_nonzero_key_mem`, 187 | Nonzero actual beta supplies a computed occupied key | Task 2 `beta_ne_zero_mem_image` and source witness |
| `finite_beta_assembly`, 193 | Actual beta is the sum of its computed block betas | `beta_block`, `beta_nonzero_key_mem` |
| `finite_beta_energy_assembly`, 203 | Exact sum of squared beta norms over arbitrary finite `B : Finset Output` equals the sum over computed blocks | Same unique-output-key facts; finite sum exchange, not Cauchy |
| `beta_block_ne_zero_key`, 215 | Nonzero block beta identifies its actual key, occupancy and underlying nonzero beta | `beta_block`, `beta_nonzero_key_mem` |
| `signed_beta_block_eq`, 227 | Existing block beta at signed `nu*n` equals existing `dyadicBeta` | `block_eq_dyadicSource`, then definitional equality |
| `assembled_short_index_eq_one`, 234 | The actual computed block's nonzero coefficient has `n=1` in the short range | `signed_beta_block_eq`, `dyadicScale_pos`, short-core endpoint |
| `assembled_beta_coprime`, 242 | The actual computed block supplies the original coprime index gate | `signed_beta_block_eq`, `dyadicBeta_coprime` |
| `nonzeroSource_idempotent`, 249 | Applying the existing nonzero filter twice changes nothing | Original filter, propositional simplification |

### Assembly-core terminals

- `finite_source_assembly` and `finite_beta_assembly` retain exact original complex coefficients.
- `finite_beta_energy_assembly` preserves the actual beta norm with no introduced cardinality loss.
- `signed_beta_block_eq` and `assembled_beta_coprime` are the existing direct suppliers of archived `rowPacket_beta` and `rowCoefficient_eq`.
- `assembled_short_index_eq_one` completes the computed-key short endpoint.

No new terminal wrapper is needed. Preserve these existing theorem names and full types.

## 5. Exact declarations retained in the old parent modules

### In `Part3ZActualPrimaryShortEndpoint.lean`

Retain these five declarations:

| Declaration, donor line | Real dependency / reason to retain |
|---|---|
| `short_common_phase_packet`, 216 | Its type explicitly uses the genuine `CommonCompletedVariable` and `.weight`. It also calls `finite_singleton`, motivating the helper promotion above |
| `actualDyadicBeta`, 237 | Specializes to `MediumAtom`, `signedResidue`, `actualNonzeroSource`, and the actual M2/mode source parameters |
| `actual_nonempty_endpoint_bounds`, 245 | Existing one-line consumer of the generic endpoint through `actualDyadicBeta` |
| `actual_short_index_eq_one`, 253 | Existing one-line consumer of the generic short index result |
| `actual_nonzero_coprime`, 261 | Uses the actual signed-residue/natAbs identity and actual-source specialization |

These are genuine existing consumers. Keeping them in the parent does not weaken or replace them, and does not imply they are newly accepted when the core passes.

### In `Part3ZActualPrimaryDyadicAssembly.lean`

Retain these three declarations:

| Declaration, donor line | Real dependency / reason to retain |
|---|---|
| `actual_beta_energy_assembly`, 257 | Specializes to actual M2/mode `actualNonzeroSource` and `signedResidue`; uses the new core's `nonzeroSource_idempotent` and exact beta-energy identity |
| `common_phase_source_assembly`, 282 | Explicit genuine `CommonCompletedVariable` / `.weight`; finite source partition and sum exchange |
| `common_phase_beta_assembly`, 293 | Same genuine common variable; exact beta partition and finite sum exchange |

The original assembly parent still needs to import the original short-endpoint parent for its actual specialization, as well as the new assembly core for the moved names. Do not strip imports needed by retained consumers just because the new core does not need them.

### CommonCompletedVariable is not a hidden dependency of the two cores

None of the 20 + 28 selected declaration types or bodies uses it. Remove the old unused `open ImbalancedChen.Part3 (CommonCompletedVariable)` from the new cores; do not change any theorem to take an arbitrary replacement weight.

The three retained common-phase statements really do need the existing object. The accepted P3.1 common interface is the appropriate existing supplier for clipping/energy bounds when those later consumers are integrated. This two-module task does not duplicate it, migrate its provider, or prove construction of a common interval from the original Poisson/Fourier step.

## 6. Exact unchanged definitions and original wiring

The source object remains the old `Source`, `output`, `carrier`, `weight` and `beta` from Task 2's same-name extraction. In particular:

`dyadicSource rho S nu U negative`

is exactly the old filter of

`primaryFibre rho (nonzeroSource S) nu`

with the original inequalities and sign; `dyadicBeta` is exactly the old `beta` on this filter. The existing `dyadicPacket` sets its beta field to that function, not a new arbitrary coefficient map.

For the actual literal source, take `S := carrier A a T H F` and `rho := a`. The required positive level and residue/level coprimality for `dyadicPacket` come from the existing source-membership/level suppliers with a true positivity hypothesis on `T`. They are already constructor parameters of the old type, not newly added assumptions or fields.

For the archived original row, the exact intended instance remains:

- `a := D.block.atom.residue`;
- `S := originalSource D`;
- `nu := k.1`, `U := dyadicScale k.2.1`, `negative := k.2.2`;
- `lambda := D.lambda r`, `omega := D.omega`, `z := z.val`.

The archived `rowPacket` already uses precisely this `dyadicPacket`; its `rowPacket_beta` calls `signed_beta_block_eq`, and its `rowCoefficient_eq` calls `assembled_beta_coprime`. The new cores promote the existing suppliers rather than creating another path. The original `D : OriginalData` and missing genuine `FixedBlock` closure are not constructed by this unit.

## 7. Manuscript linkage and substantive scope

Frozen local manuscript: `/workspace/scratch/dcb7c80f70a4/analytic-appendix-1106.tex`.

| Manuscript location | Needed finite fact supplied by this existing source |
|---|---|
| Line 676, coefficient support; line 684, each sign handled separately | The actual sign/dyadic filters and their computed-key equivalence |
| Lines 685–687, `B` / `B_nu` and harmless restrictions / unit phases | Exact block beta-energy partition; existing mode norm and short-mass identities |
| Line 722, coefficient `1_(n,a)=1 beta(nu*n,z)e(-n/z)` | Actual `dyadicBeta` in the existing `CoprimePacket`, and its proved coprime gate |
| Line 964, `y=nu*n` with primary multiplier support | Task 2's primary arithmetic plus the exact `signedY_div` interface and unchanged sign |
| Line 999, regular norm for length `L >= 1/2` | `nonempty_endpoint_bounds` gives `U/nu >= 1/2` on a genuine nonzero coefficient block |

Here the code's `U` is the **output coefficient dyadic length**, corresponding to the manuscript subsection's `Y`; it is not the original convolution length `U`.

The `U/nu<1` theorem is an elementary integer-support endpoint: the sole possible nonzero natural index is `1`. It is not a spectral estimate and does not supply the oldform multiplier cost.

The common `m` interval/phase equality consumers remain present in their old files but are deliberately outside the two-core acceptance scope. Do not claim that this task newly proves the common interval's construction or accepts all three common-phase consumers.

## 8. What can be copied without new mathematics

All selected source proofs are already present and use exactly the finite definitions or existing Task 1 / Task 2 constants listed above. Their proof bodies can be reused directly under the smaller imports. The only planned source changes beyond import/movement are:

1. remove obsolete namespace opens inherited solely from the heavy parents;
2. make the existing `finite_singleton` helper public so both migrated and retained consumers can use its one proof;
3. fix only actual pinned Lean API/linter failures if root's later compile finds them, preserving theorem types and recording each repair.

Potential API-sensitive sites are the existing integer division rewrite, `Nat.clog` theorem names / binder inference, exact casts, and simplifier/rewrite focus. Source inspection is not a compile certificate, but no unavailable project object or substantive mathematical premise was found in this selected finite closure.

Do not preemptively generalize the statements, replace their beta definition, assume support instead of deriving it, or reconstruct a proof already provided by the donor.

## 9. Root-controlled tasks, conditional on no existing acceptance covering them

### Task 0: Preserve the independent reuse audit

- [x] Root has accepted the two-core scope after the checked P3.1/P3.2/P3.5 reuse audit and exact source-only provenance comparison. Preserve those evidence boundaries for the two donor hashes.
- [ ] If the actual needed results already have sound matching acceptance, stop this migration plan and use that source/dependency evidence.
- [x] Root authorized the remaining Task 3 implementation after local and cloud Task 2 PASS. Implementation and compilation belong to the assigned worker/root, not this plan author.

### Task 1: Move the 20-declaration short endpoint core

**Create:** `ImbalancedChen/Part3PrimaryDyadicShortEndpoint.lean`.

**Modify:** `ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean` only to import the new module, remove the moved declarations, and retain its five consumers.

- [ ] Move exactly the section-3 declarations, preserving old namespaces and public types.
- [ ] Promote the single existing private helper as specified; keep one implementation.
- [ ] Verify the old parent retains the five listed declarations and can resolve the promoted helper through the import.
- [ ] Root performs strict compilation with the exact Task 1 / Task 2 dependency objects selected for its gate; no old heavy parent object is allowed to substitute for the new core.

### Task 2: Move the 28-declaration assembly core

**Create:** `ImbalancedChen/Part3PrimaryDyadicAssembly.lean`.

**Modify:** `ImbalancedChen/Part3ZActualPrimaryDyadicAssembly.lean` to import the new core, remove exactly those declarations, and retain its three consumers.

- [ ] Move exactly the section-4 declarations and preserve all computed-key, endpoint and coefficient formulas.
- [ ] Preserve the existing dependency on the original short parent where the retained actual/common consumers need it.
- [ ] Root strictly compiles the new assembly core; inspect the elaborated types of the exact energy, signed-beta and short-index terminals.

### Task 3: Root's scoped acceptance

- [ ] Use the exact nine-module order in section 2 for the fresh project closure. Do not treat an old broad parent or a prior Task 1/2 object as a trusted stand-in.
- [ ] Run nine strict compilations, nine leanchecker replays, complete nine-module defining-module/serialized inventory agreement, transitive-axiom checks and source/object hashes under the exact clean acceptance HEAD; resolve any same-named generated-constant ownership conflict explicitly.
- [ ] Source-level selected count is 48 declarations: 47 existing public declarations plus the formerly private helper. This is **not** the expected serialized inventory count; generated declarations must be counted by the audit.
- [ ] Compare moved public theorem types with the donor statements, and record the private-to-public helper change separately.
- [ ] Report only the finite dyadic/endpoint scope. Do not claim acceptance of the five + three retained consumers, `OriginalData`, fixed-height-to-`R(n)`, or the ABL spectral estimate.

## 10. Explicit exclusions

- No implementation or compilation was performed for this plan.
- No new wrapper theorem is needed beyond promoting the existing helper's visibility.
- The accepted P3.1 common-completed interface and its provider objects are left intact.
- Previously accepted P3.5 Cauchy/exhaustion is not repeated.
- Fixed-height cusp Fourier coefficients remain actual height-dependent integrals. None of the selected finite statements defines or identifies the manuscript's automorphic `R(n)`.
- The scalar cusp-phase identity, primary coprimality, finite beta partition and short endpoint do not imply the actual oldform coefficient identity or its packet norm cost.
