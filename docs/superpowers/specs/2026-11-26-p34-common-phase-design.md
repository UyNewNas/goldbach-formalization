# P3.4 common completed-variable preservation

## Goal and manuscript scope

Accept the three existing finite identities that preserve the genuine common completed-variable weight across the primary/sign/dyadic partition and short endpoint. This is the 1106 appendix's requirement that the interval and phase remain common at every level (lines 700–727). The manuscript source remains `UyNewNas/chen-imbalanced-semiprimes` commit `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`, `paper/release-20261106/en/analytic-appendix.tex`.

The source baseline is `b945f39a1e355ff4fcca9865ab59ffc97f2172c0`. Its three separately accepted scopes already cover 19 distinct modules and 294 distinct declarations. The three retained parent proofs selected here are absent from those inventories and the inspected P3.1/P3.2/P3.5 receipts.

## Approach

Two source-preserving routes were checked. Importing the present `Part3DistributionTargets` would bring a 57-module source closure into the new consumer; its old object cannot be mixed with the relocated packet constants. Extracting its exact existing common-variable structure and weight into a Mathlib-only core yields an 11-module closure with the accepted nine dyadic modules. The coordinator selects the latter to keep this finite integration small and independently reproducible. This choice does not change the structure, its fields, or its weight formula.

The alternative of introducing an arbitrary weight or another common-variable structure would lose the original interface and is outside the task. Reproving P3.1's accepted common-energy inequalities would repeat existing work and is also outside the task.

## Exact source moves

1. Move the complete `CommonCompletedVariable` structure and `CommonCompletedVariable.weight` declaration, including their documentation, from `Part3DistributionTargets` into `Part3CommonCompletedVariableCore`. Keep namespace `ImbalancedChen.Part3`, the natural interval endpoints, real additive phase, half-open `Finset.Ico` gate and exact complex exponential. Import this core in the original provider and remove only the old declarations.
2. Move `ImbalancedChen.P3ZActualPrimaryShortEndpoint.short_common_phase_packet` into `Part3PrimaryDyadicCommonAssembly`.
3. Move `ImbalancedChen.P3ZActualPrimaryDyadicAssembly.common_phase_source_assembly` and `common_phase_beta_assembly` into the same consumer, preserving their original namespaces.
4. Both old `Part3ZActualPrimary*` parents import the new consumer and lose only the moved declarations. The short parent keeps `actualDyadicBeta` and its three actual-mode theorems; the assembly parent keeps `actual_beta_energy_assembly`.

Copy statements and bodies exactly. The three proofs use the common weight as an opaque multiplier and do not unfold it. Preserve this property. The historically accepted generated constant `CommonCompletedVariable.weight.eq_1` belongs to `Part3CommonCompletedInterface`; do not copy it, eagerly materialize it in the core, or claim that this small gate has rebuilt the P3.1 interface. All actually generated constants in the new modules must still pass the unchanged complete inventory audit.

The detailed discovery report, donor source identities, exact blocks and retained remainder hashes are in `docs/part3-distribution/p34-common-phase-20261126/NEXT_SCOPE_AUDIT.md`. That report is source evidence, not a proof certificate.

## Verification contract

Reuse the existing fixed verifier and Lean auditor mechanics. The accepted nine-module dyadic dependency order is followed by `Part3CommonCompletedVariableCore` and `Part3PrimaryDyadicCommonAssembly`. Strictly compile and replay all eleven within the new joint scope, checking Lean-resolved imports against only earlier rebuilt project objects and pinned external objects. This repetition verifies the new import combination; it gives no extra proof credit to the unchanged nine modules.

The new entry point binds itself, its full auditor, the five-declaration move ledger, unchanged configuration and source bytes. It enforces the exact clean source commit, the frozen baseline ancestry, warning-as-error compilation, bundled `leanchecker`, full serialized/actual-defining-module inventory equality, complete printed types and transitive axioms. Keep every private and generated constant in the audit. Allowed axioms remain exactly `propext`, `Classical.choice`, `Quot.sound`.

The move ledger records all five full source blocks, old/public qualified names, original and target signatures, exact byte hashes, any actual API repair, generated owners and target compiler-type hashes. Verify the three entire donor remainders after the documented removals/import additions, including the five retained actual-mode declarations. Do not claim those heavy parents compiled.

Frozen Lean: `4.33.0-rc1`, compiler commit `62eed1db4d67327ec8120be05f1a1b0847d74561`. Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. All configuration and dependency pins stay unchanged. No `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide` or kernel bypass.

## Remaining boundaries

This unit gives exact finite complex identities. It does not prove a new spectral inequality, identify a fixed-height Fourier integral with `R(n)`, supply an oldform law, or construct the genuine original row. The new P3.1 actual common interface at `acfa81c6d593276ef50f8af4e4f79b150772d7c8` and P3.5 test seminorm at `0ef2ad29` are accepted neighboring work, retained for reuse.

`OriginalData` itself is available as an eleven-field original definition. Its required `OriginalMediumPhysicalE3Block.FixedBlock` source is separately pinned at 6,566 bytes, SHA-256 `1ed9fec9d526f866fff9a29f9d8d0fa96d63def2a8b1e4e7a42ad759a8989982`. Its row carrier also needs the previously unresolved `OriginalMediumDoubleLambdaColorWindows` and further original dependencies. Recovering the first file alone is not a complete closure certificate. This new target was outside the previous 59-module search set and is being checked separately without repeating that search.

Publication remains on the existing P3.4 branch/draft PR. The user has already authorized implementation, compilation and GitHub submission. P3.4 remains incomplete until the actual original/spectral obligations are closed.

## Recorded verification adjustment

Focused strict compilation and kernel replay of the two new owners plus the complete eleven-module inventory passed on P3 at task d89a6e0e760041ccbf72888c17ee6552. Local overlapping attempts were resource-terminated and the later serial attempt intentionally stopped; they are not proof failures or acceptance evidence. The exact clean source commit is 89fb011ec7f086621170b5bee819d1cf1230290e. The eleven-module standalone entry remains unchanged and available. Its full final validation is included in the fourteen-module common/actual gate described in the subsequent actual-mode plan, rather than running two overlapping full closures. No standalone full eleven-module acceptance is claimed.
