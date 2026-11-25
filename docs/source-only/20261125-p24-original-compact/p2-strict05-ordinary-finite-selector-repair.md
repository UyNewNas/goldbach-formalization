# P2 strict05: ordinary finite-selector expression repairs

## Actual failure and input

The original strict checker compiled `ed3b16671f377f1e122db28baaae321cf667a597`. The completed batch has 283/321 successful modules (276 reused, 7 fresh), four direct failures and no pending modules. This note binds the complete log `docs/source-only/20261125-p24-original-compact/p2-strict-symbolic-05.log`: 17,467 bytes, SHA-256 `d16e52df7542486074b3ccadc65abca416f372283e7f7c34cfe7e20271d841e4`.

`ActualThirdOriginalP4AOrdinaryFiniteSelector.lean` has exactly the two assigned failures: line 227 retains `decide (153*D-96*lo 2 ≤ 256*T) = true` where the proposition itself is needed; line 295 supplies a `match k` branch proof where the existing supplier expects its elaborated dependent `match k, hD` form. Its supplier `ActualThirdOriginalSixTentOrdinaryMassCeil` passed in this same batch (10.744 seconds).

Local baseline HEAD was `e37609944b79df00194066596d76fee47f0c87a0`; the assigned file was byte-identical to source `ed3b1667` before editing.

## Manuscript boundary and existing interfaces

Rechecked the frozen 1106 numerical appendix's directed arithmetic, affine enclosure and compact-upper-integration passages, together with `certify_extended_prefix.py`'s `active_min_plane`, `affine_cap_lower` and post-selection Jensen guards. Frozen publication commit: `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. Cached appendix SHA-256: `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`; cached producer SHA-256: `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`.

The cached Q80 producer has its own midpoint selector. It is not substituted for this existing auxiliary P160 selector. This repair preserves the latter's B seed, six-candidate order, exact endpoint-sum score, earlier-winner tie rule and post-selection residual/low guards. In particular, no root or residual condition moves into or out of the selection process.

Both failures are expression/API issues. Boolean reflection and case reduction provide the already available propositions; associativity only normalizes the rising root inequality. No omitted analytic derivation, new premise or substantive manuscript gap is needed for these two repairs.

## Two proof-body changes

1. `selected_base_root`: replace the unsuccessful `simpa only [...] using hr` with `exact of_decide_eq_true hr`. The log already confirms that `List.mem_filter` extracted the correct Boolean condition. The same reflection API is used in the existing source-selection/queue modules.
2. `original_finite_selected_tent_integer_upper`: keep the existing supplier and every argument value, but provide its branch, root and residual proofs through three explicit proof goals. Case analysis on `TentSide` reduces both match forms. Branch and residual cases use `exact`; the rising root case uses only `add_assoc` to identify `D + ((x+y)+z)` with `((D+x)+y)+z`, and the falling case uses `exact`.

No other proof body, public header, computational definition, import or option was changed. The local check of related tactic patterns leaves the existing multi-goal sequences intact; the newly introduced `<;>` follows a two-constructor case split, and `simpa only [add_assoc]` is confined to the rising case where the two associations actually differ. No baseline style exception is requested or added.

## Frozen candidate and review

- Source before SHA-256: `89906ec43261c8b12e6969536cf136120abe3f3a6fd1548004674195a5725bd3`.
- Candidate SHA-256: `a6ab617c31b85f34243414b7edab32173a2193fd3de58159c61b7aa140e7d35f`.
- Mechanical comparison against `ed3b16671f377f1e122db28baaae321cf667a597` confirms all 18 theorem headers, 15 complete computational declaration blocks and the sole import are unchanged. No new declaration, proof escape or linter/resource option was added. Scoped `git diff --check` passes.
- Independent read-only review by `p24_project_cache_reuse`, bound to the candidate hash, found no static blocker in the Boolean reflection, dependent-match reduction or rising-root associativity. It did not edit or compile.

Only the assigned Lean file and this note were edited. No index, commit, ref, remote input or running compiler task was touched. The candidate has not been compiled; actual acceptance remains with the parent's unchanged original checker.
