# Range-32 integer guard: floor coercion and zero branch

Status: source candidate; root owns the actual Lean recheck. No new compilation,
kernel, numerical endpoint, or cache-acceptance credit is claimed.

## Actual inputs and scope

The two newly reported errors are from source
`fb61b4cd912765dc7975051055b0d2c3ed3d3714` in
`ActualThirdOriginalPositive256LogRange32IntegerGuard.lean`:

- At original line 138, `Int.le_floor.mpr hfirst` did not elaborate with the
  intended ambient field and coerced integer one.
- At original line 141, `change` did not identify
  `originalLogBranch ((x1:Real)/(x0:Real)) 0` with `originalLnUnit`.

Only these two proof sites are changed. The previously repaired 128-factor
cancellation and explicit multiplication of the upper coordinate bound are
unchanged.

## Manuscript and existing implementation check

The frozen 1106 numerical appendix, SHA-256
`bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`, was checked
at its directed arithmetic/logarithm discussion. The frozen
`certify_extended_prefix.py`, SHA-256
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`, uses literal
logarithmic widths in the compact mass. The source-binding qualification in
`compact05-range32-symmetric-repair.md` remains unchanged: this repair does not
substitute the appendix's other logarithm series for the existing original
positive-256 construction or claim new historical source equivalence.

The imported implementation was checked directly:
`ofReal x` has lower endpoint `floor (x * P160)` over `Real`;
`originalLogBranch x k` is exactly
`add (unitLog x 256) (mul (unitLog 2 256) (ofReal (k:Real)))`;
`originalLnUnit x` has the same expression with literal real zero. Thus the
zero-branch difference is the explicit coercion of natural zero. P160,
all 256 updates, range-32 reductions, exit inequalities, rounded multiplication,
and the final zero multiple remain intact.

## Minimal repairs and classification

1. Explicitly change the floor goal to the real-valued expression already
   present in the `ofReal` definition, apply `Int.le_floor.mpr`, and finish
   with the existing `exact_mod_cast hfirst`. This supplies the field and
   coerced integer-one normalization; the numerical lower bound is unchanged.
2. Prove a local interval equality between the zero branch and `originalLnUnit`
   with `simp only [originalLogBranch, originalLnUnit, Nat.cast_zero]`, then
   rewrite the branch before the existing `omega` step. This is the same
   normalization already used by
   `P4AOriginalSeedRange32Invariant.originalLn32_eq_originalLnUnit_of_le_two`.
   That downstream module imports this guard, so its proof pattern is reused
   locally without adding a circular import. No 256-step loop is unfolded.

Both failures are expression/API elaboration problems. No omitted analytic
estimate, extra hypothesis, or substantive mathematical gap was identified.
The proof still uses the existing integer width bound, its scaled first term,
and the previously established lower-endpoint comparison.

## Static verification and bindings

All seven existing theorem headers and both imports are unchanged. The assigned
file has no computational declarations; all imported computational definitions
are untouched. No new public declaration, axiom, proof placeholder, native
decision procedure, or linter option is introduced. `git diff --check` passes.
No Lean invocation, remote task, staging, or commit was performed for this edit.

Before SHA-256:
`42f7f6e1b94a7fbfa1dba89b2c96bf6f5c81c15a2e40ce0cb7563cfd9ec87afa`.
After SHA-256:
`578f4bf17381415dc3d1242aefa9aab0dcc2f6a1fa0bf8b570b4d486495c65e1`.
