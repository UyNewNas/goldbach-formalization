# VariableEnvelope: isolated proof and integration contract

This development starts from PR #1 commit
`c339d0ba3d15c0aa897db7696531b63a14784721` on branch
`codex/variable-envelope`. It only adds the two VE modules, this note and
dedicated verification files. The root import, dependency pins and workflows
are unchanged. Consequently the existing root CI alone does **not** establish
that the new VE modules have been checked; run the dedicated verifier below.

## Mathematical scope

`ImbalancedChen.VariableEnvelope.original` is the literal eight-branch
expression, including the original three-way minimum in `v`, both gated `w`
branches, and both gated pair branches. All statements specialize the residue
exponent to 1 and the spectral exponent to 7/32.

The principal theorem `original_eq_six` proves the six-branch identity on
`0 ≤ z ≤ y ≤ x ≤ 25/128`. This includes the manuscript domain with `0 < z`.
Its only hypothesis is this geometric ordering. No envelope identity,
continuity, distribution theorem, analytic lower bound, or sieve estimate is
assumed.

The proofs establish:

- `v_eq_min`: the middle affine branch of `v` is redundant for every real input.
- `xz_gate_margin`, `yz_gate_margin`: a pair branch at least as large as `v x`
  passes its original gate with surplus at least `3/256`.
- `original_eq_six`: baseline absorption removes failed gates without asserting
  the false pointwise identity `w x y z = B z`.
- `continuousOn_original`: continuity of the original expression relative to
  the closed ordered domain, via the globally continuous six-branch formula.
- `B_le_original`, `original_le_cap`: `B z ≤ original x y z ≤ 153/256`.
- `original_margin`: `3/256 ≤ original x y z - 3*x`, with separate strict
  positivity corollaries and exact sharpness statements.
- `threshold_597_le_original`: `z ≤ 7/4000` implies the level is at least
  `597/1000` on the ordered domain.

The lower bound `3/256` is attained. “Strict margin” means a surplus bounded
below by this positive number, not a surplus strictly greater than it.
Unordered triples and perturbed residue exponents require separate arguments.

## Source alignment and reuse

The local proof source is `goldbach-research/variable-envelope-simplification.tex`
(the section “A continuous six-branch expression on the ordered domain”).
The later source supplied by the user,
`goldbach-research/slanted-restoration-final-transfer-20261009.tex`, replaces
the fourth-node restoration contribution and final numerical transfer. It
does not redefine VE. This isolated development does not formalize that final
transfer or certify any of its analytic or numerical inputs.

The existing pinned Apache-2.0 mathlib revision
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` supplies all dependencies:
min/max order facts, real arithmetic, `Continuous.min/max`,
`ContinuousOn.congr`, and kernel-checked `linarith`/`norm_num` proofs.
There is no new analytic dependency or copied external Chen theorem.

An additional reuse search inspected Lean files at the fixed revisions already
recorded in `EXTERNAL_REUSE.md`: ANT (197 files), historical Chen (14),
subfish/goldbach-lean (7390 including research files), and lixiang/chen_theorem
(420). Searches for Lichtman, VariableEnvelope and the characteristic affine
constants did not locate a matching eight-to-six theorem in those revisions.
This is a bounded search result, not a claim that no such proof exists elsewhere.

Useful upstream declarations:

- [Continuous min/max](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Topology/Order/OrderClosed.lean)
- [ContinuousOn.congr](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Topology/ContinuousOn.lean)
- [Min/max order API](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Order/MinMax.lean)

## Reproduction

On 9 October 2026, both modules compiled without warnings, all seven exact
boundary examples passed, bundled `leanchecker` replayed both modules, and
the transitive axiom audit passed for all 48 public declarations. Only the
three permitted standard axioms occurred. Independent statement-level review
also passed. The source hashes and per-declaration axiom results are saved in
`verification/variable-envelope-result.json`; this record covers VE only.

With the repository's pinned Lean 4.33.0-rc1 toolchain on `PATH`:

```sh
lake exe cache get Mathlib.Topology.Algebra.Ring.Real Mathlib.Topology.Order.Lattice Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum
python3 verification/verify_variable_envelope.py
```

The verifier builds both new modules explicitly, elaborates exact boundary
examples, runs the bundled `leanchecker` on each new module, and prints the
transitive axioms of every public definition and theorem. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. Private proof helpers are
included through their public dependents and through module replay. Source
hashes guard against edits during verification. Results and logs are written
under `.lake/variable-envelope-verification/`; a failed or incomplete run does
not count as a pass.

To consume all results in another module, explicitly import
`ImbalancedChen.VariableEnvelopeConsequences`. The eventual integrator may add
that import to the shared root after review and then rerun the full project
build, root replay and root axiom audit. This branch deliberately leaves that
shared integration step separate.
