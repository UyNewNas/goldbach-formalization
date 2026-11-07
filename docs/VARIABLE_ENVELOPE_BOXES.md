# Whole-box correctness for the existing variable-prefix algorithms

This branch starts at PR #2 commit
`7ba701070c5481acf9de1adb4489fd8016e08089`. It reuses `VariableEnvelope`
and `VariableEnvelopeConsequences` without changing their definitions or
reproving the eight-to-six identity. Its consumer is the original eight-branch
`original` at residue exponent 1 and spectral exponent 7/32.

## What the certificate means

For a rational box `b`, an effective point satisfies both its six closed
endpoint inequalities and `0 ≤ z ≤ y ≤ x ≤ 25/128`. The box need not lie
wholly inside the ordered region. `RationalBox.enclosure` proves

```text
(b.lower : Real) ≤ original x y z ≤ (b.upper : Real)
```

at every effective point. The proof propagates the scalar interval bounds
through the actual maximum. In particular, `v_hi` checks whether its interval
contains the peak `25/128`; only a non-crossing interval uses its endpoint
maximum. There is no assumption that finitely sampled corners represent the
whole box.

`RationalBox.feasible` is a computable, exact nonemptiness test, proved
equivalent to existence of an effective real point. It constructs rational
coordinates successively as

```text
z = max(0, lowerZ)
y = max(z, lowerY)
x = max(y, lowerX)
```

and checks their three upper endpoints and `x ≤ 25/128`.
`RationalBox.marginCheck` includes this nonemptiness test as well as the
strict rational inequality `lower - 3*upperX - eta > 0`.
Its soundness theorem returns both a witness and the strict inequality for
**every** effective point. An empty intersection cannot pass the certificate,
even when the isolated margin arithmetic happens to be positive.

## Exact connection to the existing scripts

The source entry points supplied by the user are
`certify_variable_prefix.py` and `certify_extended_prefix.py` under the local
`goldbach-research` directory. Their unchanged relevant function bodies and
constant assignments are preserved in `verification/reference/`, with full
source hashes, excerpt hashes and source line information in the manifest.
The extraction utility is for provenance; CI executes the checked-in excerpts
and compares their exact integer results with the Lean regression fixtures.

The Lean integer definitions preserve:

- `v_lo`: the minimum of the two downward integer divisions;
- `v_point_hi`: the minimum of the two upward divisions;
- `v_hi`: the inclusive `lo ≤ NMU ≤ hi` peak check and endpoint maximum;
- signed `ceildiv(n,d) = -((-n)//d)` for positive denominators;
- the decreasing `B` branch, with the upper coordinate used in its lower bound;
- all six `v` intervals in the scripts, including their redundant `v(y)`;
- the final componentwise `min(NT, ...)` truncation.

The seventh interval entry is `B(z)`. The proof explicitly removes the extra
`v(y)` by dominance on the ordered domain, reconnecting these seven entries
to the previously proved six-branch expression and hence to `original`.

For a positive integer scale `D`, the peak integer must satisfy
`128*NMU = 25*D`. `ScaledBox.rawLower` and `rawUpper`, divided by `D`, enclose
the untruncated `original`. The exact `phiRange` output instead encloses

```text
min (NT / D) (original x y z).
```

This distinction is essential: the truncated upper output is not generally
an upper bound on the untruncated envelope. Its lower output is still a valid
lower bound on `original`, and can therefore support a strict margin check.

These are kernel proofs about the Lean translation of the recorded arithmetic
algorithms. The source excerpts and cross-language exact regressions check the
translation against the supplied Python; they are not a formalization of the
Python interpreter, the scripts' remaining sieve calculations, or their full
numerical certificates.

## Width and rounding errors

`six_lipschitz_max` proves the global `9/2` bound with respect to maximum
coordinate distance. `original_lipschitz_max` transfers it back only when
both points satisfy the ordered-domain condition.

The exact rational box interval has the quantitative bound

```text
upper - lower ≤ (9/2) * width,
width = max(0, upperX-lowerX, upperY-lowerY, upperZ-lowerZ).
```

`enclosure_error` bounds both endpoint errors at each effective point, and
`error_lt_of_width_lt` gives an explicit epsilon criterion. The integer
algorithm retains its directed rounding; each aggregate endpoint is within
one scaled unit of the corresponding rational endpoint. Its total interval
width is therefore at most `(9/2)*width + 2/D`. Shrinking the box at a fixed
integer scale does not eliminate this rounding allowance.

## Extended-script dispatch restriction

The extended script first tests `x0 >= NMU`, including equality. Its separate
expression on that branch is not the full VE formula. The adapter here accepts
only the actual VE dispatch path `x0 < NMU` and `x1 ≤ NMU`. It rejects boxes
crossing that cut and rejects `x0 = x1 = NMU`; the latter belongs to the other
Python branch even though the original VE at that face has a separately
proved value. The general rational-box theorems still include `x = 25/128`.

## Verification and theorem inventory

Run, with the existing pinned toolchain on `PATH`:

```sh
python3 verification/verify_variable_envelope_boxes.py --cache-imports
python3 verification/verify_variable_envelope_boxes.py
```

The independent workflow `.github/workflows/variable-envelope.yml` checks out
the exact pushed or PR-head commit and records it. It explicitly builds the
two original modules and all four new modules, elaborates the old and new
regressions, replays their compiled modules with bundled `leanchecker`, and
audits the complete Lean environment inventory by defining module. The audit
includes private declarations, structure fields, constructors, recursors and
generated declarations; it does not infer coverage from source-code regexes.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed.

The retained CI artifact contains actual build/replay/audit logs,
`report.json`, `declarations.json`, `declarations.tsv`, and `theorem-types.txt`.
The latter lists the actual theorem types with the checked commit SHA. The
shared root import and other workflows remain unchanged.

Main theorem groups:

| Module | Main interface |
| --- | --- |
| `VariableEnvelopeRegularity` | `qVLo_le_v`, `v_le_qVHi`, `qVHi_sub_qVLo_le`, `six_lipschitz_max`, `original_lipschitz_max` |
| `VariableEnvelopeBoxes` | `RationalBox.enclosure`, `upper_sub_lower_le`, `enclosure_error`, `error_lt_of_width_lt`, `feasible_iff`, `marginCheck_sound`, `marginCheck_false_of_empty` |
| `VariableEnvelopeScaled` | `floorDiv_bounds`, `ceilDiv_bounds`, `scaled_v_bounds`, `scaled_B_bounds`, `scaled_crossing_iff`, scalar rounding bounds |
| `VariableEnvelopeCertificates` | `ScaledBox.raw_bounds`, `phiRange_bounds`, `rawLower_rounding`, `rawUpper_rounding`, `enclosure_error`, `error_lt_of_width_and_precision`, `marginCheck_sound`, `marginCheck_false_of_empty`, `extendedBelowCheck_sound` |

Independent read-only review was performed by an agent separate from the
authors of the mathematical modules. It checked all four new modules, including
the theorem types, both ordered-domain hypotheses for `original`, interval
directions, strict endpoints, signed division, peak equality, nonemptiness,
the capped target and the extended-script dispatch guard. A second reviewer
independently checked the whole-box and integer certificate modules. Neither
review found an outstanding issue. These reviews supplement the kernel checks;
the CI artifact records the mechanically checked types and dependencies.

The analytic distribution estimates, perturbed residue exponents, full sieve
functional, and the latest manuscript's assembled numerical constants remain
outside this interface.
