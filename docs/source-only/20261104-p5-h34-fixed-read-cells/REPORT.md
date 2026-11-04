# P5.6 / h34 — literal fixed-point cell reads

Date: 2026-11-04. Base: `def3f8c2a8418844e3ea230c2c7876e9917cc143`.
Repository: `UyNewNas/goldbach-formalization`.
Branch: `chatgpt/p5-h34-fixed-read-cells-20261104`.

PARTIAL_SOURCE_INCREMENT. Manuscript-internal h34 remains OPEN.
Three Lean files: 689 lines, 43 theorem declarations, 28 definitions/abbreviations.
All proof bodies and finite data checks are uncompiled/UNEVALUATED in Lean.
No kernel replay, transitive axiom audit, independent review, 430-round replay,
CI dispatch or external analytic implementation was performed. Lean and Lake
were not found on PATH. The commit requests [skip ci]. Only this new directory
is added; existing packets, production, P1.4 and P3.6 are unchanged.

## Why this increment is necessary

The literal producer's `points` list reads a specified OLD cell. For example,
W1 anchor 16/5 reads cell109. The scalar table lookup at the same knot uses
min(cell109,cell110). These are different expressions for arbitrary arrays.
Previous packets explicitly left bank point/candidate semantics open; their
closed-lookup profile estimates alone do not license replacing the raw read.

`specified_cell_is_not_scalar_lookup` gives a nonnegative synthetic-array
witness with the specified-cell value1 and the scalar lookup0. This is NOT a
counterexample to the actual430 arrays or manuscript, and no actual430 equality
or discrepancy was numerically tested. It prevents an invalid GENERIC rewrite.

## 1. FixedReadDictionary

W1 indices are the original 109+10*j. W2 indices are read from the existing
literal `rows.points` lists, not a second copied index table. The finite
`literal_W1_points` / `literal_W2_points` source proofs check the entire lists,
coefficients1 or4,1, order and original divisors1 or5. `w2RawCell_lt` guards
actual index bounds; there is no modulo-index truncation. All these checks
still await Lean execution.

`w1Cell_contains` and `w2Cell_contains` connect the specified cells to the
existing real anchor records. They prove CLOSED-cell containment, not open
atom membership. W2 uses the unchanged36 parameter records.

`rawFixedValue_eq` exactly decodes the point numerator. `candidate_fixedRead_upper`
retains the integer quotient of the FULL candidate and pays it in its correct
direction. It proves, also for signed old arrays/bases:

    candidate/Q80 <= baseValue + specifiedFixedValue + feedbackValue.

The individual feedback product floors remain INSIDE feedbackValue, and the
base remains in its original position. No floor is distributed as an equality.
This is not yet the real-integral comparison for feedbackValue or the base.

`fixedValue_le_of_cells` provides the finite fixed-channel induction step from
a PRECEDING closed-cell bound. That old bound is an explicit induction premise,
not proved for original counts here, not a new axiom, and not renamed as an
external theorem. Original count-history induction remains an internal gap.

## 2. FixedReadRows

The fixed channel now has explicit cell-labelled coefficient reads. Integral
channels remain the same production strict W1/W2 prime-child sums with the
same physical queries and all closed table atoms. Fixed coefficients stay1
for W1 and4/5,1/5 for W2.

`cellKernel` uses the existing row index type to index a cell value. Its inl
index does NOT claim that a fixed physical query belongs to an OPEN atom.
`fixed_physical_queries` separately records the real perform query's closed
cell. Thus query geometry and coefficient indexing are not conflated.

The new ideal is explicitly named `cellReadIdeal`. It differs from the old
scalar ideal in its fixed channel; no equality of those two profiles is claimed.
The same fixed-channel change is made to both arithmetic and ideal rows:

    newRow_b - theta * newIdeal_b = oldRow_b - theta * oldIdeal_b.

`discrepancy_exact` is pointwise before absolute values and before summing
parents. `cellReadRow_mass` and `cellReadIdeal_mass` preserve total row mass
exactly. Nonnegativity of the new arithmetic coefficients is obtained from
actual prime-child product support; ideal nonnegativity follows from the
unchanged nonnegative kernels. No negative coefficients are hidden in the
subtraction notation used to define the ideal correction.

`cellReadRow_value` binds the new coefficients to the specified fixed values
plus the original dynamic production sums. This is an exact finite dictionary,
not a count-defect claim or an alteration of any saved array.

## 3. SelectedFixedReadSupply

`literal_old_fixed_channel` pins the reads to `iterate g`, and
`selected_bank_fixedRead_upper` applies the candidate inequality to the NEW
closed owner whose selected action reads the OLD table. It leaves original
baseValue and feedbackValue visible.

`uniform_selected_fixedReads` invokes the existing strict W1 and production W2
suppliers. It transfers their coefficientwise absolute error by the exact
identity above, not by a signed cancellation estimate. One threshold precedes
N, root precision, mesh, root cell, action, generation map and nonnegative marks:

    selectedError <= epsilon * Theta;
    every new production coefficient >= 0;
    sum_coefficients <= 12 * Theta;
    Theta=0 implies error=0 and each coefficient=0.

There is no extra epsilon payment, no new12+epsilon constant, and no division
by a possibly zero Theta. The applied-profile inequality uses the EXPLICIT
cell-labelled ideal; it is not silently rewritten to the old closed lookup.
Outer aggregation remains after selected-action/root-cell partition; each
root cell retains its own Q and alternative offers are not all added.

## Remaining manuscript-internal obligations

1. Construct the COMPLETE original U3/U4 selected-count histories, including
   g/sigma assignments, actual cell-labelled fixed requests, owner multiplicity,
   and full/selected/inherited filter correspondence. The current Member-family
   estimates still take g and sigma as inputs.
2. Establish the original count induction with a preceding CLOSED-CELL
   invariant sufficient to consume the specified fixed reads. Do not replace
   this by equality with scalar adjacent-min lookup; no such equality is proved.
3. Bind all literal singleton/pair rounded weights to their actual integral
   pieces and complete feedbackValue/baseValue comparisons, ordinary/fixed/
   switched bases, analytic seed application and manuscript-local PP/same-rho
   instances. Fixed point-list binding alone is not full quadrature soundness.
4. Complete native-history proper/equality/inherit mass control, outer
   integral/Theta/count conversion and ONE nested430+11 causal refinement.
5. Stage the full held closure, compile, kernel-replay and audit axioms.

Genuinely external theorems remain recorded/reused inputs, not new implementations.
The manuscript's own unfinished instances are not moved to that bucket.
No h34 or hLower theorem, new axiom, or target-equivalent licence record is added.
Original c, K, root norm7/2, row norm12 and430+11 budget remain unchanged.

## Validation and staging

Stage FixedReadDictionary, FixedReadRows, SelectedFixedReadSupply, each with
Part5OriginalH430 prefix, under ImbalancedChen after the unchanged pinned imports.
The three new files alone are NOT a complete buildable dependency installation.

Static token/delimiter/whitespace and unique-declaration checks succeeded.
Two hundred synthetic exact-rational tests checked the row-replacement and
outer-floor formulas only. They did not execute Lean, the original tables,
finite point guards, or a count proof. These tests confer no formal credit.
Source hashes/imports are recorded in REGISTRY.json. Compilation and all finite
point-list/geometry guards remain explicitly unevaluated.
