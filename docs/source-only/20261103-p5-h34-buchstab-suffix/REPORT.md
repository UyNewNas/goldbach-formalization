# P5.6 / h34 — literal Buchstab suffix to selected arithmetic feedback

Date: 2026-11-03. Base: `9df29be647f3a5a93af16920cf863a17afb08b0d`.
Repository: `UyNewNas/goldbach-formalization`.

**PARTIAL_SOURCE_INCREMENT. Full h34 and the common 441-level realization
remain OPEN.** Four new Lean modules supply the previously missing oriented
connection from the selected integer Buchstab suffix to the original real
profile at the actual closed-cell query, then to the literal old-table
prime-child profile on the existing selected same-Q family.

`compiled=false`, `kernel_verified=false`, `formal_credit=0`.
All Lean proof bodies, including the new 200-entry finite equality guard,
are UNEVALUATED. No Lean/Lake executable is available on PATH. No kernel
replay, transitive axiom audit, independent review, Codex job, connected
computer action or CI dispatch was performed. No 430-round table was run.
Only this new source-only directory is added; older packets, production,
P1.4 and P3.6 are unchanged. No master merge is requested.

## Exact gap removed

The preceding selected-feedback packet proved BOTH:

* the actual closed owner reads a literal winning Buchstab integer suffix;
* the actual strict-prime profile approximates the original real Buchstab
  profile at the physical query.

It explicitly did not compare the integer suffix with that real profile.
This packet supplies that comparison, in the required direction:

    decoded selected suffix
        <= old-table integral at the owner's right endpoint
        <= old-table integral at the actual query.

The second step uses only nonnegative old entries and containment in the
closed owner cell. It does not assume the old array is antitone. It is not
an equality: floors, downward log rounding, and right-endpoint transport
are conservative losses. They must not be silently canceled.

## 1. Literal log binding

`Part5OriginalH430LiteralLogBinding` reuses J's
`P2HistoricalBankLogWeights.logWeight_le_log`, whose algorithm rounds both
rational grid endpoints, rounds their quotient, and then applies the exact
historical atanh32 fixed-point logarithm. It does not substitute logI(b/a),
a floating-point logarithm, or a differently rounded backend.

The new `literal_logWeight_eq_producer` contains a closed `fin_cases` /
`decide` proof for every i : Fin 200, binding the actual430 literal
`logWeights i` to that historical producer. It is not an input field or
assumption. Nevertheless it has NOT been reduced or checked by Lean in
this session. Its resource options remove the heartbeat cap and raise the
recursion cap for future checking; they confer no formal credit.

`literal_logWeight_le_log` transports J's analytic theorem to the actual
literal coefficients. `literal_product_le_log` uses the existing
`roundedProduct_eq_ediv` and `roundedProduct_le`, keeping each original
integer division INSIDE its summand and normalizing by Q80 only once.

As a nonformal spot check, an independent exact-integer Python calculation
matched source entries 0, 1, 2, 50 and 199. This was FIVE coefficient checks,
not an all-200 authentication, proof of backend equivalence, Lean check,
or table iteration. No conclusion of this packet depends on Python output.

## 2. Integer suffix to actual table integral

`Part5OriginalH430SuffixIntegral` gives an explicit bijection from the
original range(200-k) to the retained Fin 200 indices. It keeps duplicates
where the producer has them, preserves every quotient, and loses no tail
term. The k=200 empty suffix is included.

`tableTail_at_grid` specializes the existing exact scalar integral formula
`tableTail_eq_finite_log`, without changing closed knot values. Only the
previously proved scalar Lebesgue-AE identity is used for integration; no
prime-sum endpoint or moving pullback is discarded.

`suffix_le_tableTail` supplies the full oriented comparison. Its only data
premise is nonnegativity of the OLD array, which the actual iterate already
satisfies. No bound by one, integral estimate, final-table estimate or
analytic H/h licence is an input.

`tableTail_antitone` is derived from the same clipped-log formula. It works
for arbitrary nonnegative integer arrays and includes empty tails beyond
five. There is no unproved monotonicity premise for the 430 arrays.

## 3. Actual closed owner and original query

`Part5OriginalH430OwnedBuchstabLower` identifies the earlier full original
Buchstab profile with the existing tableTail primitive. It uses the literal
lower/upper table guards and changes Icc to Ico only within the scalar
Lebesgue integral, using existing endpoint integral identities.

The historical starts are kept exactly:

    lower: k = i-49,
    upper: k = max 50 (i-49),
    floorGrid k = baseStart(floorGrid(i+1)).

`buchstabValue_le_cell_profile` covers EVERY point of the owned closed
cell, including both endpoints and s=2. `selected_atom_le_original` then
uses the prior next-generation closed-min owner and preceding-generation
maximum provenance. `selected_lookup_le_original` gives the actual new
closed lookup <= the old real profile at the actual physical argument.
The owner is not recomputed from the old table.

## 4. Same-Q selected arithmetic gain

`Part5OriginalH430SelectedFeedbackGain.selectedGain` is the labelled sum of
the NEW decoded lookup times its ACTUAL parent thetaAtom. It is not defined
as an ideal integral. `selectedPrimeGain` is the existing literal strict
prime-child sum evaluated against the OLD arrays.

`selectedGain_le_prime_add_error` first multiplies the new scalar inequality
by the nonnegative actual parent mass, then uses the already supplied
absolute applied-profile error. `uniform_selected_feedback_gain` supplies
one threshold before N, refinement, mesh, cell, generations and marks:

    0 <= selectedGain,
    selectedGain <= selectedPrimeGain + epsilon * selectedTheta,
    selectedTheta = 0 -> selectedGain = 0.

There is no division by Theta. The zero-mass theorem uses nonnegativity of
the labelled parent weights before any normalization. It does not assume
that a signed sum of errors being zero forces its coefficients to vanish.

`uniform_selected_outer_feedback_gain` aggregates only AFTER the same-Q
cell estimates. Each original root cell keeps its own Q; the right side
is the sum of those cell normalizers, not a fictitious common Q for all
roots. Generation and mark functions remain explicit inputs until the
original count histories are identified.

## Remaining obligations — not renamed as interfaces

1. Bind all original U3/U4 selected count histories, generation assignments,
   positive marks, owner multiplicities and inherited/full/selected filters
   to the corresponding Member subfamilies. The existing catalog completeness
   and derived common residual floor apply to the stated geometric class;
   they do not prove that the entire original count source has that form.
2. Supply the all-bank physical W1/W2 component realization, original source
   endpoints/repeat lanes/inherited masks, and their finite rounded weights.
   This packet covers the TWO Buchstab actions, not all106 analytic actions.
3. Supply ordinary/fixed/switched bases, the adopted analytic positive seed,
   source count licences and the required same-rho positive-product inputs.
   A feedback-mass comparison does not by itself license an H/h count defect.
4. Pay full native-history proper/equality/inherit symmetric differences,
   native outer integral/Theta/count conversion, and construct ONE nested
   causal refinement through 430+11 levels in the original reserve order.
5. Stage the full held dependency closure; elaborate, compile, replay the
   kernel and audit transitive axioms, including the new finite log binding.

The earlier specific suffix/real-profile comparison obligation is now
covered in source. The actual eventual h34 count bound is NOT declared.
No manuscript counterexample, new seed, changed c/K, changed root norm7/2,
changed row budget12, or replacement of the 441-level construction is claimed.

## Staging and status

Use the unchanged Lean v4.33.0-rc1 / Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` / native goldbach
`09b97db5764ade1246bfb77206baa1b124760958` pins. Install the existing held
imports first, then these new modules in this order:

1. Part5OriginalH430LiteralLogBinding
2. Part5OriginalH430SuffixIntegral
3. Part5OriginalH430OwnedBuchstabLower
4. Part5OriginalH430SelectedFeedbackGain

Static token/delimiter/import/whitespace scans and patch byte round trips
are not Lean parsing or verification. New-source hashes and exact direct
source pins are recorded in REGISTRY.json. No green node is added.

Narrow new blue descriptions (delivery response supplies the commit):

    蓝｜430原logWeights闭式认证源码、逐项floor suffix到闭owner实际Buchstab积分下界
    蓝｜本代选中closed值到前代真实素数反馈和的同Q定向供应及零Theta/外层聚合
    黄｜原始U3/U4完整selected-count历史/代数/正权重绑定、全bank解析许可与441共同细化
