# P5.6 / h34 — two actual Buchstab rows: interior limits and local mass

Date: 2026-11-03. Parent commit: `a0dd5d1ec20162522d6d379352b8c5fd56521c74`.

**PARTIAL_SOURCE_INCREMENT. Whole h34 / full Member / common441 remains OPEN.**
This packet supplies proof-source bodies for the local Buchstab interior
prime-to-native-atom passage that the previous ceiling packet left open.
It also supplies their actual arithmetic row mass bound. It does not prove
the original U3+U4 count inequality or supply the whole h34 argument.

Seven new Lean files: 1,576 lines, 74 theorem declarations, 22 definitions
and one abbreviation. No existing file is changed. P1.4 and P3.6 are untouched.

`compiled=false`, `kernel_verified=false`, `formal_credit=0`.
No Lean or Lake executable is on PATH. No proof body, inherited finite guard,
seed-only recurrence, or saved-table producer was evaluated. No connected
computer/Codex job or explicit CI dispatch was used. Source review was within
this session, not independent review. Static checks are not kernel evidence.

## Governing source and actual terminal

The original manuscript's `paper/source/manuscript-body.tex:795-895` was read
from `UyNewNas/chen-imbalanced-semiprimes`, blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. It specifies positive marked
families at one Q, the true residual exponent and alpha, both positive
Buchstab transitions, preceding-generation reads, closed minima, seed-only430,
and a single nested common441 approximation. The upper root clamp at 2 is a
positive-measure state, not a null set.

The ultimate h34 consumer still requires

```lean
forall delta > 0, eventually N,
  Even N -> currentChenUpsilon3 N + currentChenUpsilon4 N <=
    (originalGroupedU34 + delta) * singularNormalization N
```

The new local terminal does not assume this inequality, a count licence,
a coefficientwise convergence field, or an already supplied common441 graph.
Its exact exported entry is

```text
ImbalancedChen.Part5OriginalH430BuchstabLocalMass.
  immutable430_uniform_buchstab_supply
```

Fix Lmin>0 and epsilon>0. One threshold is selected before N, Q, arbitrary
finite labels, old integer words, physical nodes, ceilings, nonnegative
weights, both directions and generation indices g<430. Each parent must
satisfy the original parentWindow, the actual residual/ceiling identities,
parent argument >=1, the original direction guard, and residual >= Lmin.
The theorem supplies both

```text
sum_i sigma_i * sum_b |strictRow_i,b - thetaAtom_i * integralRow_i,b|
                      * |oldAtomValue(precedingH(g_i),precedingh(g_i),b)|
    <= epsilon * parentTheta,

strictRow_i,b >= 0,
sum_i sigma_i * sum_b strictRow_i,b <= 5 * parentTheta.
```

The arrays are the literal immutable seed-only predecessors, not arbitrary
saved replacements. Equal-product histories remain separately labelled.
No division by parentTheta or by an individual cell mass is used.

## Source chain and mathematical increments

### CompactParameterGates

Extends the existing real-parameter finite-net proof to an arbitrary metric
parameter space. It reuses the actual fixed prime-box theorem, signed finite
sandwich and closed-wall-strip payment. This derives uniformity on a compact
parameter set instead of taking a maximum of infinitely many thresholds.

### BuchstabInteriorPrimeLimit

Instantiates that proof on the compact product of residual L and TWO moving
interval endpoints. It covers u in [1/6,1/2], including coincident and reversed
endpoints. Existing W1/W2 convenience lemmas imposed u>=1/5; the original
actual tuple enumeration [1/10,3/5) already covers the larger Buchstab range.
There is no truncation of [1/6,1/5), nor a change of target from N to floor(N^L).
The exact fresh/repeated-prefix localPrimeFactor is restored by the existing
finite multiplier error, uniformly before the moving endpoints and prefix.

### BuchstabMaskedIntervals

Proves exact Pi1-tuple/natural-prime reindexing on the enlarged original
window, then pays the actual d*N deletion using the existing generic prefix
mask estimate. Its d<=N hypothesis is later derived from parentWindow.
A moving singleton contains at most one prime. Each endpoint is bounded by
20/N^(L/10), and any set between the open and closed interval receives the
two-endpoint bound 40/N^(L/10). This pays closed knots and open/closed endpoint
choices in arithmetic; no finite prime fibre is deleted using Lebesgue nullity.

### BuchstabAtomIntervalGeometry

The reciprocal map u=1/(w+1) converts all 200 open-cell and 201 knot atoms,
including the actual physical ceiling in physicalStart, to mixed-endpoint
intervals inside [1/6,1/2]. Empty rows, start>5, and singleton rows are kept.
Only a bounded endpoint parameter is used; the physical query and original
LocalDomain are not replaced by a clipped surrogate.

An actual injective change of variables proves the interval integral equals
the existing atomMass. A separate equality identifies the existing native
physical integral with physicalWeight(parent)*atomMass. Arithmetic parent
Theta and continuous physicalWeight are NOT identified with one another.
The full outer prime integration relating those parent measures remains open.

### BuchstabInteriorDictionary

Binds the original closedChildren to the d*N-deleted atom sum in BOTH directions,
including the converse and the natural-prime to Fin(N+1) conversion. Finite
support follows from the existing local square/product geometry, not a new
support premise. It factors each actual coefficient into parent thetaAtom
and the exact normalized prime mass. The ideal row is the existing atomMass,
with original polarity: upper parent reads old h, lower parent reads old H.

### BuchstabAbsoluteSupplier

Takes absolute values coefficient by coefficient, multiplies by the actual
old atom values, then sums over positive parent labels. It combines the new
interior error with the preceding ceiling packet by a triangle inequality.
The ceiling-to-strict correction is charged once. The finite old-array L1
envelope is a threshold device, not a replacement for the original norm12.
The explicit zero-Theta theorem is proved in absolute form before division.

### BuchstabLocalMass

Uses the actual constant-one closed table to show the SUM of ideal atom
masses is at most 4, rather than paying that bound 401 times. The true uniform
atom estimate then gives arithmetic strict-row mass <=5*parentTheta for large
N. Thus these two rows fit within the original allowance12 without assuming
that allowance as an input. Also derives physicalLevel<=1 from parentWindow;
the final joint supplier retains no arbitrary compact upper-residual premise.

## Removed versus remaining obligations

Supplied in this narrow source scope: the full [1/6,1/2] local prime limit;
simultaneous residual/two-endpoint uniformity; actual prefix deletion; every
finite endpoint/knot payment; exact original local carrier reindexing;
arithmetic-to-existing-native-atom main terms; immutable430 coefficientwise
absolute lifting; and the two actual local arithmetic row mass bounds.

Still required for the WHOLE h34 terminal:

1. Bind actual U3/U4 roots and all descendants to the complete original
   Program.Member source with incomingAllowed, cellMember, ownership, full
   and selected histories, and all parent query/cutoff admission tests.
   LocalDomain alone is not this complete graph.
2. Supply all proper/equality/inherit strata and their full native-domain
   errors. Keeping the local lower s=2 guard does not establish its stability
   under a common moving full-history refinement.
3. Supply the original ordinary/fixed/switched base and count inequalities,
   adopted seed/count licences, and all same-source analytic PP inputs.
   A true prime-Theta coefficient limit is not a Buchstab count inequality.
4. Identify full outer parent-Theta integration with the physical native
   measure, and derive a common positive lower residual floor for every actual
   graph node. Only the upper bound<=1 is eliminated in this packet.
5. Construct one nested causal pre-N refinement through 430+11 levels, with
   actual source/interpreter correspondence and all bases, then instantiate
   the original error propagation and root U3/U4 count consumer.
6. Stage and compile the exact held import closure, replay the kernel and
   audit transitive axioms. Existing held dependencies are not revalidated.

The original c, K, 430 interpreter, norm12, root norm7/2 and common441 budget
are unchanged. No new contradiction to the manuscript is claimed.

## Validation and staging

Text checks found no admission, new-axiom, unsafe or native-evaluation tokens,
no trailing whitespace, and balanced delimiters after removing nested comments
and strings. These are NOT a Lean parse/elaboration/proof check. Exact bytes,
SHA256, Git blob hashes, declaration counts and direct imports are recorded in REGISTRY.
Only directly used API statements and the cited source sections were inspected;
this is not a full dependency-closure audit or an independent review.

Stage existing source-only imports at their intended ImbalancedChen module
paths; seven files alone do not constitute a compilable dependency closure.
The new modules must be staged in this order:

1. Part5OriginalH430CompactParameterGates
2. Part5OriginalH430BuchstabInteriorPrimeLimit
3. Part5OriginalH430BuchstabMaskedIntervals
4. Part5OriginalH430BuchstabAtomIntervalGeometry
5. Part5OriginalH430BuchstabInteriorDictionary
6. Part5OriginalH430BuchstabAbsoluteSupplier
7. Part5OriginalH430BuchstabLocalMass

Principal kernel/axiom targets: compact_uniform_parameter_gates,
compact_uniform_masked_interval, atomMass_eq_interval,
closedAtom_eq_windowMass, uniform_closed_row_atom_error,
immutable430_uniform_buchstab_absolute, immutable430_uniform_buchstab_zero,
atomMass_sum_le_four, uniform_buchstab_row_mass,
and immutable430_uniform_buchstab_supply.

## Status-tree delta

```text
黄｜全Member proper/equality层质量、全native域误差、完整外层Theta与immutable430/441共同realization
    蓝｜双Buchstab局部实际算术行到native原子积分、moving-L/双端点统一逐系数绝对误差及430代同Q已准入父族供应（source-only，未编译）
    蓝｜双Buchstab局部实际行质量≤5Theta及parentWindow导出残差上界≤1（source-only，未编译）
```

Only these narrowly stated source scopes have new coverage. Their yellow
parent, h34, P5.6 and the overall theorem are not upgraded.
