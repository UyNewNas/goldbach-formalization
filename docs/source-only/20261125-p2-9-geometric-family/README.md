# P2.9: original Gamma5 geometric Family

The fixed manuscript is release-20261106, commit
`a988cba584d803ae2856a0de50efb582f4f3dd6a`. The repository baseline is
`a929011ec95843553fc2e10b7291c8077e0952c0`.

**These are source candidates. This directory initially records exact
extraction and static dependency checks, with no new ordinary-compilation,
kernel-replay, or owned-declaration acceptance.** Acceptance must bind the
actual final source bytes to each of those three independent gates.

## The original interface is preserved

`ImbalancedChen.P2Gamma5AdmissibleFamilyCore` contains the original
`ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily.Family`
structure. Its declaration is 823 bytes, SHA256
`f49c2f2841c86a101eb672d102e86ab1dd4dbbce7b19b705b7299fb61d70ca7b`.
The name, field order, field types, and declaration bytes are unchanged.
The block agrees with both the original full preimage and the existing
postimage of the earlier Euler-operator extraction.

The core imports the already accepted original Euler-operator core and
standard Mathlib prime definitions. It imports no native research module
or heavy arithmetic-history owner. In particular, it defines no parallel
Family and introduces no replacement predicate for its support or Euler
conditions.

`owner-preimages/` preserves the previous complete owner. The new
`owner-postimages/` file adds the core import and removes only the exact
structure segment, including its leading comments. Removing the added
import and reinserting that segment reconstructs the previous owner
byte for byte. Existing archived owners are unchanged. A later joint
import of the heavy owner and this core must select the new postimage;
an earlier owner that still declares `Family` cannot be imported with it.

The new generated constructor, projections, recursors and auxiliaries
must be audited as complete owned declarations after compilation. The
heavy owner's postimage has no new acceptance from this extraction.

## Constructed Family and exact agreement

`ImbalancedChen.P2FiniteMarkedGamma5GeometricFamily.geometricFamily`
constructs an inhabitant of the original `Family K` for numerical inputs

- fixed `a > 0` and fixed `0 < width ≤ 1`;
- an arbitrary fixed function `logQ : ℕ → ℝ`;
- a fixed old/tail split `(k, r)` with `k + 2 + r ≤ K`.

Put `h = k + (2 + r)` and use the already accepted threshold

\[
N_0(a)=\max\{\exp(1),2^{2/a}\}.
\]

At rank `h` and scale `T ≥ N0(a)`, the ambient function is exactly

\[
v\longmapsto\operatorname{finPhysicalProfile}_{k,r}
  (\operatorname{logQ}(T),T,\mathrm{width},T^a)(v).
\]

At every other rank it is zero. Below `N0(a)` it is zero at every rank.
The only coordinate transport is `Fin.cast` along equality with `h`;
there is no extra permutation or collapse of slots. The old, two fresh,
and rough coordinates retain the accepted slot numbering.

`geometricFamily_at_rank` is equality of functions on the whole real
coordinate space at the intended rank and above the threshold.
`geometricFamily_zero_below_threshold` records the scale truncation,
and `finite_below_threshold` proves that the altered natural-number
scales form a finite initial set. No all-scale equality to the original
profile is asserted.

## Discharged structure fields

The instance uses `aStar = a`, `lower = 1/2`, and `upper = exp 1`.
At an active scale, the original nonzero-support theorem gives

\[
\frac{T^a}{2}<v_i,
\qquad
\prod_i v_i<\exp(\mathrm{width})T\le\exp(1)T.
\]

These imply the original real support field directly. The unchanged
profile supplies smoothness. The new integer-support module proves
finite support on all natural tuples; the prime-support field is its
subset. The zero branches discharge the same fields without adding
arithmetic hypotheses.

For every order `m`, the existing bounded-rank mixed-Euler theorem gives
a nonnegative real constant `C0(K,m)` before the moving parameters.
The instance chooses a positive natural constant

\[
C_m=\left\lceil C_0(K,m)(1+\mathrm{width}^{-1})^m\right\rceil_{\mathbb N}+1,
\qquad B_m=0.
\]

`ambient_mixedEuler_budget` selects this constant before `a`, `logQ`,
`k`, `r`, `T`, the rank, the word, and the physical point. The width is
fixed before this choice. Thus the proof does not claim a constant
uniform over arbitrary widths tending to zero.

## Dependency and completion boundary

`SOURCE_CLOSURE.json` records a 15-module project closure: 11 exact
previously accepted project sources, one existing owner with a new
public API forwarder, and the three current candidates
`P2FiniteMarkedGamma5IntegerSupport`, `P2Gamma5AdmissibleFamilyCore`,
and `P2FiniteMarkedGamma5GeometricFamily`. Every external boundary is
standard Mathlib; there are zero direct native roots and no native
qualification extension.

The existing `P2FiniteMarkedGamma5AllRankEulerBudget` owner contained a
private zero-word theorem. Its new public `eulerWord_zero_eq` theorem is
only the term `eulerWord_zero w`, reusing that existing proof. Removing
the added comment/declaration segment recovers all prior owner bytes
exactly. `PUBLIC_API_FORWARDER.json` records the former accepted source,
the exact insertion and the new source hash. The previous acceptance
applies only to the former hash; the modified owner requires the three
gates again. No private compiler-generated name is called by the Family
consumer.

This construction activates one fixed old/tail split. It does not prove
that every actual arithmetic history has been connected to this profile,
the actual source plateau, collar payment, a PP/VM estimate, W1/W2
directed payments, or the final endpoint licences. Those obligations
remain explicit. The geometric Family is not a completion claim for
P2.9 or the full P2 development.

The execution plan uses the universal Lean statements as its mathematical
verification specification. The author of these two modules performed
the static extraction and dependency checks only; root performs the
existing strict compilation, stock replay and complete owned audit in
the isolated P2 environment. No old archived proof was rewritten, no
compiler was invoked by this task's author, and no Git commit was made
by this task's author.
