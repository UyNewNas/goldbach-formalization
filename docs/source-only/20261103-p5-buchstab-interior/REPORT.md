# P5.6 / h34 — actual Buchstab interior rows and local mass

Date: 2026-11-03. Intended base: `a0dd5d1ec20162522d6d379352b8c5fd56521c74`.
Repository: `UyNewNas/goldbach-formalization`.

**PARTIAL_SOURCE_INCREMENT. The whole h34 / full-Member / 441 scope is OPEN.**
Seven new Lean files contain proof bodies for the local interior-prime-to-integral
chain, its literal production-carrier binding, the immutable430 coefficientwise
absolute budget, and a positive local row-mass bound. This is not a new h34 theorem.

`compiled=false`, `kernel_verified=false`, `formal_credit=0`,
`proof_bodies=UNEVALUATED`, `independent_review=false`.
Existing held dependencies and their finite computations remain UNEVALUATED.
No Lean/Lake/compiler, kernel replay, numerical table evaluation, CI, Codex job,
connected computer, quota query, or child agent was used.

**Delivery is local only.** The GitHub actions exposed in this session provide
reads but no create-blob/tree/commit/ref operation. Plugin discovery found the
installed GitHub integration, but no additional write action was exposed. The
container has git, but no gh, Lean or Lake. No remote branch or commit is claimed.
The source ZIP and additive patch are the deliverables. A Git blob hash in the
registry is a content identifier calculated locally, not evidence of publication.

## Exact selected yellow and terminal

The selected scope remains P5.6 -> h34 ->

> 全Member proper/equality层质量、全native域误差、完整外层Theta与immutable430/441共同realization

The production terminal remains the original eventual estimate

```lean
forall delta : Real, 0 < delta -> eventually N atTop,
  Even N -> currentChenUpsilon3 N + currentChenUpsilon4 N <=
    (originalGroupedU34 + delta) * singularNormalization N
```

The display above is explanatory pseudocode for the existing production h34
argument, not a newly declared Lean theorem. This packet does NOT supply it.

S18 retained the two actual Buchstab arithmetic rows as an outstanding piece.
The previous a0dd5d1 packet paid only their strict/closed ceiling discrepancy.
This continuation addresses the previously unpaid interior at the same Q and
literal old word. It does not edit P1.4, P3.6, production files, or older packets.

The manuscript was re-read at `paper/source/manuscript-body.tex:795-895` in
`UyNewNas/chen-imbalanced-semiprimes`; the retrieved Git blob was
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. It explicitly requires one positive
marked family at one Q, preceding-generation reads, the original two Buchstab
actions, closed minima, a nested common refinement, the 12 row budget, root norm
7/2, and a positive residual floor through the finite 430+11 construction. The
new local result does not replace any of these requirements with finite depth.

## Source chain

### 1. Compact parameter and boundary theorem

`Part5OriginalCompactParameterSandwich.lean` extends the existing O finite-net
proof from a single real parameter to an arbitrary compact metric parameter
space. Fixed-center actual prime-wall strip estimates, the genuine prime-box
limit, and compactness of the continuous kernel are reused.

There are two finite covers. The first pays oscillation of the strict affine
selector and the kernel. The second pays the difference between an arbitrary
open/closed affine sandwich and its strict interior. In the second cover a
boundary prime lies on an actual moving wall and hence inside a fixed-center
closed strip. The strip's arithmetic mass is paid before the integral AE
identification. Even an atom with empty strict interior can therefore retain
its finite arithmetic contribution. No uniform-limit or endpoint-prime-mass
hypothesis is added.

### 2. Joint residual/start and all closed table atoms

`Part5OriginalBuchstabCompactAtoms.lean` reboxes supported selectors exactly and
applies the parameter theorem jointly to `(L,c)`. The original integer target
is N throughout, not an integer surrogate for N^L.

The normalized prime coordinate is u; its actual query is w=1/u-1. For c>=1,

```text
atomDomain(up,b,c)
 = { u : 1/6 <= u <= 1/(c+1),  w in tableAtomSet(up,b) }.
```

Both the 200 open cells and 201 singleton knots are retained for each polarity.
The affine normals are fixed. Their nonzeroness is proved only at the actual
support and grid coefficients; the false stronger condition
`coord + t*coord != 0 for every real t` is not used.

The conclusion has one threshold before L in its fixed positive compact
interval, c in [1,6], both directions, and every table atom.

### 3. Exact arithmetic factors and the original d*N mask

`Part5OriginalBuchstabTrueAtomLimits.lean` first reindexes the actual one-prime
box into the original half-open prime window, without a factorial or ordering
quotient. It then uses the exact localPrimeFactor (1/p on repeated-prefix lanes,
1/(p-2) on fresh lanes) and the existing proved multiplier-error estimate.
The original Buchstab child mask excludes prime divisors of d*N, whereas the
unmasked prime-limit carrier excludes only divisors of N. The existing prefix
mask theorem pays this difference with a fixed N^(Lmin/10) floor and d<=N.
It is not silently identified away.

Arbitrary c>=1 is handled by the exact identity
`Icc (min c 6) 5 = Icc c 5`. The cap is 6, NOT 5: a start above 5 must remain
empty, not become the singleton {5}. All finite knot/endpoint terms remain in
the actual sum until the arithmetic estimate has controlled them.

### 4. Genuine native integral dictionary

`Part5OriginalBuchstabNativeAtomDictionary.lean` converts Pi1 volume to real
Lebesgue volume, then uses the actual injective map u=1/(w+1), its derivative,
and the original residual kernel. It obtains

```text
normalizedAtomIntegral(up,b,c) = atomMass(up,b,c)
                               = integral over [c,5] cap atom of dw/w.
```

R15's existing native-x change of variables then gives the actual
nativeAtomCoefficient as physicalWeight(parent) times this normalized atom.
The physical weight and arithmetic thetaAtom are NOT declared equal. No
division by either mass is used. Full outer native/Theta conversion is still
not supplied by this local identity.

### 5. Literal closed and strict production carriers

`Part5OriginalBuchstabActualRowLimits.lean` proves the exact two-way dictionary
between the normalized atom and the literal LocalDomain at the actual prime
coordinate. Product support and the finite N+1 enumeration cap are derived
from the existing local geometry; the natural-to-Fin conversion is proved in
the sum reindexing.

It supplies, before limits,

```text
closedAtom = thetaAtom(N,Q,d) * maskedAtom(N,L,d,...).
```

The physical level is the actual log(Q/d)/log(N). The unchanged parentWindow
already gives Q<=N and d>=1, so L<=1 is proved instead of requested as a new
upper-bound field. The positive lower floor Lmin remains an explicit, genuine
full-history obligation.

Upper-parent reads the old h polarity; lower-parent reads old H. The scalar
is one. The proof works for the actual lower s=2 case but does not assert
stability of that guard along the full frozen history.

The endpoint `uniform_closedRow_error` pays every actual closed arithmetic
coefficient against the real normalized integral, uniformly before the parent,
its query/ceiling, the common Q and the atom.

### 6. Original immutable430 absolute budget

`Part5OriginalBuchstabImmutable430Budget.lean` applies the new coefficient
estimate to the literal existing `precedingH g` / `precedingh g` arrays for
every g<430. These arrays are not evaluated or substituted by saved tables.
The old finite L1 envelope is only a threshold device, not a replacement for
the manuscript's row norm.

The strongest error terminal is

```text
ImbalancedChen.Part5OriginalBuchstabImmutable430Budget.
  immutable430_uniform_buchstab_rows
```

For fixed Lmin>0 and epsilon>0, it chooses a single T BEFORE N,Q and every
finite positive labelled family, actual old word, physical parent, ceiling,
direction and predecessor generation. It supplies

```text
sum_i sigma_i * sum_b
  |strictRow_i,b - thetaAtom_i * integralRow_i,b| * |oldAtomValue_i,b|
  <= epsilon * parentTheta.
```

This uses the original production strict children, not just the enlarged
closed carrier: the new interior budget and a0dd5d1's ceiling budget each
receive epsilon/2. Equal-product histories are not quotiented. The absolute
zero-Theta conclusion follows before any normalization. A signed applied-row
estimate is derived FROM coefficientwise absolute control, not conversely.

Visible geometric premises are the original parentWindow, actual residual
and ceiling identification, parent argument>=1, the original lower-direction
guard, nonnegative marks, and the common positive residual floor. None is an
assumption of h34, a prime-to-integral limit, or the desired coefficient error.

### 7. Actual positive Buchstab row mass

`Part5OriginalBuchstabRowMass.lean` proves coefficient nonnegativity for the
literal strict carrier. Constant-one closed tables are used only to measure
mass; they are not proposed as a new analytic seed. The original table guards
remain present, and the ideal row mass is at most four.

The uniform coefficient error 1/802 pays the finite total row error. Positivity
of the ceiling coefficients permits passage from the closed to the strict row.
`uniform_strictRow_mass` gives the actual eventual bound

```text
sum_b strictRow_b <= 5 * thetaAtom(parent).
```

`uniform_labelled_row_mass` lifts it to arbitrary nonnegative labelled families
at one Q, with no positive-total-Theta premise. This is compatible with the
unchanged manuscript bound twelve. It supplies the two local Buchstab row-mass
inputs, not an all-history hmass certificate for the complete 441-level graph.

## Precise remaining scope

The whole yellow remains open. The following are NOT hidden in a new record:

1. Actual U3/U4 integer-root and every original causal descendant, source
   coefficient, incomingAllowed/cellMember/owner and full/selected-history
   filter must be identified with one full Member graph and these local rows.
2. Proper versus stable equality/inherit strata for the entire history and
   native weighted symmetric differences, including the moving lower s=2
   guard, still need the original full-family proof.
3. One common positive residual floor and all parent-query admissions must be
   instantiated for every actual physical/arithmetic parent used downstream.
   Local parentWindow supplies the upper bound; it does not supply the whole
   original-history identification or its uniform positive lower floor.
4. Ordinary/fixed/switched bases, positive bad-D5 costs, true-alpha switching
   costs, analytic seed/count licences and the requisite same-rho PP source
   remain outside this local feedback calculation.
5. Full native outer parent integration/Theta correspondence and the actual
   closed-minimum / per-product-floor / retained-maximum realization of the
   immutable interpreter remain necessary.
6. A single nested causal smooth refinement through 430+11 levels, in the
   original reserve -> delta -> refinement/tau/caps -> N0 order, must still be
   constructed and used to instantiate the final h34 consumer. Taking maxima
   of arithmetic thresholds here does not construct that refinement.
7. Same-source elaboration, compilation, kernel replay, and transitive axiom
   checking remain outstanding for this packet and its held import closure.

No counterexample to the manuscript is claimed. The new work is a proposed
source proof of a local omitted deduction; API/elaboration and larger source
assembly obligations remain explicit. c=49044063/25000000, K=8452171/1250000,
root norm7/2, row budget12 and the 430+11 history are unchanged.

## Validation and staging

The seven Lean files contain 1,556 lines, 69 theorem declarations and 22
other definitions. Static text checks found no admission/axiom/unsafe/native
evaluation tokens outside comments, no trailing whitespace, and balanced
brackets/comments/strings. Exact new-source SHA256 and Git blob identifiers,
declaration lists, imports and known dependency pins are in REGISTRY.json.
These checks are NOT a Lean parser, a proof check, or an independent review.

The patch adds only this new directory. From an appropriate checkout containing
a0dd5d1 and with no conflicting local files, the normal application commands are:

```sh
git apply --check /path/to/p5-h34-buchstab-interior-20261103.patch
git apply /path/to/p5-h34-buchstab-interior-20261103.patch
```

A temporary empty-directory patch round-trip checks only additive patch syntax
and byte preservation, not integration into the full repository or Lean validity.
The ZIP contains the same nine new files. No remote commit or branch is created.

To stage Lean later, materialize the pinned held import closure into the intended
`ImbalancedChen.*` module paths first. Copying only the seven new files is not a
complete import installation. The order of the new modules is:

1. Part5OriginalCompactParameterSandwich
2. Part5OriginalBuchstabCompactAtoms
3. Part5OriginalBuchstabTrueAtomLimits
4. Part5OriginalBuchstabNativeAtomDictionary
5. Part5OriginalBuchstabActualRowLimits
6. Part5OriginalBuchstabImmutable430Budget
7. Part5OriginalBuchstabRowMass

Use the existing Lean v4.33.0-rc1 / pinned Mathlib / pinned native dependency
recorded in the registry, without silently upgrading them. Future validation
should inspect the actual transitive axioms of the prime-limit supplier as well
as the new terminals. A passing check would credit this narrow row chain only.

## Status-tree delta

```text
黄｜全Member proper/equality层质量、全native域误差、完整外层Theta与immutable430/441共同realization
    蓝｜双Buchstab实际strict/closed ceiling字典、同Q逐系数绝对修正与430代统一阈值（上一轮）
    蓝｜双Buchstab原始内部素数和→native积分、moving L/start全闭原子与immutable430同Q绝对预算（本轮source-only）
    蓝｜双Buchstab实际正系数行质量≤5Theta及同Q非负标记族聚合（本轮source-only）
```

This is an artifact-local proposed status delta, not an update to a remote
project board. The parent yellow, h34, P5.6 and the overall theorem retain their
previous states. No green node is asserted.
