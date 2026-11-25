# Cell00 row00: original finite geometry arithmetic

**Status: SOURCE ONLY. No new Lean compile, independent replay or complete
owned-declaration audit has run for this row00 candidate.** The existing core,
payload and stored-floor acceptance does not certify the new geometry equalities.

## Exact target

`P2Saving16Cell00Row00Arithmetic.lean` contains fifteen public source declarations.
Its two data definitions retain the existing record and vertex lookup:

```lean
def row : SimplexRecord := simplex00
def vertices : Fin 9 → QPoint := simplexVertices cell00Payload row
```

The original ordered vertex IDs are `[15, 14, 13, 9, 7, 6, 3, 1, 0]`.
No independent point array or rational literal is generated. The final target is
exactly the existing predicate:

```lean
theorem simplex_valid : simplexValid cell00Payload (0 : Fin 8)
```

The candidate keeps all eleven conjuncts of `simplexValid`. Existing shape
certificates supply the simplex ID, nine vertex IDs, their bounds and ten stored
means. New closed computations supply the following four separate statements:

```lean
volume_eq : row.physicalVolume = physicalVolumeQ vertices
mean_gap_eq : row.meanGap = gapTotalQ vertices / 9
ten_means_eq : ∀ j : Fin 10,
  row.gapWeightedMeans.getD j.val 0 = meansQ vertices j
stored_jensen_expression : row.jensenBound =
  4 * row.physicalVolume * row.meanGap /
    ∏ j : Fin 10, row.gapWeightedMeans.getD j.val 0
```

Positive stored volume and mean gap are checked separately. Their positivity is
transported to the computed volume and gap sum using the preceding equalities,
so the determinant and gap sum are not evaluated a second time for positivity.
Congruence of multiplication, division and the finite product then proves
`row.jensenBound = jensenQ vertices`. The accepted
`simplex00_stored_jensen_floor` is transported through that equality to obtain the
last original conjunct. There is no new floor computation or combined row decision.

## Prior evidence and reuse

| Component | Exact known acceptance | Reuse boundary |
|---|---|---|
| Original `P2OriginalSaving16FiniteCore` | P3 strict normal, independent replay, full-owned audit; 29 declarations | Same original definitions and guard, source `552f7ac2…` |
| `P2Saving16Cell00TypedPayload` | P3 strict normal, independent replay, full-owned audit; 544 declarations | Typed data only; exact decoder binding is a separate proof |
| `P2Saving16Cell00StoredFloors` | P3 strict normal, independent replay, full-owned audit; 30 declarations | Stored-bound floors, counts and shape; no geometric Jensen identity |
| Existing `P2Winner9FastDetPure` | Historical normal and independent leanchecker passed with exact same source/object | No matching complete-owned/current P3 acceptance was found in the inspected records |
| Current analytic `SimplexMoments` / `JensenFloor` closure | Round2 acceptance pending at preparation | Existing analytic source is not promoted to accepted here |

The actual P3 payload/floor result is in the repository archive
`docs/verification/20261126-p2-5-continuation/payload_floors_and_chars_attempt002.tar.gz`,
member `p25-payload-floors-attempt001/RESULT.json`. The manifest records its exact
hash, both accepted object hashes and all three successful stages. The finite-core
receipt is the existing `remote/p25-finite-core-attempt001/RESULT.json`.

The FastDet source is copied **byte for byte**, with its existing full module name,
from the prior P26 representation package. It is not a new algorithm or a new
namespace extraction. Its source SHA256 is
`d1a0d2ae8af1cf90e05af11b983c5c41ea97a42387eb6c6b9c32ff176e2258ac`;
the existing object SHA256 is
`abd3a41b786826af3d608a50de7096dda26fe7034970340789063647b88bd64c`.
Its force and determinant blocks also match the current heavy
`P2Winner9RowArithmeticChecker` source exactly. Only its lightweight Pure module
is imported by the new candidate.

The historical FastDet normal/replay receipts and logs are preserved in `evidence/`.
They report 2.408s and 1.901s, respectively; both exit successfully and name the
same source/object. Their normal command did not use `warningAsError` and the
printed public theorem has only `propext`, `Classical.choice` and `Quot.sound`.
This is not a claim that the full private/generated declaration inventory has
already passed the present acceptance rules. The supplied local P1 blue-member
evidence root was searched once for the exact Pure FQN and source hash; no match
was found. No remote query job was submitted.

The P26 row000 and all56 arithmetic packages provide prior successful use of the
same representation pattern, but they concern saving19: 28 vertices, 56 rows and
different comparison/cap functions. None of their concrete row equalities is used
for the present saving16 data.

## Mathematical normalization

The manuscript is pinned to
`UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`.
The local `argument.tex` and `numerical-appendix.tex` Git blobs were checked against
that pin's existing inventory. The exact paths and hashes are in `MANIFEST.json`.

The numerical appendix's `num:simplex-moment` gives, in dimension eight,

\[
\int_T \lambda_i = \frac{\operatorname{vol}(T)}9,\qquad
\int_T \lambda_i\lambda_k =
\frac{\operatorname{vol}(T)(1+\mathbf1_{i=k})}{9\cdot10}.
\]

For vertex gap values \(g_i\), factor values \(\ell_{ij}\) and
\(G=\sum_i g_i\), this yields exactly the existing core formulas

\[
\overline g=G/9,\qquad
\overline\ell_j=
\frac{\sum_i\ell_{ij}+(\sum_i g_i\ell_{ij})/G}{10}.
\]

The argument's `eq:current-eighth-saving` has density
\(4(M-R)/((R-S)(M-S)\prod_i t_i)\). Hence the existing rational Jensen expression
is \(4V\overline g/\prod_{j=0}^9\overline\ell_j\). Both residual factors and all
eight coordinate factors are retained through the unchanged `meansQ` and
`factorsQ`. The geometric volume is \(V=|\det E|/8!\). This geometric divisor is
not an additional ordering factorial; no Chen quarter or further factorial is
introduced.

## Expression cost and first future test

Pinned Mathlib defines `Matrix.det` by the Leibniz sum over permutations. For an
8 by 8 rational matrix that has 8! terms before the products and rational
normalizations. The existing generic theorem

```lean
P2Winner9FastDetPure.fastDet_eq {n : Nat}
  (A : Matrix (Fin n) (Fin n) ℚ) : fastDet A = A.det
```

permits the same volume specification to be reduced by exact Gaussian elimination
with materialized rational entries/minors. This is an expression representation
change backed by its existing proof; it does not change the mathematical volume.
No current row00 timing or memory measurement has been made.

The first new numerical obligation in the candidate is `volume_eq`. After the
unchanged FastDet source/object has the required acceptance evidence, the smallest
useful test is this exact row00 source against accepted core/payload/floor objects,
with strict normal, independent replay and complete-owned audit. It imports no
Chars, FieldDecode, OriginalParse or all-cell finite-guard module. If volume fails,
its actual log should determine the next subdivision; the other seven rows should
not be generated or run before this pilot is understood.

## Remaining scope

This candidate does not connect the named payload to `originalText0` or `archive 0`;
that still uses the separate exact decoder and canonical consumer chain. It does
not certify the other seven cell00 simplices, compute the original
`cellFloorNumerator`, certify the other thirteen cells, prove vertex membership in
the physical source cell, prove pulling ownership or prove an integral endpoint.
The remaining closed arithmetic equalities are untested: source plausibility is
not their acceptance, and no new success hypothesis fills them.
