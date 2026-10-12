# Part 1 round 2: stored historical cap permit types

**Status: VERIFIED.** The independent permit production module, probe,
and audit module passed all three strict `trustLevel = 0` compilations
and all three original `leanchecker` calls. The complete defining-module
census contains 14 production declarations and 22 probe declarations,
with only `propext`, `Classical.choice`, and `Quot.sound` among their
transitive axioms. The final receipt and the exact raw audit log are
bound below. All twelve public source declarations have been matched
by full name, declaration kind, and defining module to that audit;
Appendix A reproduces its actual pretty-printed types.

This verification covers this independent permit interface and its
probes. It does not certify the separate main historical-cell candidates,
a full repository build or replay, or the complete adopted construction.

The working proof baseline remains
`1a80c1bcce67886f699d097fc37fd245cd3620bf`. The previously published P1
source checkpoint is `7f894bfb57b7aa561360e335c6d610b7c30614e0`.
The hash below identifies the new permit source bytes. That checkpoint
is not presented as the source commit or verification receipt for this
new module.

## Extraction scope

All two public definitions and all ten public theorem declaration types
from the module are reproduced below. The definitions include their
complete defining expressions; theorem proof bodies are omitted without
inserting placeholder proofs. Every parameter, dependent cell field,
hypothesis, arithmetic carrier, strict comparison, selected subproduct,
and finite filter is preserved. The headings give fully qualified names;
the code blocks retain their exact source spelling in that namespace.

| Source | Source SHA256 | Definitions | Public theorem types |
| --- | --- | ---: | ---: |
| `ImbalancedChen/StoredHistoricalBoxPermit.lean` | `50a9dc07e98046a664711572bcf69b58a528c0a97502bbd9f75de245dd43bc0d` | 2 | 10 |

The source has only the direct import
`ImbalancedChen.SelectedPrefixRationalMesh`. Its declaration context is
`namespace ImbalancedChen`, `noncomputable section`,
`open scoped BigOperators`, and `open VariableEnvelope`.
The actual defining-module audit also covers the two generated equation
theorems listed below. The source inventory remains the original twelve
public declarations; the complete fourteen-declaration production census
and its actual types are supplied separately. This document records the
results of the bound audit and does not replace its raw log or receipt.

## Meaning and required historical binding

`storedBoxCapCheck` checks the supplied rational `cap` itself against
strict whole-box lower and upper bounds. The cap need not equal the
existing automatic midpoint. The midpoint adapter supplies a compatible
special case. The soundness theorem applies to each point of the closed
real box and retains the precise prefix and selected-subproduct square
expressions, the strict inherited-level comparison, and the envelope
bound involving the actual `v`.

The mesh checker accepts the following separate data:

| Field | Exact type or role |
| --- | --- |
| `n` | Number of logarithmic coordinates, `ℕ`. |
| `a b` | Shared rational mesh endpoints, `ℚ`. |
| `m` | Mesh parameter; each coordinate cell label lies in `Fin (m + 1)`. |
| `J` | Selected cell family, `Finset (Fin n → Fin (m + 1))`. |
| `I` | Per-cell mask, `(Fin n → Fin (m + 1)) → Finset (Fin n)`. |
| `old` | Per-cell inherited rational level, `(Fin n → Fin (m + 1)) → ℚ`. |
| `nu` | Per-cell rational ceiling, `(Fin n → Fin (m + 1)) → ℚ`. |
| `cap` | Per-cell rational cap actually stored, `(Fin n → Fin (m + 1)) → ℚ`. |

The outer decider is explicitly
`Finset.decidableDforallFinset (s := J)`. It traverses the selected
finite family rather than enumerating the entire cell-label function
space. Its local lower and upper bounds retain the existing finite
coordinate and mask computations.

**The caller must identify `old j` with the actual inherited historical
value on cell `j`.** For example, use of a fifth-level certificate would
require a separate binding to the effective fourth ancestor value such
as `D.old5 j`, including its fallback behavior. An arbitrary smaller
`old j` that makes the finite check pass does not license replacement
of the actual historical policy. The current module neither imports the
historical policy package nor proves this identity. The theorem
`storedMeshCapCheck_old_lt` projects only the comparison with the supplied
field and leaves its historical interpretation to that binding proof.

The intended certificate use fixes `a`, `b`, `m`, `J`, `I`, `old`, `nu`,
and `cap` before varying the target `N`; the actual-square theorems then
introduce `N`, the labels `p`, and their coordinate bounds. The checker
contains no target argument. The caller must use that same fixed data
when supplying a family of target instances.

The mesh soundness and actual-square conclusions use membership in the
original `logPrimeMeshCell`, whose coordinate cells are left closed and
right open. The proof only weakens the upper point inequality when
invoking closed-box soundness. It does not change cell ownership or
strict cap/product endpoints. The square-product formulas apply to
natural labels satisfying the displayed power bounds; actual primality,
`p ∤ N`, sorting, and frontier membership remain inputs of their separate
historical/prime suppliers.

There is no K/c bound, integral estimate, or final analytic estimate in
these finite checks. The module does not assert coverage, an actual Part 2
certificate instance, a complete policy/factorization theorem, or any old
or new own-cube admission. The two own-cube indicators and the historical
fallback must be supplied and kept distinct by their downstream interfaces.

## Verification binding and complete production census

The actual audit log was read from the `log` field of
`new_target_records["verification.parts.p1.round2.permit.StoredCapAudit"]` in
`/workspace/scratch/127408f63891/lean-runtime/logs/round2/permit/compile/result.json`. The source bytes match the hash above before and after
compilation and checker replay. This document preserves the original
source declaration blocks and appends the decoded, unmodified `type`
strings from the matching `PART1_STORED_CAP_AUDIT_DECL` records.
Pretty-printer notation such as `↑` and `∏ i with ...` is retained.
The record match checks full name, kind, and defining module; it does
not assert textual identity between the source syntax and its printed
elaborated form.

| Evidence | SHA256 |
| --- | --- |
| Final receipt, `part1-permit-final-receipt.json` | `7f687c1d1b61ec3142de63f1458b5dcf650928348e6b4231b871a121c99d4ee1` |
| Actual raw audit log | `f942c8432aee8ae28d70dc97dd804ffa0a1323e9f55edfb55d999c5f74a805f5` |
| Actual compile result | `8c91d47aad24ce05dcefba18ec9bd94471644bcc99f2ec973baad4c581ce64a6` |
| Actual original-checker replay result | `a81c420ef5dc2ce7baa3d2d75aeb7ddcad17504775133bc41707c6bff5fff698` |
| Production `.olean` | `c05b355bb77a95468850321807846cfb743955e2a77d5e2aafca02185bc4a8ee` |

Final receipt path:
`/workspace/scratch/127408f63891/lean-runtime/part1-permit-final-receipt.json`.
Its status is `VERIFIED`, recorded at
`2026-10-12T12:56:10.056234+00:00`.
Actual raw audit log path:
`/workspace/scratch/127408f63891/lean-runtime/logs/round2/permit/compile/attempt-20261012T124921086741Z/modules/verification.parts.p1.round2.permit.StoredCapAudit.log`.
The three checker calls replay declarations defined by their selected
modules; imported dependencies are loaded and are not all replayed.

The raw log contains exactly 36 distinct declaration records and reports
module counts of 14 and 22. These counts were checked against the records
and the final receipt. The production set is exactly the twelve public
names plus the following two generated equation theorems, with no omitted
production declaration. All fourteen production records report the same
allowed transitive axiom set: `propext`, `Classical.choice`, `Quot.sound`.

| Full declaration name | Actual kind | Origin |
| --- | --- | --- |
| `ImbalancedChen.storedBoxCapCheck` | `definition` | public source declaration |
| `ImbalancedChen.storedBoxCapCheck_iff` | `theorem` | public source declaration |
| `ImbalancedChen.storedBoxCapCheck_old_lt` | `theorem` | public source declaration |
| `ImbalancedChen.storedBoxCapCheck_midpoint` | `theorem` | public source declaration |
| `ImbalancedChen.storedBoxCapCheck_sound` | `theorem` | public source declaration |
| `ImbalancedChen.storedBoxCapCheck_actual_square_gates` | `theorem` | public source declaration |
| `ImbalancedChen.storedMeshCapCheck` | `definition` | public source declaration |
| `ImbalancedChen.storedMeshCapCheck_iff` | `theorem` | public source declaration |
| `ImbalancedChen.storedMeshCapCheck_old_lt` | `theorem` | public source declaration |
| `ImbalancedChen.storedMeshCapCheck_sound` | `theorem` | public source declaration |
| `ImbalancedChen.storedMeshCapCheck_actual_square_gates` | `theorem` | public source declaration |
| `ImbalancedChen.storedMeshCapCheck_of_selectedBoxCapChecks` | `theorem` | public source declaration |
| `ImbalancedChen.storedBoxCapCheck.eq_1` | `theorem` | generated equation theorem |
| `ImbalancedChen.storedMeshCapCheck.eq_1` | `theorem` | generated equation theorem |

## Complete source declarations

### `ImbalancedChen.storedBoxCapCheck`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
def storedBoxCapCheck {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ) : Bool :=
  decide (selectedCapLower I old hi < cap ∧ cap < selectedCapUpper I nu lo hi)
```

### `ImbalancedChen.storedBoxCapCheck_iff`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
theorem storedBoxCapCheck_iff {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ) :
    storedBoxCapCheck I old nu lo hi cap = true ↔
      selectedCapLower I old hi < cap ∧ cap < selectedCapUpper I nu lo hi
```

### `ImbalancedChen.storedBoxCapCheck_old_lt`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
theorem storedBoxCapCheck_old_lt {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ)
    (hc : storedBoxCapCheck I old nu lo hi cap = true) : old < cap
```

### `ImbalancedChen.storedBoxCapCheck_midpoint`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
theorem storedBoxCapCheck_midpoint {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (hc : selectedBoxCapCheck I old nu lo hi = true) :
    storedBoxCapCheck I old nu lo hi (selectedBoxCap I old nu lo hi) = true
```

### `ImbalancedChen.storedBoxCapCheck_sound`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
theorem storedBoxCapCheck_sound {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ)
    (hc : storedBoxCapCheck I old nu lo hi cap = true)
    (t : Fin n → ℝ) (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    (old : ℝ) < cap ∧ (cap : ℝ) < nu ∧ (1 / 2 : ℝ) < cap ∧
      (∀ j, prefixSquareExpr t j < cap) ∧
      (∀ j ∉ I, selectedSquareExpr I t j < cap) ∧
      (cap : ℝ) < v (∑ i ∈ I, t i)
```

### `ImbalancedChen.storedBoxCapCheck_actual_square_gates`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
theorem storedBoxCapCheck_actual_square_gates {n : ℕ} (I : Finset (Fin n))
    (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ)
    (hc : storedBoxCapCheck I old nu lo hi cap = true)
    (t : Fin n → ℝ) (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ))
    (N : ℝ) (hN : 1 < N) (p : Fin n → ℕ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i) :
    (∀ j, ((∏ i ∈ Finset.univ.filter (fun i => i < j), p i : ℕ) : ℝ) *
      (p j : ℝ) ^ 2 < N ^ (cap : ℝ)) ∧
    (∀ j ∉ I, ((∏ i ∈ I, p i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i => i < j ∧ i ∉ I), p i : ℕ) : ℝ) *
        (p j : ℝ) ^ 2 < N ^ (cap : ℝ))
```

### `ImbalancedChen.storedMeshCapCheck`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
def storedMeshCapCheck {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ) : Bool :=
  @decide _ (Finset.decidableDforallFinset (s := J)
    (p := fun j _ => storedBoxCapCheck (I j) (old j) (nu j)
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) (cap j) = true))
```

### `ImbalancedChen.storedMeshCapCheck_iff`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
theorem storedMeshCapCheck_iff {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ) :
    storedMeshCapCheck a b m J I old nu cap = true ↔
      ∀ j ∈ J, storedBoxCapCheck (I j) (old j) (nu j)
        (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) (cap j) = true
```

### `ImbalancedChen.storedMeshCapCheck_old_lt`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
theorem storedMeshCapCheck_old_lt {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ)
    (hc : storedMeshCapCheck a b m J I old nu cap = true) :
    ∀ j ∈ J, old j < cap j
```

### `ImbalancedChen.storedMeshCapCheck_sound`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
theorem storedMeshCapCheck_sound {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ)
    (hc : storedMeshCapCheck a b m J I old nu cap = true)
    (j : Fin n → Fin (m + 1)) (hj : j ∈ J)
    (t : Fin n → ℝ) (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    (old j : ℝ) < cap j ∧ (cap j : ℝ) < nu j ∧ (1 / 2 : ℝ) < cap j ∧
      (∀ i, prefixSquareExpr t i < cap j) ∧
      (∀ i ∉ I j, selectedSquareExpr (I j) t i < cap j) ∧
      (cap j : ℝ) < v (∑ i ∈ I j, t i)
```

### `ImbalancedChen.storedMeshCapCheck_actual_square_gates`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
theorem storedMeshCapCheck_actual_square_gates {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ)
    (hc : storedMeshCapCheck a b m J I old nu cap = true)
    (j : Fin n → Fin (m + 1)) (hj : j ∈ J)
    (t : Fin n → ℝ) (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j)
    (N : ℝ) (hN : 1 < N) (p : Fin n → ℕ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i) :
    (∀ k, ((∏ i ∈ Finset.univ.filter (fun i => i < k), p i : ℕ) : ℝ) *
      (p k : ℝ) ^ 2 < N ^ (cap j : ℝ)) ∧
    (∀ k ∉ I j, ((∏ i ∈ I j, p i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i => i < k ∧ i ∉ I j), p i : ℕ) : ℝ) *
        (p k : ℝ) ^ 2 < N ^ (cap j : ℝ))
```

### `ImbalancedChen.storedMeshCapCheck_of_selectedBoxCapChecks`

**Matched to the actual audit by full name and kind; actual type in Appendix A.**

```lean
theorem storedMeshCapCheck_of_selectedBoxCapChecks {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu : (Fin n → Fin (m + 1)) → ℚ)
    (hc : ∀ j ∈ J, selectedBoxCapCheck (I j) (old j) (nu j)
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) :
    storedMeshCapCheck a b m J I old nu
      (fun j => selectedBoxCap (I j) (old j) (nu j)
        (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j)) = true
```

## Appendix A: actual audit types

These are the literal decoded `type` strings of all fourteen production
records in the bound actual audit log. The first twelve correspond to the
public source declarations in the same order as above; the final two
complete the production census. Every record below has defining module
`ImbalancedChen.StoredHistoricalBoxPermit` and reports transitive axioms
`[propext, Classical.choice, Quot.sound]`.

### A1. `ImbalancedChen.storedBoxCapCheck`

Actual kind: `definition`. Origin: public source declaration.

```lean
{n : ℕ} → Finset (Fin n) → ℚ → ℚ → (Fin n → ℚ) → (Fin n → ℚ) → ℚ → Bool
```

### A2. `ImbalancedChen.storedBoxCapCheck_iff`

Actual kind: `theorem`. Origin: public source declaration.

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ),
  ImbalancedChen.storedBoxCapCheck I old nu lo hi cap = true ↔
    ImbalancedChen.selectedCapLower I old hi < cap ∧ cap < ImbalancedChen.selectedCapUpper I nu lo hi
```

### A3. `ImbalancedChen.storedBoxCapCheck_old_lt`

Actual kind: `theorem`. Origin: public source declaration.

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ),
  ImbalancedChen.storedBoxCapCheck I old nu lo hi cap = true → old < cap
```

### A4. `ImbalancedChen.storedBoxCapCheck_midpoint`

Actual kind: `theorem`. Origin: public source declaration.

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ),
  ImbalancedChen.selectedBoxCapCheck I old nu lo hi = true →
    ImbalancedChen.storedBoxCapCheck I old nu lo hi (ImbalancedChen.selectedBoxCap I old nu lo hi) = true
```

### A5. `ImbalancedChen.storedBoxCapCheck_sound`

Actual kind: `theorem`. Origin: public source declaration.

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ),
  ImbalancedChen.storedBoxCapCheck I old nu lo hi cap = true →
    ∀ (t : Fin n → ℝ),
      (∀ (i : Fin n), ↑(lo i) ≤ t i) →
        (∀ (i : Fin n), t i ≤ ↑(hi i)) →
          ↑old < ↑cap ∧
            ↑cap < ↑nu ∧
              1 / 2 < ↑cap ∧
                (∀ (j : Fin n), ImbalancedChen.prefixSquareExpr t j < ↑cap) ∧
                  (∀ j ∉ I, ImbalancedChen.selectedSquareExpr I t j < ↑cap) ∧
                    ↑cap < ImbalancedChen.VariableEnvelope.v (∑ i ∈ I, t i)
```

### A6. `ImbalancedChen.storedBoxCapCheck_actual_square_gates`

Actual kind: `theorem`. Origin: public source declaration.

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ),
  ImbalancedChen.storedBoxCapCheck I old nu lo hi cap = true →
    ∀ (t : Fin n → ℝ),
      (∀ (i : Fin n), ↑(lo i) ≤ t i) →
        (∀ (i : Fin n), t i ≤ ↑(hi i)) →
          ∀ (N : ℝ),
            1 < N →
              ∀ (p : Fin n → ℕ),
                (∀ (i : Fin n), ↑(p i) ≤ N ^ t i) →
                  (∀ (j : Fin n), ↑(∏ i with i < j, p i) * ↑(p j) ^ 2 < N ^ ↑cap) ∧
                    ∀ j ∉ I, ↑(∏ i ∈ I, p i) * ↑(∏ i with i < j ∧ i ∉ I, p i) * ↑(p j) ^ 2 < N ^ ↑cap
```

### A7. `ImbalancedChen.storedMeshCapCheck`

Actual kind: `definition`. Origin: public source declaration.

```lean
{n : ℕ} →
  ℚ →
    ℚ →
      (m : ℕ) →
        Finset (Fin n → Fin (m + 1)) →
          ((Fin n → Fin (m + 1)) → Finset (Fin n)) →
            ((Fin n → Fin (m + 1)) → ℚ) → ((Fin n → Fin (m + 1)) → ℚ) → ((Fin n → Fin (m + 1)) → ℚ) → Bool
```

### A8. `ImbalancedChen.storedMeshCapCheck_iff`

Actual kind: `theorem`. Origin: public source declaration.

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu cap : (Fin n → Fin (m + 1)) → ℚ),
  ImbalancedChen.storedMeshCapCheck a b m J I old nu cap = true ↔
    ∀ j ∈ J,
      ImbalancedChen.storedBoxCapCheck (I j) (old j) (nu j) (ImbalancedChen.qLogPrimeMeshLo a b m j)
          (ImbalancedChen.qLogPrimeMeshHi a b m j) (cap j) =
        true
```

### A9. `ImbalancedChen.storedMeshCapCheck_old_lt`

Actual kind: `theorem`. Origin: public source declaration.

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu cap : (Fin n → Fin (m + 1)) → ℚ),
  ImbalancedChen.storedMeshCapCheck a b m J I old nu cap = true → ∀ j ∈ J, old j < cap j
```

### A10. `ImbalancedChen.storedMeshCapCheck_sound`

Actual kind: `theorem`. Origin: public source declaration.

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu cap : (Fin n → Fin (m + 1)) → ℚ),
  ImbalancedChen.storedMeshCapCheck a b m J I old nu cap = true →
    ∀ j ∈ J,
      ∀ t ∈ ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j,
        ↑(old j) < ↑(cap j) ∧
          ↑(cap j) < ↑(nu j) ∧
            1 / 2 < ↑(cap j) ∧
              (∀ (i : Fin n), ImbalancedChen.prefixSquareExpr t i < ↑(cap j)) ∧
                (∀ i ∉ I j, ImbalancedChen.selectedSquareExpr (I j) t i < ↑(cap j)) ∧
                  ↑(cap j) < ImbalancedChen.VariableEnvelope.v (∑ i ∈ I j, t i)
```

### A11. `ImbalancedChen.storedMeshCapCheck_actual_square_gates`

Actual kind: `theorem`. Origin: public source declaration.

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu cap : (Fin n → Fin (m + 1)) → ℚ),
  ImbalancedChen.storedMeshCapCheck a b m J I old nu cap = true →
    ∀ j ∈ J,
      ∀ t ∈ ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j,
        ∀ (N : ℝ),
          1 < N →
            ∀ (p : Fin n → ℕ),
              (∀ (i : Fin n), ↑(p i) ≤ N ^ t i) →
                (∀ (k : Fin n), ↑(∏ i with i < k, p i) * ↑(p k) ^ 2 < N ^ ↑(cap j)) ∧
                  ∀ k ∉ I j, ↑(∏ i ∈ I j, p i) * ↑(∏ i with i < k ∧ i ∉ I j, p i) * ↑(p k) ^ 2 < N ^ ↑(cap j)
```

### A12. `ImbalancedChen.storedMeshCapCheck_of_selectedBoxCapChecks`

Actual kind: `theorem`. Origin: public source declaration.

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu : (Fin n → Fin (m + 1)) → ℚ),
  (∀ j ∈ J,
      ImbalancedChen.selectedBoxCapCheck (I j) (old j) (nu j) (ImbalancedChen.qLogPrimeMeshLo a b m j)
          (ImbalancedChen.qLogPrimeMeshHi a b m j) =
        true) →
    (ImbalancedChen.storedMeshCapCheck a b m J I old nu fun j =>
        ImbalancedChen.selectedBoxCap (I j) (old j) (nu j) (ImbalancedChen.qLogPrimeMeshLo a b m j)
          (ImbalancedChen.qLogPrimeMeshHi a b m j)) =
      true
```

### A13. `ImbalancedChen.storedBoxCapCheck.eq_1`

Actual kind: `theorem`. Origin: generated equation theorem.

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ),
  ImbalancedChen.storedBoxCapCheck I old nu lo hi cap =
    decide (ImbalancedChen.selectedCapLower I old hi < cap ∧ cap < ImbalancedChen.selectedCapUpper I nu lo hi)
```

### A14. `ImbalancedChen.storedMeshCapCheck.eq_1`

Actual kind: `theorem`. Origin: generated equation theorem.

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu cap : (Fin n → Fin (m + 1)) → ℚ),
  ImbalancedChen.storedMeshCapCheck a b m J I old nu cap =
    decide
      (∀ a_1 ∈ J,
        ImbalancedChen.storedBoxCapCheck (I a_1) (old a_1) (nu a_1) (ImbalancedChen.qLogPrimeMeshLo a b m a_1)
            (ImbalancedChen.qLogPrimeMeshHi a b m a_1) (cap a_1) =
          true)
```
