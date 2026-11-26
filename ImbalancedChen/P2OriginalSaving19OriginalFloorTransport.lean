import ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix
import ImbalancedChen.P2OriginalSaving19RowNumericsPure
import ImbalancedChen.P2OriginalLogMomentQ96ArithmeticBridge

/-!
SOURCE CANDIDATE / NOT COMPILED. Data-independent transport for the original
Saving19 floor formula. No concrete row or row family is certified here.

The entry theorem derives the original rationalMoment from exact coordinate
encodings and transports the five already proved finite prefix clauses and
both Q80 bounds. Its premises do not include an original floor, an integral
bound, archive success, or an all-row conclusion. Saved new Q96 remains the
maximum of the old and the uncapped new operator. Existing suppliers and all
accepted row owners are imported without modification.
-/
namespace ImbalancedChen.P2OriginalSaving19OriginalFloorTransport

set_option maxRecDepth 1000000
set_option Elab.async false

open scoped BigOperators
open P2OriginalSaving19Archive
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

def prefixMoments (g : Fin 9 → Nat) (z : Fin 10 → Fin 9 → Nat)
    (d : Fin 10 → Nat) (j : Fin 10) (k : Nat) : ℚ :=
  P2OriginalSaving19PrefixMoments.normalizedMoment g (z j) (d j) k

noncomputable def originalMoments (vertices : Fin 9 → QPoint)
    (row : GeometryRow) (j : Fin 10) (k : Nat) : ℚ :=
  P2OriginalSaving19HigherMoments.rationalMoment
    (fun i => gapQ (vertices i))
    (fun i => 1 - factorsQ (vertices i) j / topsOf row j) k

/-- Exactly the five finite clauses already exposed by each prefix owner. -/
def PrefixFloorChecksFor (row : GeometryRow) (momentRow : MomentRecord)
    (moments : Fin 10 → Nat → ℚ) : Prop :=
  (∀ j : Fin 10, moments j 1 = 1 - meansOf row j / topsOf row j) ∧
  (∀ j : Fin 10, momentRow.factorFloorsQ80[j.val]! = factorFloorQ80 (moments j)) ∧
  momentRow.oldFloorQ96 = row.jensenFloorQ96 ∧
  momentRow.oldFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) ∧
  momentRow.newFloorQ96 =
    max (oldFloorQ96 (massOf row) (meansOf row))
      (newFloorQ96 (massOf row) (meansOf row) moments)

/-- The same five clauses in the unchanged original checker namespace. -/
def OriginalFloorChecksFor (row : GeometryRow) (momentRow : MomentRecord)
    (moments : Fin 10 → Nat → ℚ) : Prop :=
  (∀ j : Fin 10, moments j 1 = 1 - meansOf row j / topsOf row j) ∧
  (∀ j : Fin 10, momentRow.factorFloorsQ80[j.val]! =
    P2OriginalLogMomentQ96CheckerSourceOnly.factorFloorQ80 (moments j)) ∧
  momentRow.oldFloorQ96 = row.jensenFloorQ96 ∧
  momentRow.oldFloorQ96 =
    P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 (massOf row) (meansOf row) ∧
  momentRow.newFloorQ96 =
    max (P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 (massOf row) (meansOf row))
      (P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96
        (massOf row) (meansOf row) moments)

def PrefixQ80BoundsFor (momentRow : MomentRecord)
    (moments : Fin 10 → Nat → ℚ) : Prop :=
  ∀ j : Fin 10,
    ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
        gapEvaluator (moments j) * (2 : ℚ)^80 ∧
      gapEvaluator (moments j) * (2 : ℚ)^80 <
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1

def OriginalQ80BoundsFor (momentRow : MomentRecord)
    (moments : Fin 10 → Nat → ℚ) : Prop :=
  ∀ j : Fin 10,
    ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
        P2OriginalLogMomentQ96CheckerSourceOnly.gapEvaluator (moments j) * (2 : ℚ)^80 ∧
      P2OriginalLogMomentQ96CheckerSourceOnly.gapEvaluator (moments j) * (2 : ℚ)^80 <
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1

/-- The original degree-six evaluator reads only degrees one through six. -/
theorem gapEvaluator_congr_through_six (a b : Nat → ℚ)
    (h : ∀ k, k ≤ 6 → a k = b k) : gapEvaluator a = gapEvaluator b := by
  unfold gapEvaluator
  apply Finset.sum_congr rfl
  intro k hk
  rw [h (k + 2) (by have hmem := Finset.mem_range.mp hk; omega),
    h 1 (by decide)]

theorem totalLowerQ80_congr_through_six (a b : Fin 10 → Nat → ℚ)
    (h : ∀ j k, k ≤ 6 → a j k = b j k) :
    totalLowerQ80 a = totalLowerQ80 b := by
  unfold totalLowerQ80 factorLowerQ80 roundDownQ
  apply Finset.sum_congr rfl
  intro j hj
  rw [gapEvaluator_congr_through_six (a j) (b j) (h j)]

/-- Congruence of the uncapped new operator; no saved maximum is substituted. -/
theorem newFloorQ96_congr_through_six (mass : ℚ) (means : Fin 10 → ℚ)
    (a b : Fin 10 → Nat → ℚ) (h : ∀ j k, k ≤ 6 → a j k = b j k) :
    newFloorQ96 mass means a = newFloorQ96 mass means b := by
  unfold newFloorQ96 newEvaluator
  rw [totalLowerQ80_congr_through_six a b h]

/-- Only coordinate encodings and nonzero common scales are premises. -/
theorem prefixMoments_eq_original (vertices : Fin 9 → QPoint) (row : GeometryRow)
    (g : Fin 9 → Nat) (z : Fin 10 → Fin 9 → Nat) (d : Fin 10 → Nat) (s : Nat)
    (hd : ∀ j, d j ≠ 0) (hs : s ≠ 0)
    (hg : ∀ i, gapQ (vertices i) = (g i : ℚ) / (s : ℚ))
    (hz : ∀ j i, 1 - factorsQ (vertices i) j / topsOf row j =
      (z j i : ℚ) / (d j : ℚ))
    (j : Fin 10) (k : Nat) (hk : k ≤ 6) :
    prefixMoments g z d j k = originalMoments vertices row j k := by
  exact P2OriginalSaving19HigherMomentsPrefix.normalizedMoment_eq_encoded
    g (z j) (d j) s k (hd j) hs hk
    (fun i => gapQ (vertices i))
    (fun i => 1 - factorsQ (vertices i) j / topsOf row j) hg (hz j)

/-- General finite congruence. The entry theorem below derives h from the
original vertex coordinates, rather than assuming a rational-moment result. -/
theorem originalFloorChecks_of_prefix (row : GeometryRow) (momentRow : MomentRecord)
    (encoded actual : Fin 10 → Nat → ℚ)
    (h : ∀ j k, k ≤ 6 → encoded j k = actual j k)
    (hprefix : PrefixFloorChecksFor row momentRow encoded) :
    OriginalFloorChecksFor row momentRow actual := by
  rcases hprefix with ⟨hfirst, hfactor, hgeometry, hold, hnew⟩
  refine ⟨?_, ?_, hgeometry, ?_, ?_⟩
  · intro j
    rw [← h j 1 (by decide)]
    exact hfirst j
  · intro j
    rw [← P2OriginalLogMomentQ96ArithmeticBridge.factorFloorQ80_eq]
    unfold factorFloorQ80
    rw [← gapEvaluator_congr_through_six (encoded j) (actual j) (h j)]
    exact hfactor j
  · rw [← P2OriginalLogMomentQ96ArithmeticBridge.oldFloorQ96_eq]
    exact hold
  · rw [← P2OriginalLogMomentQ96ArithmeticBridge.oldFloorQ96_eq,
      ← P2OriginalLogMomentQ96ArithmeticBridge.newFloorQ96_eq,
      ← newFloorQ96_congr_through_six (massOf row) (meansOf row) encoded actual h]
    exact hnew

theorem originalQ80Bounds_of_prefix (momentRow : MomentRecord)
    (encoded actual : Fin 10 → Nat → ℚ)
    (h : ∀ j k, k ≤ 6 → encoded j k = actual j k)
    (hbounds : PrefixQ80BoundsFor momentRow encoded) :
    OriginalQ80BoundsFor momentRow actual := by
  intro j
  rw [← P2OriginalLogMomentQ96ArithmeticBridge.gapEvaluator_eq,
    ← gapEvaluator_congr_through_six (encoded j) (actual j) (h j)]
  exact hbounds j

/-- Entry point for one actual finite owner. Every premise must be discharged
by that owner's proved encoding, five prefix clauses, and twenty Q80 bounds. -/
theorem original_floor_and_bounds_of_encoding
    (vertices : Fin 9 → QPoint) (row : GeometryRow) (momentRow : MomentRecord)
    (g : Fin 9 → Nat) (z : Fin 10 → Fin 9 → Nat) (d : Fin 10 → Nat) (s : Nat)
    (hd : ∀ j, d j ≠ 0) (hs : s ≠ 0)
    (hg : ∀ i, gapQ (vertices i) = (g i : ℚ) / (s : ℚ))
    (hz : ∀ j i, 1 - factorsQ (vertices i) j / topsOf row j =
      (z j i : ℚ) / (d j : ℚ))
    (hprefix : PrefixFloorChecksFor row momentRow (prefixMoments g z d))
    (hbounds : PrefixQ80BoundsFor momentRow (prefixMoments g z d)) :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) := by
  have h : ∀ j k, k ≤ 6 →
      prefixMoments g z d j k = originalMoments vertices row j k :=
    prefixMoments_eq_original vertices row g z d s hd hs hg hz
  exact ⟨originalFloorChecks_of_prefix row momentRow _ _ h hprefix,
    originalQ80Bounds_of_prefix momentRow _ _ h hbounds⟩

/-- Raw lookups may replace typed selectors only through proved equalities.
The nine vertices retain their original order and all eight coordinates. -/
theorem original_floor_and_bounds_of_bindings
    (rawVertices vertices : Fin 9 → QPoint)
    (rawRow row : GeometryRow) (rawMomentRow momentRow : MomentRecord)
    (hvertices : ∀ i j, rawVertices i j = vertices i j)
    (hrow : rawRow = row) (hmoment : rawMomentRow = momentRow)
    (h : OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row)) :
    OriginalFloorChecksFor rawRow rawMomentRow (originalMoments rawVertices rawRow) ∧
      OriginalQ80BoundsFor rawMomentRow (originalMoments rawVertices rawRow) := by
  have hv : rawVertices = vertices := by
    funext i j
    exact hvertices i j
  rw [hv, hrow, hmoment]
  exact h

/-- Definitional agreement with the original five-clause row formula, with
its actual selectors left explicit. This imports no unverified all-row owner. -/
theorem originalFloorChecksFor_iff_originalForm {R : Type*}
    (rawVertex : R → Fin 9 → QPoint) (rawGeometryRow : R → GeometryRow)
    (rawMomentRow : R → MomentRecord) (r : R) :
    OriginalFloorChecksFor (rawGeometryRow r) (rawMomentRow r)
      (originalMoments (rawVertex r) (rawGeometryRow r)) ↔
      let massQ : R → ℚ := fun t =>
        (rawGeometryRow t).physicalVolume * (rawGeometryRow t).meanGap
      let meansQ : R → Fin 10 → ℚ := fun t j =>
        (rawGeometryRow t).gapWeightedMeans[j.val]!
      let topsQ : R → Fin 10 → ℚ := fun t j =>
        (rawGeometryRow t).factorMaxima[j.val]!
      let momentsQ : R → Fin 10 → Nat → ℚ := fun t j k =>
        P2OriginalSaving19HigherMoments.rationalMoment
          (fun i => gapQ (rawVertex t i))
          (fun i => 1 - factorsQ (rawVertex t i) j / topsQ t j) k
      (∀ j : Fin 10, momentsQ r j 1 = 1 - meansQ r j / topsQ r j) ∧
      (∀ j : Fin 10, (rawMomentRow r).factorFloorsQ80[j.val]! =
        P2OriginalLogMomentQ96CheckerSourceOnly.factorFloorQ80 (momentsQ r j)) ∧
      (rawMomentRow r).oldFloorQ96 = (rawGeometryRow r).jensenFloorQ96 ∧
      (rawMomentRow r).oldFloorQ96 =
        P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 (massQ r) (meansQ r) ∧
      (rawMomentRow r).newFloorQ96 =
        max (P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 (massQ r) (meansQ r))
          (P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96
            (massQ r) (meansQ r) (momentsQ r)) :=
  Iff.rfl

#print axioms gapEvaluator_congr_through_six
#print axioms totalLowerQ80_congr_through_six
#print axioms newFloorQ96_congr_through_six
#print axioms prefixMoments_eq_original
#print axioms originalFloorChecks_of_prefix
#print axioms originalQ80Bounds_of_prefix
#print axioms original_floor_and_bounds_of_encoding
#print axioms original_floor_and_bounds_of_bindings
#print axioms originalFloorChecksFor_iff_originalForm

end ImbalancedChen.P2OriginalSaving19OriginalFloorTransport
