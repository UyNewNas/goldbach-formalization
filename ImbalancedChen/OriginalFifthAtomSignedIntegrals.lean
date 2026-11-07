import ImbalancedChen.OriginalFifthOwnCubeSignRefinement

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

The ORIGINAL primitive sign and terminal own-cube sign fibers form a finite
Borel partition with equality states included. Every signed point charge
occurs exactly once. The original FULL fifth saving is exactly the finite
sum of its constructed fixed-label/fixed-flag atom integrals. The existing
actual full-kernel integrability theorem supplies integrability; no desired
saving, positivity, selected-source identity, or distribution estimate is
an input. Empty fibers contribute zero. All native variable caps remain.
-/

namespace ImbalancedChen.OriginalFifthAtomSignedIntegrals20261026b

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open OriginalFifthLiteralAffineSignBank20261026b
open OriginalFifthOwnCubeSignRefinement20261026b

private theorem measurable_strict_bit {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (f : X → ℝ) (hf : Continuous f) (b : Bool) :
    MeasurableSet {t | decide (f t < 0) = b} := by
  cases b
  · have hs : {t | decide (f t < 0) = false} = {t | 0 ≤ f t} := by ext t; simp
    rw [hs]
    exact (isClosed_le continuous_const hf).measurableSet
  · have hs : {t | decide (f t < 0) = true} = {t | f t < 0} := by ext t; simp
    rw [hs]
    exact (isOpen_lt hf continuous_const).measurableSet

private theorem measurable_weak_bit {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (f : X → ℝ) (hf : Continuous f) (b : Bool) :
    MeasurableSet {t | decide (f t ≤ 0) = b} := by
  cases b
  · have hs : {t | decide (f t ≤ 0) = false} = {t | 0 < f t} := by ext t; simp
    rw [hs]
    exact (isOpen_lt continuous_const hf).measurableSet
  · have hs : {t | decide (f t ≤ 0) = true} = {t | f t ≤ 0} := by ext t; simp
    rw [hs]
    exact (isClosed_le hf continuous_const).measurableSet

private theorem measurable_twoBit_fiber {X I : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [Fintype I] (f : I → X → ℝ)
    (hf : ∀ k, Continuous (f k)) (w : I → Bool × Bool) :
    MeasurableSet {t | (fun k => (decide (f k t < 0), decide (f k t ≤ 0))) = w} := by
  have hs : {t | (fun k => (decide (f k t < 0), decide (f k t ≤ 0))) = w} =
      ⋂ k : I, ({t | decide (f k t < 0) = (w k).1} ∩ {t | decide (f k t ≤ 0) = (w k).2}) := by
    ext t
    constructor
    · intro h
      apply mem_iInter.mpr
      intro k
      have hk := congrFun h k
      exact ⟨congrArg Prod.fst hk, congrArg Prod.snd hk⟩
    · intro h
      funext k
      have hk := mem_iInter.mp h k
      exact Prod.ext hk.1 hk.2
  rw [hs]
  exact MeasurableSet.iInter (fun k =>
    (measurable_strict_bit (f k) (hf k) (w k).1).inter
      (measurable_weak_bit (f k) (hf k) (w k).2))

theorem measurableSet_nativeSignAtom
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (w : SignWord R4 R5) :
    MeasurableSet (signAtom R4 R5 e m j w) := by
  exact measurable_twoBit_fiber (guardValue R4 R5 e m j)
    (continuous_guardValue R4 R5 e m j) w

theorem measurableSet_cubeAtom
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (v : CubeWord R4 R5) :
    MeasurableSet (cubeAtom R4 R5 e m j v) := by
  exact measurable_twoBit_fiber (cubeWall R4 R5 e m j)
    (continuous_cubeWall R4 R5 e m j) v

theorem measurableSet_refinedAtom
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (w : SignWord R4 R5) (v : CubeWord R4 R5) :
    MeasurableSet (refinedAtom R4 R5 e m j w v) :=
  (measurableSet_nativeSignAtom R4 R5 e m j w).inter (measurableSet_cubeAtom R4 R5 e m j v)

abbrev WordPair (R4 : List FourthWireRow) (R5 : List FifthWireRow) := SignWord R4 R5 × CubeWord R4 R5

def actualWordPair (R4 : List FourthWireRow) (R5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) (t : Fin 5 → ℝ) : WordPair R4 R5 :=
  (primitiveWord R4 R5 e m j t, actualCubeWord R4 R5 e m j t)

theorem refinedAtom_actual
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (t : Fin 5 → ℝ) :
    t ∈ refinedAtom R4 R5 e m j (actualWordPair R4 R5 e m j t).1
      (actualWordPair R4 R5 e m j t).2 := ⟨rfl, rfl⟩

theorem refinedAtom_unique
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (z : WordPair R4 R5) {t : Fin 5 → ℝ}
    (ht : t ∈ refinedAtom R4 R5 e m j z.1 z.2) : actualWordPair R4 R5 e m j t = z :=
  Prod.ext ht.1 ht.2

/-- Pointwise conservation includes every equality fiber and every sign. -/
theorem indicator_eq_sum_refinedAtoms
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (R : Set (Fin 5 → ℝ)) (f : (Fin 5 → ℝ) → ℝ) (t : Fin 5 → ℝ) :
    R.indicator f t = ∑ z : WordPair R4 R5, (R ∩ refinedAtom R4 R5 e m j z.1 z.2).indicator f t := by
  symm
  rw [Finset.sum_eq_single (actualWordPair R4 R5 e m j t)]
  · by_cases ht : t ∈ R
    · rw [indicator_of_mem ht, indicator_of_mem ⟨ht, refinedAtom_actual R4 R5 e m j t⟩]
    · rw [indicator_of_notMem ht, indicator_of_notMem
        (show t ∉ R ∩ refinedAtom R4 R5 e m j (actualWordPair R4 R5 e m j t).1
          (actualWordPair R4 R5 e m j t).2 from fun h => ht h.1)]
  · intro z _hz hne
    apply indicator_of_notMem
    intro ht
    exact hne (refinedAtom_unique R4 R5 e m j z ht.2).symm
  · simp

theorem signed_integral_eq_refinedAtoms
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (R : Set (Fin 5 → ℝ)) (hR : MeasurableSet R)
    (f : (Fin 5 → ℝ) → ℝ) (hf : IntegrableOn f R) :
    (∫ t in R, f t) = ∑ z : WordPair R4 R5, ∫ t in R ∩ refinedAtom R4 R5 e m j z.1 z.2, f t := by
  have hs (z : WordPair R4 R5) : MeasurableSet (R ∩ refinedAtom R4 R5 e m j z.1 z.2) :=
    hR.inter (measurableSet_refinedAtom R4 R5 e m j z.1 z.2)
  have hi (z : WordPair R4 R5) :
      Integrable ((R ∩ refinedAtom R4 R5 e m j z.1 z.2).indicator f) :=
    (integrable_indicator_iff (hs z)).mpr (hf.mono_set (fun _ ht => ht.1))
  calc
    (∫ t in R, f t) = ∫ t, R.indicator f t := (integral_indicator hR).symm
    _ = ∫ t, ∑ z : WordPair R4 R5, (R ∩ refinedAtom R4 R5 e m j z.1 z.2).indicator f t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (indicator_eq_sum_refinedAtoms R4 R5 e m j R f)
    _ = ∑ z : WordPair R4 R5, ∫ t, (R ∩ refinedAtom R4 R5 e m j z.1 z.2).indicator f t :=
      integral_finset_sum _ (fun z _ => hi z)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _hz
      exact integral_indicator (hs z)

/-- Empty sign fibers carry zero; occupied fibers use their CONSTRUCTED
native labels and their two separate own-cube flags. -/
def atomKernel (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (z : WordPair R4 R5) (t : Fin 5 → ℝ) : ℝ :=
  if h : (refinedAtom R4 R5 e m j z.1 z.2).Nonempty then
    fixedFlagKernel R4 R5 e m j (frozenData R4 R5 e m j L z.1 z.2 h) t
  else 0

/-- Exact FULL original saving; integrability is supplied by the existing
untruncated actual-kernel theorem, with no positive cutoff or target bound. -/
theorem actual_full_saving_eq_constructed_atom_integrals
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (he : 0 ≤ e)
    (chi : ℝ) (m : ℕ) (omega : ℝ) (ho : 0 < omega) (hr : omega < (19 / 96 : ℝ))
    (J : Finset (Fin 5 → Fin (m + 1))) (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (L : ProducerRow → Prop) :
    P1ActualVariableFifthUntruncatedDomination.fullCellIntegral e chi m omega
        (fourthFamily R4) L (fifthFamily R5 m) j =
      ∑ z : WordPair R4 R5, ∫ t in P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j ∩
        refinedAtom R4 R5 e m j z.1 z.2, atomKernel R4 R5 e m j L z t := by
  unfold P1ActualVariableFifthUntruncatedDomination.fullCellIntegral
  rw [signed_integral_eq_refinedAtoms R4 R5 e m j _
    (P1OriginalFifthUntruncatedIntegral.fullCell_measurable e chi m omega j) _
    (P1ActualVariableFifthUntruncatedDomination.integrableOn_actualKernel_fullCell
      e he chi m omega ho hr J j hj (fourthFamily R4) L (fifthFamily R5 m))]
  apply Finset.sum_congr rfl
  intro z _hz
  apply setIntegral_congr_fun ((P1OriginalFifthUntruncatedIntegral.fullCell_measurable
    e chi m omega j).inter (measurableSet_refinedAtom R4 R5 e m j z.1 z.2))
  intro t ht
  have hne : (refinedAtom R4 R5 e m j z.1 z.2).Nonempty := ⟨t, ht.2⟩
  rw [atomKernel, dif_pos hne]
  exact actualKernel_eq_frozenData R4 R5 e chi m omega J j hj L z.1 z.2 hne ht.2 ht.1.2.2.1

end
end ImbalancedChen.OriginalFifthAtomSignedIntegrals20261026b
