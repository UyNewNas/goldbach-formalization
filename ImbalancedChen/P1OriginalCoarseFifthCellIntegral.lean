import ImbalancedChen.P1OriginalCoarseFifthContinuationCells
import ImbalancedChen.P1OriginalHistoricalFifthOwnCubeAffineGates
import ImbalancedChen.P1HistoricalFifthJointIntegralSign

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

Original fifth selected-cell integrals on [a,19/96)^5, a > 0.
The original T3 candidate parent keeps firstStop, the initial first cube,
the current third first/third cubes, and the actual rough activation.
The new and inherited fifth own-cube indicators remain separate in the
definition.  The real lower-factor zero extension proves integrability.
No a->0, small-prime remainder, or original global mean is asserted.
-/

namespace ImbalancedChen.P1OriginalFifthIntegral

noncomputable section
open MeasureTheory Set Filter Topology
open scoped Classical BigOperators
open MathlibNt.SieveTheory
open P1OriginalCoarseFifthContinuation

def truncatedCell (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (j : Label5 m) :
    Set (Fin 5 → ℝ) :=
  logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ)) ∩
    (logPrimeMeshCell 0 (19 / 96) m j ∩
      HistoricalThirdCoarse.P1OriginalCoarseFifth.jointRegion (e : ℝ) chi m omega j)

theorem truncatedCell_measurable (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (j : Label5 m) : MeasurableSet (truncatedCell e chi m omega a j) :=
  (measurableSet_logPrimeBox _ _).inter
    ((measurableSet_logPrimeMeshCell _ _ _ _).inter
      (HistoricalThirdCoarse.P1OriginalCoarseFifth.measurableSet_jointRegion _ _ _ _ _))

theorem truncatedCell_subset_closedBox (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (j : Label5 m) :
    truncatedCell e chi m omega a j ⊆ univ.pi (fun _ : Fin 5 => Icc a (19 / 96 : ℝ)) := by
  intro t ht i _
  exact ⟨(mem_logPrimeBox.mp ht.1 i).1, (mem_logPrimeBox.mp ht.1 i).2.le⟩

/-- Selection proves the original inclusive activation throughout this owner. -/
theorem selectedCell_active (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    {t : Fin 5 → ℝ} (ht : t ∈ truncatedCell e chi m omega a j) : omega ≤ t 2 := by
  exact P1OriginalHistoricalFifthOwnCubeAffineGates.selected_cell_rough
    e chi m omega J5 j hj ht.2.1

theorem selectedCell_in_original_selectedRegion (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega a : ℝ) (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    {t : Fin 5 → ℝ} (ht : t ∈ truncatedCell e chi m omega a j) :
    t ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.selectedRegion (e : ℝ) m omega j := by
  exact (P1OriginalHistoricalFifthOwnCubeAffineGates.jointRegion_on_selected_cell
    e chi m omega J5 j hj ht.2.1).mp ht.2.2

/-- The literal canonical lower profile, licensed only inside its own cube. -/
def literalOwnCubeProfile (lambda : ℝ) (t : Fin 5 → ℝ) : ℝ :=
  if primeTupleOwnCubeForm t < lambda then
    (2 * Real.exp (-Real.eulerMascheroniConstant) / t (Fin.last 4)) *
      suzukiContinuousLowerFactor ((lambda - ∑ i, t i) / t (Fin.last 4))
  else 0

theorem literalOwnCubeProfile_eq_gated (lambda : ℝ) (t : Fin 5 → ℝ)
    (hp : 0 < t (Fin.last 4)) :
    literalOwnCubeProfile lambda t = primeOwnCubeGatedProfile lambda t := by
  by_cases hg : primeTupleOwnCubeForm t < lambda
  · simp only [literalOwnCubeProfile, primeOwnCubeGatedProfile, if_pos hg]
    exact (primeTupleMinusProfile_of_ownCube hp hg.le).symm
  · simp only [literalOwnCubeProfile, primeOwnCubeGatedProfile, if_neg hg]

theorem continuousOn_gatedProfile {a b : ℝ} (ha : 0 < a) (lambda : ℝ) :
    ContinuousOn (primeOwnCubeGatedProfile (k := 4) lambda)
      (univ.pi (fun _ : Fin 5 => Icc a b)) := by
  apply (continuousOn_primeTupleMinusProfile ha lambda).congr
  intro t ht
  exact p1PrimeOwnCubeGatedProfile_eq_profile lambda t
    (ha.trans_le (ht _ (mem_univ _)).1)

theorem minusProfile_at_ownCube_wall (lambda : ℝ) (t : Fin 5 → ℝ)
    (hp : 0 < t (Fin.last 4)) (hwall : primeTupleOwnCubeForm t = lambda) :
    primeTupleMinusProfile lambda t = 0 := by
  rw [← p1PrimeOwnCubeGatedProfile_eq_profile lambda t hp]
  simp only [primeOwnCubeGatedProfile, hwall, lt_self_iff_false, if_false]

def reciprocalWeight (t : Fin 5 → ℝ) : ℝ := ∏ i, 1 / t i

theorem continuousOn_reciprocalWeight {a b : ℝ} (ha : 0 < a) :
    ContinuousOn reciprocalWeight (univ.pi (fun _ : Fin 5 => Icc a b)) := by
  unfold reciprocalWeight
  apply continuousOn_finsetProd Finset.univ
  intro i _
  exact continuousOn_const.div (continuous_apply i).continuousOn
    (fun t ht => (ha.trans_le (ht i (mem_univ _)).1).ne')

/-- Both original level-dependent strict own-cube indicators stay visible. -/
def cellKernel (old new : ℝ) (t : Fin 5 → ℝ) : ℝ :=
  (primeOwnCubeGatedProfile new t - primeOwnCubeGatedProfile old t) * reciprocalWeight t

theorem cellKernel_eq_two_indicators (old new : ℝ) (t : Fin 5 → ℝ) :
    cellKernel old new t =
      ((if primeTupleOwnCubeForm t < new then primeTupleMinusProfile new t else 0) -
        (if primeTupleOwnCubeForm t < old then primeTupleMinusProfile old t else 0)) *
        ∏ i, 1 / t i := by rfl

theorem cellKernel_eq_literal (old new : ℝ) (t : Fin 5 → ℝ)
    (hp : 0 < t (Fin.last 4)) :
    cellKernel old new t =
      (literalOwnCubeProfile new t - literalOwnCubeProfile old t) * ∏ i, 1 / t i := by
  rw [literalOwnCubeProfile_eq_gated new t hp, literalOwnCubeProfile_eq_gated old t hp]
  rfl

theorem continuousOn_cellKernel {a b : ℝ} (ha : 0 < a) (old new : ℝ) :
    ContinuousOn (cellKernel old new) (univ.pi (fun _ : Fin 5 => Icc a b)) :=
  ((continuousOn_gatedProfile ha new).sub (continuousOn_gatedProfile ha old)).mul
    (continuousOn_reciprocalWeight ha)

theorem integrableOn_cellKernel (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (j : Label5 m) (old new : ℝ) :
    IntegrableOn (cellKernel old new) (truncatedCell e chi m omega a j) :=
  ((continuousOn_cellKernel ha old new).integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
      (truncatedCell_subset_closedBox e chi m omega a j)

theorem integrableOn_gatedWeightedProfile (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (j : Label5 m) (lambda : ℝ) :
    IntegrableOn (fun t => primeOwnCubeGatedProfile lambda t * reciprocalWeight t)
      (truncatedCell e chi m omega a j) :=
  (((continuousOn_gatedProfile ha lambda).mul
    (continuousOn_reciprocalWeight ha)).integrableOn_compact
      (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
        (truncatedCell_subset_closedBox e chi m omega a j)

def cellIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (cap5 : Label5 m → ℚ) (j : Label5 m) : ℝ :=
  ∫ t in truncatedCell e chi m omega a j,
    cellKernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ) t

def selectedIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5, cellIntegral e chi m omega a J4 cap4 cap5 j

theorem cellIntegral_eq_literal (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (cap5 : Label5 m → ℚ) (j : Label5 m) :
    cellIntegral e chi m omega a J4 cap4 cap5 j =
      ∫ t in truncatedCell e chi m omega a j,
        (literalOwnCubeProfile (cap5 j : ℝ) t -
          literalOwnCubeProfile (old5 e chi m omega J4 cap4 j : ℝ) t) * ∏ i, 1 / t i := by
  apply setIntegral_congr_fun (truncatedCell_measurable e chi m omega a j)
  intro t ht
  exact cellKernel_eq_literal _ _ t (ha.trans_le (mem_logPrimeBox.mp ht.1 _).1)

theorem cellIntegral_eq_gated_difference (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (cap5 : Label5 m → ℚ) (j : Label5 m) :
    cellIntegral e chi m omega a J4 cap4 cap5 j =
      (∫ t in truncatedCell e chi m omega a j,
        primeOwnCubeGatedProfile (cap5 j : ℝ) t * reciprocalWeight t) -
      ∫ t in truncatedCell e chi m omega a j,
        primeOwnCubeGatedProfile (old5 e chi m omega J4 cap4 j : ℝ) t * reciprocalWeight t := by
  unfold cellIntegral cellKernel
  simp_rw [sub_mul]
  exact integral_sub (integrableOn_gatedWeightedProfile e chi m omega ha j _)
    (integrableOn_gatedWeightedProfile e chi m omega ha j _)

/-- Purely continuous zero-extension identity; arithmetic gates are not removed. -/
theorem cellIntegral_eq_continuousProfile (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (cap5 : Label5 m → ℚ) (j : Label5 m) :
    cellIntegral e chi m omega a J4 cap4 cap5 j =
      ∫ t in truncatedCell e chi m omega a j,
        (primeTupleMinusProfile (cap5 j : ℝ) t -
          primeTupleMinusProfile (old5 e chi m omega J4 cap4 j : ℝ) t) * ∏ i, 1 / t i := by
  apply setIntegral_congr_fun (truncatedCell_measurable e chi m omega a j)
  intro t ht
  have hp : 0 < t (Fin.last 4) := ha.trans_le (mem_logPrimeBox.mp ht.1 _).1
  unfold cellKernel
  rw [p1PrimeOwnCubeGatedProfile_eq_profile _ t hp,
    p1PrimeOwnCubeGatedProfile_eq_profile _ t hp]
  rfl

theorem selectedIntegral_eq_literal (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) :
    selectedIntegral e chi m omega a J4 cap4 J5 cap5 =
      ∑ j ∈ selectedFifthCells e chi m omega J5,
        ∫ t in truncatedCell e chi m omega a j,
          (literalOwnCubeProfile (cap5 j : ℝ) t -
            literalOwnCubeProfile (old5 e chi m omega J4 cap4 j : ℝ) t) * ∏ i, 1 / t i := by
  apply Finset.sum_congr rfl
  intro j _
  exact cellIntegral_eq_literal e chi m omega ha J4 cap4 cap5 j

theorem selected_lookup_levels (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) (hN : 1 < N) (hlen : pre.length = 5)
    (hpos : ∀ p ∈ pre, 0 < p) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ truncatedCell e chi m omega a j) :
    P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 N (rosserAncestor 4 pre) =
        N ^ (old5 e chi m omega J4 cap4 j : ℝ) ∧
      level5 e chi m omega J4 cap4 J5 cap5 N pre = N ^ (cap5 j : ℝ) := by
  constructor
  · change N ^ (P1OriginalCoarseContinuation.effectiveExponent4Q
      e chi m omega J4 cap4 N (rosserAncestor 4 pre) : ℝ) = _
    rw [inherited_fourth_on_selected_fifth_cell e chi m omega J4 cap4 J5 N pre hN hlen hpos
      j hj ht.2.1]
  · exact level5_on_selected_cell e chi m omega J4 cap4 J5 cap5 N pre hlen j hj ht.2.1

theorem selected_lookup_profile (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) (hN : 1 < N) (hlen : pre.length = 5)
    (hpos : ∀ p ∈ pre, 0 < p) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ truncatedCell e chi m omega a j) :
    cellKernel
      (P1OriginalCoarseContinuation.effectiveExponent4 e chi m omega J4 cap4 N
        (rosserAncestor 4 pre))
      (effectiveExponent5 e chi m omega J4 cap4 J5 cap5 N pre)
      (primeHistoryLogCoordinates N 5 pre) =
    cellKernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ)
      (primeHistoryLogCoordinates N 5 pre) := by
  unfold P1OriginalCoarseContinuation.effectiveExponent4 effectiveExponent5
  rw [inherited_fourth_on_selected_fifth_cell e chi m omega J4 cap4 J5 N pre hN hlen hpos
      j hj ht.2.1,
    effectiveExponent5Q_on_selected_cell e chi m omega J4 cap4 J5 cap5 N pre hlen j hj ht.2.1]

end
end ImbalancedChen.P1OriginalFifthIntegral
