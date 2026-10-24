import ImbalancedChen.P1HistoricalFourthFullCellIntegral
import ImbalancedChen.P1OriginalCoarseContinuationCells
import ImbalancedChen.P1OriginalCoarseFourthJointGeometry

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

The fourth selected-cell integral for the ORIGINAL coarse third policy.
The old exponent is the literal Gamma-2e at the selected third ancestor;
the initial first cube, firstStop, current first cube, current third cube,
and inclusive rough activation remain in the original joint region.

The ambient prime integral is truncated to [a,19/96)^4 with a>0.  No claim
is made about the omitted small-prime part, a->0, or a global mean limit.
-/

namespace ImbalancedChen.P1OriginalFourthIntegral

noncomputable section
open MeasureTheory Set Filter Topology
open scoped Classical BigOperators
open P1OriginalCoarseContinuation
open P1FourthNearOneKernel
open P1FourthFullCellIntegral

def oldExponent (e : ℚ) (m : ℕ) (j : FourthCell m) : ℝ :=
  (thirdCellExponent e m j : ℝ)

theorem oldExponent_eq_actual (e : ℚ) (m : ℕ) (j : FourthCell m) :
    oldExponent e m j = HistoricalThirdCoarse.levelExponent (e : ℝ)
      (HistoricalThirdCoarse.box m (HistoricalThirdCoarse.P1OriginalFourth.prefix3 j)) := by
  exact cast_thirdCellExponent e m j

/-- Positive truncation of the real original-policy common joint cell. -/
def truncatedCell (e : ℚ) (m : ℕ) (omega a : ℝ) (j : FourthCell m) :
    Set (Fin 4 → ℝ) :=
  logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ)) ∩
    (HistoricalThirdCoarse.P1OriginalFourth.jointCell m m
        (HistoricalThirdCoarse.P1OriginalFourth.prefix3 j) j ∩
      HistoricalThirdCoarse.P1OriginalFourth.jointRegion (e : ℝ) omega m
        (HistoricalThirdCoarse.P1OriginalFourth.prefix3 j))

theorem truncatedCell_measurable (e : ℚ) (m : ℕ) (omega a : ℝ) (j : FourthCell m) :
    MeasurableSet (truncatedCell e m omega a j) :=
  (measurableSet_logPrimeBox _ _).inter
    ((HistoricalThirdCoarse.P1OriginalFourth.jointCell_measurable _ _ _ _).inter
      (HistoricalThirdCoarse.P1OriginalFourth.jointRegion_measurable _ _ _ _))

theorem truncatedCell_subset_closedBox (e : ℚ) (m : ℕ) (omega a : ℝ) (j : FourthCell m) :
    truncatedCell e m omega a j ⊆ univ.pi (fun _ : Fin 4 => Icc a (19 / 96 : ℝ)) := by
  intro t ht i _
  exact ⟨(mem_logPrimeBox.mp ht.1 i).1, (mem_logPrimeBox.mp ht.1 i).2.le⟩

theorem residual_gt_one_on_truncated (e : ℚ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (j : FourthCell m) {lambda : ℝ}
    (hlevel : oldExponent e m j ≤ lambda) {t : Fin 4 → ℝ}
    (ht : t ∈ truncatedCell e m omega a j) : 1 < residual lambda t := by
  have hp : 0 < t 3 := ha.trans_le (mem_logPrimeBox.mp ht.1 3).1
  have hlevel' : HistoricalThirdCoarse.levelExponent (e : ℝ)
      (HistoricalThirdCoarse.box m (HistoricalThirdCoarse.P1OriginalFourth.prefix3 j)) ≤
        lambda := by
    rw [← oldExponent_eq_actual]
    exact hlevel
  exact (HistoricalThirdCoarse.P1OriginalFourth.jointRegion_plus_legal
    (e : ℝ) omega m _ t ht.2.2 hp lambda hlevel').2.2

theorem truncatedCell_subset_legal (e : ℚ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (j : FourthCell m) {lambda : ℝ}
    (hlevel : oldExponent e m j ≤ lambda) :
    truncatedCell e m omega a j ⊆ legal a lambda := by
  intro t ht
  have hp : 0 < t (Fin.last 3) := ha.trans_le (mem_logPrimeBox.mp ht.1 _).1
  have hs := residual_gt_one_on_truncated e m omega ha j hlevel ht
  change 1 < (lambda - ∑ i, t i) / t (Fin.last 3) at hs
  have h := (lt_div_iff₀ hp).mp hs
  exact ⟨(mem_logPrimeBox.mp ht.1 _).1, by linarith⟩

/-- Exact restoration of the raw fourth PLUS profile on the original domain. -/
theorem rawProfile_eq_extended_on_truncated (e : ℚ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (j : FourthCell m) {lambda : ℝ}
    (hlevel : oldExponent e m j ≤ lambda) {t : Fin 4 → ℝ}
    (ht : t ∈ truncatedCell e m omega a j) :
    fourthPlusProfileP1 lambda t = extendedProfile lambda t := by
  have hlegal := truncatedCell_subset_legal e m omega ha j hlevel ht
  have heq : density lambda t = fourthPlusProfileP1 lambda t :=
    density_eq_actual lambda t (residual_gt_one_on_truncated e m omega ha j hlevel ht)
  rw [← heq, extendedProfile, maxOneNormalized_eq ha hlegal]
  rfl

theorem abs_rawProfile_le_on_truncated (e : ℚ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (j : FourthCell m) {lambda : ℝ}
    (hlevel : oldExponent e m j ≤ lambda) {t : Fin 4 → ℝ}
    (ht : t ∈ truncatedCell e m omega a j) : |fourthPlusProfileP1 lambda t| ≤ 4 / a := by
  have heq : density lambda t = fourthPlusProfileP1 lambda t :=
    density_eq_actual lambda t (residual_gt_one_on_truncated e m omega ha j hlevel ht)
  rw [← heq]
  exact abs_density_le ha (truncatedCell_subset_legal e m omega ha j hlevel ht)

theorem integrableOn_extendedWeightedProfile (e : ℚ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (j : FourthCell m) (lambda : ℝ) :
    IntegrableOn (extendedWeightedProfile lambda) (truncatedCell e m omega a j) := by
  have hc : ContinuousOn (extendedWeightedProfile lambda)
      (univ.pi (fun _ : Fin 4 => Icc a (19 / 96 : ℝ))) :=
    (continuousOn_extendedProfile ha).mul (continuousOn_reciprocalWeight ha)
  exact (hc.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
    (truncatedCell_subset_closedBox e m omega a j)

theorem integrableOn_rawWeightedProfile (e : ℚ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (j : FourthCell m) {lambda : ℝ}
    (hlevel : oldExponent e m j ≤ lambda) :
    IntegrableOn (fun t => fourthPlusProfileP1 lambda t * ∏ i, 1 / t i)
      (truncatedCell e m omega a j) := by
  apply (integrableOn_extendedWeightedProfile e m omega ha j lambda).congr_fun
    (fun t ht => ?_) (truncatedCell_measurable e m omega a j)
  unfold extendedWeightedProfile reciprocalWeight
  rw [rawProfile_eq_extended_on_truncated e m omega ha j hlevel ht]

def cellIntegral (e : ℚ) (m : ℕ) (omega a : ℝ)
    (cap4 : FourthCell m → ℚ) (j : FourthCell m) : ℝ :=
  ∫ t in truncatedCell e m omega a j,
    (extendedProfile (oldExponent e m j) t - extendedProfile (cap4 j : ℝ) t) *
      reciprocalWeight t

def selectedIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ) : ℝ :=
  ∑ j ∈ selectedFourthCells e chi m omega J4, cellIntegral e m omega a cap4 j

theorem integrableOn_cellIntegrand (e : ℚ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (cap4 : FourthCell m → ℚ) (j : FourthCell m) :
    IntegrableOn (fun t =>
      (extendedProfile (oldExponent e m j) t - extendedProfile (cap4 j : ℝ) t) *
        reciprocalWeight t) (truncatedCell e m omega a j) := by
  simpa only [extendedWeightedProfile, sub_mul] using
    (integrableOn_extendedWeightedProfile e m omega ha j (oldExponent e m j)).sub
      (integrableOn_extendedWeightedProfile e m omega ha j (cap4 j : ℝ))

theorem selected_cap_ge_old (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4) :
    oldExponent e m j ≤ (cap4 j : ℝ) := by
  change (thirdCellExponent e m j : ℝ) ≤ (cap4 j : ℝ)
  exact_mod_cast h34Check_sound e chi m omega J4 cap4 hcheck j hj

theorem cellIntegral_eq_raw (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4) :
    cellIntegral e m omega a cap4 j = ∫ t in truncatedCell e m omega a j,
      (fourthPlusProfileP1 (oldExponent e m j) t - fourthPlusProfileP1 (cap4 j : ℝ) t) *
        ∏ i, 1 / t i := by
  have hlevel := selected_cap_ge_old e chi m omega J4 cap4 hcheck j hj
  apply setIntegral_congr_fun (truncatedCell_measurable e m omega a j)
  intro t ht
  rw [rawProfile_eq_extended_on_truncated e m omega ha j le_rfl ht,
    rawProfile_eq_extended_on_truncated e m omega ha j hlevel ht]
  rfl

theorem cellIntegral_eq_raw_difference (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4) :
    cellIntegral e m omega a cap4 j =
      (∫ t in truncatedCell e m omega a j,
        fourthPlusProfileP1 (oldExponent e m j) t * ∏ i, 1 / t i) -
      ∫ t in truncatedCell e m omega a j,
        fourthPlusProfileP1 (cap4 j : ℝ) t * ∏ i, 1 / t i := by
  rw [cellIntegral_eq_raw e chi m omega ha J4 cap4 hcheck j hj]
  simp_rw [sub_mul]
  exact integral_sub (integrableOn_rawWeightedProfile e m omega ha j le_rfl)
    (integrableOn_rawWeightedProfile e m omega ha j
      (selected_cap_ge_old e chi m omega J4 cap4 hcheck j hj))

theorem selectedIntegral_eq_raw (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    selectedIntegral e chi m omega a J4 cap4 =
      ∑ j ∈ selectedFourthCells e chi m omega J4,
        ∫ t in truncatedCell e m omega a j,
          (fourthPlusProfileP1 (oldExponent e m j) t -
            fourthPlusProfileP1 (cap4 j : ℝ) t) * ∏ i, 1 / t i := by
  apply Finset.sum_congr rfl
  intro j hj
  exact cellIntegral_eq_raw e chi m omega ha J4 cap4 hcheck j hj

/-- The old exponent is the original raw Q3, and the new one is the actual lookup. -/
theorem selected_original_levels (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (ht : actualPrimeTupleLog N p ∈ truncatedCell e m omega a j) :
    HistoricalThirdCoarse.frozenLevel (e : ℝ) chi m omega (N : ℝ)
        (HistoricalThirdCoarse.P1OriginalFourth.history4 p) = (N : ℝ) ^ oldExponent e m j ∧
      P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ)
        (HistoricalThirdCoarse.P1OriginalFourth.history4 p) = (N : ℝ) ^ (cap4 j : ℝ) := by
  have hs := (mem_selectedFourthCells e chi m omega J4 j).mp hj
  have hcast : (qLogPrimeMeshLo 0 (19 / 96) m
      (HistoricalThirdCoarse.P1OriginalFourth.prefix3 j) 2 : ℝ) =
      logPrimeMeshLo 0 (19 / 96) m (HistoricalThirdCoarse.P1OriginalFourth.prefix3 j) 2 := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m
        (HistoricalThirdCoarse.P1OriginalFourth.prefix3 j)) 2
  have hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m
      (HistoricalThirdCoarse.P1OriginalFourth.prefix3 j) 2 := by
    rw [← hcast]
    exact hs.2.2
  constructor
  · rw [oldExponent_eq_actual]
    exact HistoricalThirdCoarse.P1OriginalFourth.frozenLevel_on_selected_jointCell
      (e : ℝ) chi m m omega N hN p hpos _ hs.2.1 j hwhole ht.2.1
  · apply P1OriginalCoarseContinuation.level4_on_selected_cell e chi m omega J4 cap4
      (N : ℝ) _ (by simp [HistoricalThirdCoarse.P1OriginalFourth.history4]) j hj
    rw [HistoricalThirdCoarse.P1OriginalFourth.history4_log]
    exact ht.2.1.1

end
end ImbalancedChen.P1OriginalFourthIntegral
