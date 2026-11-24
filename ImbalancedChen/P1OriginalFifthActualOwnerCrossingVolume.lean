import ImbalancedChen.P1OriginalFifthActualOwnerGateCrossing
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / HELD DEPENDENCIES.
-- Directed slabs for the ACTUAL three moving historical bounds, at fixed
-- mesh and owner. Gamma is never assumed continuous in e. The exact
-- actual cap difference is retained as an argument of the estimate.
namespace ImbalancedChen.P1OriginalFifthActualOwnerCrossingVolume

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalCoarseFifthContinuation
open P1OriginalFifthActualOwnerGateCrossing

private abbrev Point := Fin 5 → ℝ
private abbrev Base := Fin 4 → ℝ

private def rest (a : Fin 5 → ℝ) (k : Fin 5) (y : Base) : ℝ :=
  ∑ i : Fin 4, a (k.succAbove i) * y i

private def baseBox (raw : FifthWireRow) (k : Fin 5) : Set Base :=
  univ.pi (fun i => Icc (raw.lower (k.succAbove i) : ℝ) (raw.upper (k.succAbove i) : ℝ))

private def cylinder (raw : FifthWireRow) (a : Fin 5 → ℝ) (k : Fin 5)
    (A B : ℝ) : Set (ℝ × Base) :=
  {q | q.2 ∈ baseBox raw k ∧ q.1 ∈
    Icc ((min A B - rest a k q.2) / 3) ((max A B - rest a k q.2) / 3)}

private theorem cylinder_measurable (raw : FifthWireRow) (a : Fin 5 → ℝ)
    (k : Fin 5) (A B : ℝ) : MeasurableSet (cylinder raw a k A B) := by
  have hb : MeasurableSet (baseBox raw k) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hr : Continuous (rest a k) := by unfold rest; fun_prop
  exact (hb.preimage measurable_snd).inter
    ((isClosed_le (by fun_prop) continuous_fst).measurableSet.inter
      (isClosed_le continuous_fst (by fun_prop)).measurableSet)

private theorem raw_width (raw : FifthWireRow) (hg : raw.grid = 400) (i : Fin 5) :
    (raw.upper i : ℝ) - (raw.lower i : ℝ) = 1 / 400 := by
  simp only [FifthWireRow.upper, FifthWireRow.lower, hg]
  push_cast
  ring

private theorem directed_length (A B r : ℝ) :
    (max A B - r) / 3 - (min A B - r) / 3 = |A - B| / 3 := by
  by_cases h : A ≤ B
  · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have h' : B ≤ A := le_of_not_ge h
    rw [min_eq_right h', max_eq_left h', abs_of_nonneg (sub_nonneg.mpr h')]
    ring

-- Fubini supplies the interval length for each ACTUAL fiber. All four
-- remaining saved unit widths are exactly 1/400, independently of pivot.
private theorem cylinder_volume (raw : FifthWireRow) (hg : raw.grid = 400)
    (a : Fin 5 → ℝ) (k : Fin 5) (A B : ℝ) :
    volume (cylinder raw a k A B) =
      ENNReal.ofReal (|A - B| / 3) * (ENNReal.ofReal (1 / 400 : ℝ)) ^ 4 := by
  have hb : MeasurableSet (baseBox raw k) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hv : volume (baseBox raw k) = (ENNReal.ofReal (1 / 400 : ℝ)) ^ 4 := by
    rw [baseBox, volume_pi_pi]
    simp_rw [Real.volume_Icc, raw_width raw hg]
    simp
  have hfiber (y : Base) :
      volume ((fun x : ℝ => (x, y)) ⁻¹' cylinder raw a k A B) =
        (baseBox raw k).indicator (fun _ => ENNReal.ofReal (|A - B| / 3)) y := by
    by_cases hy : y ∈ baseBox raw k
    · have heq : ((fun x : ℝ => (x, y)) ⁻¹' cylinder raw a k A B) =
          Icc ((min A B - rest a k y) / 3) ((max A B - rest a k y) / 3) := by
        ext x
        simp [cylinder, hy]
      rw [heq, indicator_of_mem hy, Real.volume_Icc, directed_length]
    · have heq : ((fun x : ℝ => (x, y)) ⁻¹' cylinder raw a k A B) = ∅ := by
        ext x
        simp [cylinder, hy]
      rw [heq, measure_empty, indicator_of_notMem hy]
  change (volume.prod volume) (cylinder raw a k A B) = _
  rw [Measure.prod_apply_symm (cylinder_measurable raw a k A B)]
  simp_rw [hfiber]
  rw [lintegral_indicator hb]
  simp only [lintegral_const, Measure.restrict_apply_univ, hv]

private def slab (a : Fin 5 → ℝ) (A B : ℝ) : Set Point :=
  {t | min A B ≤ ∑ i, a i * t i ∧ ∑ i, a i * t i ≤ max A B}

-- A directed threshold crossing is enclosed by its true interval, so
-- there is no factor two from a symmetric wall strip.
private theorem slab_volume (raw : FifthWireRow) (hg : raw.grid = 400)
    (a : Fin 5 → ℝ) (k : Fin 5) (hk : a k = 3) (A B : ℝ) :
    volume (raw.originalBox ∩ slab a A B) ≤
      ENNReal.ofReal (|A - B| / 3) * (ENNReal.ofReal (1 / 400 : ℝ)) ^ 4 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) k
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin 5 => ℝ) k
  have hsub : raw.originalBox ∩ slab a A B ⊆ e ⁻¹' cylinder raw a k A B := by
    intro t ht
    have hsum : (∑ i : Fin 5, a i * t i) =
        3 * t k + rest a k (fun i => t (k.succAbove i)) := by
      unfold rest
      rw [Fin.sum_univ_succAbove _ k, hk]
    change (t k, fun i => t (k.succAbove i)) ∈ cylinder raw a k A B
    refine ⟨?_, ?_, ?_⟩
    · intro i _hi
      exact ⟨(ht.1 (k.succAbove i)).1, (ht.1 (k.succAbove i)).2.le⟩
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
      have h := ht.2.1
      rw [hsum] at h
      linarith
    · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
      have h := ht.2.2
      rw [hsum] at h
      linarith
  calc
    volume (raw.originalBox ∩ slab a A B) ≤ volume (e ⁻¹' cylinder raw a k A B) :=
      measure_mono hsub
    _ = volume (cylinder raw a k A B) := by
      rw [← Measure.map_apply e.measurable (cylinder_measurable raw a k A B)]
      exact congrArg (fun mu => mu (cylinder raw a k A B)) hmp.map_eq
    _ = _ := cylinder_volume raw hg a k A B

private def firstCoefficients : Fin 5 → ℝ := ![3, 0, 0, 0, 0]
private def thirdCoefficients : Fin 5 → ℝ := ![1, 1, 3, 0, 0]

def initialDifference (e₀ e₁ : ℚ) : ℝ :=
  |HistoricalThirdCoarse.initial (e₀ : ℝ) - HistoricalThirdCoarse.initial (e₁ : ℝ)|

theorem initialDifference_eq_twice_buffer (e₀ e₁ : ℚ) :
    initialDifference e₀ e₁ = 2 * |(e₀ : ℝ) - (e₁ : ℝ)| := by
  have h (C x y : ℝ) : (C - 2 * x) - (C - 2 * y) = (-2) * (x - y) := by ring
  unfold initialDifference HistoricalThirdCoarse.initial
  rw [h, abs_mul]
  norm_num

def thirdCap (e : ℚ) (m : ℕ) (j : Label5 m) : ℝ :=
  HistoricalThirdCoarse.levelExponent (e : ℝ)
    (HistoricalThirdCoarse.box m (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j))

def thirdDifference (e₀ e₁ : ℚ) (m : ℕ) (j : Label5 m) : ℝ :=
  |thirdCap e₀ m j - thirdCap e₁ m j|

private theorem between_of_crossing (x A B : ℝ)
    (h : (x < A ∧ B ≤ x) ∨ (x < B ∧ A ≤ x)) : min A B ≤ x ∧ x ≤ max A B := by
  rcases h with h | h
  · exact ⟨(min_le_right _ _).trans h.2, h.1.le.trans (le_max_left _ _)⟩
  · exact ⟨(min_le_left _ _).trans h.2, h.1.le.trans (le_max_right _ _)⟩

private theorem actual_crossing_subset_three_slabs (e₀ e₁ : ℚ) (m : ℕ) (j : Label5 m) :
    movingGateCrossing e₀ e₁ m j ⊆
      slab firstCoefficients (HistoricalThirdCoarse.initial (e₀ : ℝ))
          (HistoricalThirdCoarse.initial (e₁ : ℝ)) ∪
        slab firstCoefficients (thirdCap e₀ m j) (thirdCap e₁ m j) ∪
          slab thirdCoefficients (thirdCap e₀ m j) (thirdCap e₁ m j) := by
  intro t ht
  obtain ⟨i, hi⟩ := ht
  have hfirst : (∑ s : Fin 5, firstCoefficients s * t s) = 3 * t 0 := by
    simp [firstCoefficients, Fin.sum_univ_succ]
  have hthird : (∑ s : Fin 5, thirdCoefficients s * t s) = t 0 + t 1 + 3 * t 2 := by
    simp [thirdCoefficients, Fin.sum_univ_succ]
  fin_cases i
  · change ((t 1 - t 0 < 0 ∧ 0 ≤ t 1 - t 0) ∨
      (t 1 - t 0 < 0 ∧ 0 ≤ t 1 - t 0)) at hi
    rcases hi with hi | hi <;> linarith
  · change ((t 2 - t 1 < 0 ∧ 0 ≤ t 2 - t 1) ∨
      (t 2 - t 1 < 0 ∧ 0 ≤ t 2 - t 1)) at hi
    rcases hi with hi | hi <;> linarith
  · change ((t 3 - t 2 < 0 ∧ 0 ≤ t 3 - t 2) ∨
      (t 3 - t 2 < 0 ∧ 0 ≤ t 3 - t 2)) at hi
    rcases hi with hi | hi <;> linarith
  · change ((t 4 - t 3 < 0 ∧ 0 ≤ t 4 - t 3) ∨
      (t 4 - t 3 < 0 ∧ 0 ≤ t 4 - t 3)) at hi
    rcases hi with hi | hi <;> linarith
  · apply Or.inl
    apply Or.inl
    change min _ _ ≤ _ ∧ _ ≤ max _ _
    rw [hfirst]
    exact between_of_crossing _ _ _ hi
  · apply Or.inl
    apply Or.inr
    change min _ _ ≤ _ ∧ _ ≤ max _ _
    rw [hfirst]
    exact between_of_crossing _ _ _ hi
  · apply Or.inr
    change min _ _ ≤ _ ∧ _ ≤ max _ _
    rw [hthird]
    exact between_of_crossing _ _ _ hi

-- Sharp directed-slab constant for the saved unit box: two distinct
-- actual cap differences, with the third difference occurring twice.
theorem movingGateCrossing_grid400_volume_le
    (raw : FifthWireRow) (hg : raw.grid = 400) (e₀ e₁ : ℚ)
    (m : ℕ) (j : Label5 m) :
    volume (raw.originalBox ∩ movingGateCrossing e₀ e₁ m j) ≤
      ENNReal.ofReal ((initialDifference e₀ e₁ + 2 * thirdDifference e₀ e₁ m j) /
        (3 * (400 : ℝ) ^ 4)) := by
  let I₀ := HistoricalThirdCoarse.initial (e₀ : ℝ)
  let I₁ := HistoricalThirdCoarse.initial (e₁ : ℝ)
  let G₀ := thirdCap e₀ m j
  let G₁ := thirdCap e₁ m j
  let S₀ := raw.originalBox ∩ slab firstCoefficients I₀ I₁
  let S₁ := raw.originalBox ∩ slab firstCoefficients G₀ G₁
  let S₂ := raw.originalBox ∩ slab thirdCoefficients G₀ G₁
  have hsub : raw.originalBox ∩ movingGateCrossing e₀ e₁ m j ⊆ S₀ ∪ S₁ ∪ S₂ := by
    intro t ht
    rcases actual_crossing_subset_three_slabs e₀ e₁ m j ht.2 with (h | h) | h
    · exact Or.inl (Or.inl ⟨ht.1, h⟩)
    · exact Or.inl (Or.inr ⟨ht.1, h⟩)
    · exact Or.inr ⟨ht.1, h⟩
  have h₀ := slab_volume raw hg firstCoefficients (0 : Fin 5) (by norm_num [firstCoefficients]) I₀ I₁
  have h₁ := slab_volume raw hg firstCoefficients (0 : Fin 5) (by norm_num [firstCoefficients]) G₀ G₁
  have h₂ := slab_volume raw hg thirdCoefficients (2 : Fin 5) (by norm_num [thirdCoefficients]) G₀ G₁
  have hdI : 0 ≤ |I₀ - I₁| / 3 := by positivity
  have hdG : 0 ≤ |G₀ - G₁| / 3 := by positivity
  calc
    volume (raw.originalBox ∩ movingGateCrossing e₀ e₁ m j) ≤ volume (S₀ ∪ S₁ ∪ S₂) := measure_mono hsub
    _ ≤ volume S₀ + volume S₁ + volume S₂ :=
      (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal (|I₀ - I₁| / 3) * (ENNReal.ofReal (1 / 400 : ℝ)) ^ 4 +
        ENNReal.ofReal (|G₀ - G₁| / 3) * (ENNReal.ofReal (1 / 400 : ℝ)) ^ 4 +
        ENNReal.ofReal (|G₀ - G₁| / 3) * (ENNReal.ofReal (1 / 400 : ℝ)) ^ 4 :=
      add_le_add (add_le_add h₀ h₁) h₂
    _ = ENNReal.ofReal ((initialDifference e₀ e₁ + 2 * thirdDifference e₀ e₁ m j) /
        (3 * (400 : ℝ) ^ 4)) := by
      simp_rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 400)]
      rw [← ENNReal.ofReal_mul hdI, ← ENNReal.ofReal_mul hdG, ← ENNReal.ofReal_mul hdG,
        ← ENNReal.ofReal_add (mul_nonneg hdI (by positivity)) (mul_nonneg hdG (by positivity)),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hdI (by positivity))
          (mul_nonneg hdG (by positivity))) (mul_nonneg hdG (by positivity))]
      congr 1
      dsimp only [initialDifference, thirdDifference, I₀, I₁, G₀, G₁]
      ring

-- The fixed-owner base and any positive-cube restriction only decrease
-- the same crossing volume. No arithmetic boundary atom is deleted.
theorem fixedOwnerBase_crossing_volume_le
    (raw : FifthWireRow) (hg : raw.grid = 400) (e₀ e₁ : ℚ) (m : ℕ) (j : Label5 m) :
    volume (fixedOwnerBase raw m j ∩ movingGateCrossing e₀ e₁ m j) ≤
      ENNReal.ofReal ((initialDifference e₀ e₁ + 2 * thirdDifference e₀ e₁ m j) /
        (3 * (400 : ℝ) ^ 4)) := by
  apply (measure_mono (show fixedOwnerBase raw m j ∩ movingGateCrossing e₀ e₁ m j ⊆
      raw.originalBox ∩ movingGateCrossing e₀ e₁ m j from
    fun _ ht => ⟨ht.1.1.1.1, ht.2⟩)).trans
  exact movingGateCrossing_grid400_volume_le raw hg e₀ e₁ m j

end
end ImbalancedChen.P1OriginalFifthActualOwnerCrossingVolume
