import ImbalancedChen.CurrentChenUpsilon8HarmonicMean

/-!
# P2: complete negative eighth-term domain cover

SOURCE ONLY / UNCOMPILED. The exact original eighth harmonic domain is
partitioned at the original H and D exponents. No endpoint enclosure,
`currentC` inequality, or missing box table is assumed here.

This supplies a usable predecessor to the negative U8 certificate: every
point of its original domain occurs in exactly one of the three bands,
including points on H and D, and its genuine Lebesgue integral is the sum
of the three genuine integrals. The numerical cell cover and upper
enclosure in the adopted baseline remain separate obligations.
-/

namespace ImbalancedChen.P2NegativeDomainCover

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open Classical

/-- Literal domain of the existing eighth-term harmonic integral. -/
def eighthDomain : Set (Fin 2 → ℝ) :=
  logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ)) (fun _ => (1 / 2 : ℝ)) ∩
    currentChenUpsilon8HarmonicRegion

/-- The full unmodified density, including both prime-coordinate weights. -/
def eighthDensity (x : Fin 2 → ℝ) : ℝ :=
  (1 / (1 - x 0 - x 1)) * ∏ i, 1 / x i

def eighthLow : Set (Fin 2 → ℝ) :=
  eighthDomain ∩ {x | x 0 < (19 / 125 : ℝ)}

def eighthMiddle : Set (Fin 2 → ℝ) :=
  eighthDomain ∩ {x | (19 / 125 : ℝ) ≤ x 0 ∧ x 0 < (59 / 250 : ℝ)}

def eighthHigh : Set (Fin 2 → ℝ) :=
  eighthDomain ∩ {x | (59 / 250 : ℝ) ≤ x 0}

theorem measurableSet_eighthDomain : MeasurableSet eighthDomain := by
  exact (measurableSet_logPrimeBox _ _).inter
    measurableSet_currentChenUpsilon8HarmonicRegion

theorem measurableSet_eighthLow : MeasurableSet eighthLow := by
  exact measurableSet_eighthDomain.inter
    (measurableSet_lt (continuous_apply 0).measurable measurable_const)

theorem measurableSet_eighthMiddle : MeasurableSet eighthMiddle := by
  exact measurableSet_eighthDomain.inter
    ((measurableSet_le measurable_const (continuous_apply 0).measurable).inter
      (measurableSet_lt (continuous_apply 0).measurable measurable_const))

theorem measurableSet_eighthHigh : MeasurableSet eighthHigh := by
  exact measurableSet_eighthDomain.inter
    (measurableSet_le measurable_const (continuous_apply 0).measurable)

/-- The ambient cube walls are redundant in precisely these moving slices.
The weak wall y=1/3 and strict moving upper wall are both retained. -/
theorem eighthDomain_vec_iff (x y : ℝ) :
    ![x, y] ∈ eighthDomain ↔
      x ∈ Ico (417 / 5000 : ℝ) (1 / 3 : ℝ) ∧
        y ∈ Ico (1 / 3 : ℝ) ((1 - x) / 2) := by
  constructor
  · rintro ⟨hbox, hr⟩
    have hx := mem_logPrimeBox.mp hbox (0 : Fin 2)
    change 417 / 5000 ≤ x ∧ x < (1 / 2 : ℝ) at hx
    change x < 1 / 3 ∧ 1 / 3 ≤ y ∧ x + 2 * y < 1 at hr
    exact ⟨⟨hx.1, hr.1⟩, ⟨hr.2.1, by linarith only [hr.2.2]⟩⟩
  · rintro ⟨hx, hy⟩
    refine ⟨mem_logPrimeBox.mpr ?_, ?_⟩
    · intro i
      fin_cases i
      · change 417 / 5000 ≤ x ∧ x < (1 / 2 : ℝ)
        exact ⟨hx.1, by linarith only [hx.2]⟩
      · change 417 / 5000 ≤ y ∧ y < (1 / 2 : ℝ)
        constructor <;> linarith only [hx.1, hy.1, hy.2]
    · change x < 1 / 3 ∧ 1 / 3 ≤ y ∧ x + 2 * y < 1
      exact ⟨hx.2, hy.1, by linarith only [hy.2]⟩

/-- Full coverage, without discarding either internal rational wall. -/
theorem eighthDomain_eq_three_bands :
    eighthDomain = (eighthLow ∪ eighthMiddle) ∪ eighthHigh := by
  ext x
  constructor
  · intro hx
    by_cases hH : x 0 < (19 / 125 : ℝ)
    · exact Or.inl (Or.inl ⟨hx, hH⟩)
    · by_cases hD : x 0 < (59 / 250 : ℝ)
      · exact Or.inl (Or.inr ⟨hx, le_of_not_gt hH, hD⟩)
      · exact Or.inr ⟨hx, le_of_not_gt hD⟩
  · rintro ((hx | hx) | hx)
    · exact hx.1
    · exact hx.1
    · exact hx.1

theorem eighthLow_disjoint_middle : Disjoint eighthLow eighthMiddle := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_lt_of_ge hy.2.1) hx.2

theorem eighthLow_disjoint_high : Disjoint eighthLow eighthHigh := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hxl : x 0 < (19 / 125 : ℝ) := hx.2
  have hyl : (59 / 250 : ℝ) ≤ x 0 := hy.2
  linarith only [hxl, hyl]

theorem eighthMiddle_disjoint_high : Disjoint eighthMiddle eighthHigh := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_lt_of_ge hy.2) hx.2.2

private def eighthExtendedDensity (x : Fin 2 → ℝ) : ℝ :=
  currentChenUpsilon8HarmonicKernel x * ∏ i, 1 / x i

/-- Integrability is supplied by the actual continuous extension, with
the positive original lower endpoint, rather than by a numerical claim. -/
private theorem integrableOn_eighthExtendedDensity :
    IntegrableOn eighthExtendedDensity eighthDomain := by
  exact (integrableOn_logPrimeBox_test_cube (by norm_num : (0 : ℝ) < 417 / 5000)
    currentChenUpsilon8HarmonicKernel
    continuous_currentChenUpsilon8HarmonicKernel.continuousOn).mono_set inter_subset_left

private theorem eighthExtendedDensity_eq {x : Fin 2 → ℝ} (hx : x ∈ eighthDomain) :
    eighthExtendedDensity x = eighthDensity x := by
  unfold eighthExtendedDensity eighthDensity
  rw [currentChenUpsilon8HarmonicKernel_eq hx.2]

private theorem eighthExtendedIntegral_eq (S : Set (Fin 2 → ℝ))
    (hS : MeasurableSet S) (hsub : S ⊆ eighthDomain) :
    (∫ x in S, eighthExtendedDensity x) = ∫ x in S, eighthDensity x := by
  apply setIntegral_congr_fun hS
  intro x hx
  exact eighthExtendedDensity_eq (hsub hx)

/-- Genuine Fubini reduction of the full eighth term to its exact moving
slices. This is the actual density, rather than its continuous extension. -/
theorem eighthHarmonicIntegral_eq_nested :
    currentChenUpsilon8HarmonicIntegral =
      ∫ x in Ico (417 / 5000 : ℝ) (1 / 3 : ℝ),
        ∫ y in Ico (1 / 3 : ℝ) ((1 - x) / 2),
          1 / (x * y * (1 - x - y)) := by
  let F := eighthDomain.indicator eighthExtendedDensity
  have hF : Integrable F :=
    integrableOn_eighthExtendedDensity.integrable_indicator measurableSet_eighthDomain
  let E := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinTwo _
  have hPF : Integrable (fun p : ℝ × ℝ => F (E.symm p)) :=
    (hE.symm.integrable_comp_emb E.symm.measurableEmbedding).mpr hF
  have hvec (x y : ℝ) : E.symm (x, y) = ![x, y] := by
    ext i
    fin_cases i <;> rfl
  have hpoint (x y : ℝ) : F ![x, y] =
      (Ico (417 / 5000 : ℝ) (1 / 3 : ℝ)).indicator
        (fun x => (Ico (1 / 3 : ℝ) ((1 - x) / 2)).indicator
          (fun y => 1 / (x * y * (1 - x - y))) y) x := by
    change eighthDomain.indicator eighthExtendedDensity ![x, y] = _
    by_cases hx : x ∈ Ico (417 / 5000 : ℝ) (1 / 3 : ℝ)
    · by_cases hy : y ∈ Ico (1 / 3 : ℝ) ((1 - x) / 2)
      · have hxy := (eighthDomain_vec_iff x y).mpr ⟨hx, hy⟩
        rw [indicator_of_mem hxy, indicator_of_mem hx, indicator_of_mem hy,
          eighthExtendedDensity_eq hxy]
        simp only [eighthDensity, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, one_div, mul_inv_rev]
        ring
      · have hxy : ![x, y] ∉ eighthDomain := fun hxy =>
          hy ((eighthDomain_vec_iff x y).mp hxy).2
        rw [indicator_of_notMem hxy, indicator_of_mem hx, indicator_of_notMem hy]
    · have hxy : ![x, y] ∉ eighthDomain := fun hxy =>
        hx ((eighthDomain_vec_iff x y).mp hxy).1
      rw [indicator_of_notMem hxy, indicator_of_notMem hx]
  calc
    currentChenUpsilon8HarmonicIntegral = ∫ t in eighthDomain, eighthExtendedDensity t :=
      (eighthExtendedIntegral_eq eighthDomain measurableSet_eighthDomain
        (fun _ hx => hx)).symm
    _ = ∫ t, F t := (integral_indicator measurableSet_eighthDomain).symm
    _ = ∫ p : ℝ × ℝ, F (E.symm p) := (hE.symm.integral_comp' F).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, F (E.symm (x, y)) := integral_prod _ hPF
    _ = ∫ x : ℝ, ∫ y : ℝ, F ![x, y] := by simp only [hvec]
    _ = ∫ x : ℝ, (Ico (417 / 5000 : ℝ) (1 / 3 : ℝ)).indicator
        (fun x => ∫ y in Ico (1 / 3 : ℝ) ((1 - x) / 2),
          1 / (x * y * (1 - x - y))) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Ico (417 / 5000 : ℝ) (1 / 3 : ℝ)
      · rw [indicator_of_mem hx]
        simp_rw [hpoint, indicator_of_mem hx]
        exact integral_indicator measurableSet_Ico
      · rw [indicator_of_notMem hx]
        simp_rw [hpoint, indicator_of_notMem hx]
        exact integral_zero ℝ ℝ
    _ = _ := integral_indicator measurableSet_Ico

/-- Complete disjoint integral cover for the literal negative eighth-term
integral. All three integrals use its unmodified original density. -/
theorem eighthHarmonicIntegral_eq_three_bands :
    currentChenUpsilon8HarmonicIntegral =
      (∫ x in eighthLow, eighthDensity x) +
      (∫ x in eighthMiddle, eighthDensity x) +
      (∫ x in eighthHigh, eighthDensity x) := by
  have hL : IntegrableOn eighthExtendedDensity eighthLow :=
    integrableOn_eighthExtendedDensity.mono_set inter_subset_left
  have hM : IntegrableOn eighthExtendedDensity eighthMiddle :=
    integrableOn_eighthExtendedDensity.mono_set inter_subset_left
  have hH : IntegrableOn eighthExtendedDensity eighthHigh :=
    integrableOn_eighthExtendedDensity.mono_set inter_subset_left
  have hLMH : Disjoint (eighthLow ∪ eighthMiddle) eighthHigh := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp eighthLow_disjoint_high hx hy
    · exact Set.disjoint_left.mp eighthMiddle_disjoint_high hx hy
  calc
    currentChenUpsilon8HarmonicIntegral = ∫ x in eighthDomain, eighthDensity x := rfl
    _ = ∫ x in eighthDomain, eighthExtendedDensity x :=
      (eighthExtendedIntegral_eq eighthDomain measurableSet_eighthDomain (fun _ hx => hx)).symm
    _ = (∫ x in eighthLow, eighthExtendedDensity x) +
        (∫ x in eighthMiddle, eighthExtendedDensity x) +
        (∫ x in eighthHigh, eighthExtendedDensity x) := by
      rw [eighthDomain_eq_three_bands]
      rw [setIntegral_union hLMH measurableSet_eighthHigh (hL.union hM) hH]
      rw [setIntegral_union eighthLow_disjoint_middle measurableSet_eighthMiddle hL hM]
    _ = _ := by
      rw [eighthExtendedIntegral_eq eighthLow measurableSet_eighthLow inter_subset_left,
        eighthExtendedIntegral_eq eighthMiddle measurableSet_eighthMiddle inter_subset_left,
        eighthExtendedIntegral_eq eighthHigh measurableSet_eighthHigh inter_subset_left]

end

end ImbalancedChen.P2NegativeDomainCover
