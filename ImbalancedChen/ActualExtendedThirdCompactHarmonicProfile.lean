import ImbalancedChen.ActualExtendedThirdCompactCellConvergence
import ImbalancedChen.ActualPrimeIcoCellTestFunctions

/-!
# The actual compact-cell harmonic test profile

The prime test measure already contributes one reciprocal of each log
coordinate. The test profile supplies the remaining reciprocal of z.
Its positive clamp is a continuous extension only; it agrees exactly
with the original cell kernel on the actual owned, ordered cell.

Both ordering walls and every Ico ownership boundary are kept in the
arithmetic selector. The strict/weak affine sandwich is pointwise and
does not assume that prime atoms on a wall disappear.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical BigOperators

def actualExtendedThirdCompactHarmonicProfile (e h lam : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  4 * (actualExtendedThirdLowerFactor
      ((thirdPrefixTheta - 2 * e - t 0 - t 1 - t 2) / max (h / 2) (t 2)) -
    actualExtendedThirdLowerFactor ((lam - t 0 - t 1 - t 2) / max (h / 2) (t 2))) /
      max (h / 2) (t 2)

theorem continuous_actualExtendedThirdCompactHarmonicProfile {h : ℝ}
    (hh : 0 < h) (e lam : ℝ) :
    Continuous (actualExtendedThirdCompactHarmonicProfile e h lam) := by
  have hx : Continuous (fun t : Fin 3 → ℝ => t 0) := continuous_apply 0
  have hy : Continuous (fun t : Fin 3 → ℝ => t 1) := continuous_apply 1
  have hz : Continuous (fun t : Fin 3 → ℝ => t 2) := continuous_apply 2
  have hden : Continuous (fun t : Fin 3 → ℝ => max (h / 2) (t 2)) :=
    continuous_const.max hz
  have hne (t : Fin 3 → ℝ) : max (h / 2) (t 2) ≠ 0 :=
    ne_of_gt ((half_pos hh).trans_le (le_max_left _ _))
  unfold actualExtendedThirdCompactHarmonicProfile
  exact (continuous_const.mul
    ((continuous_actualExtendedThirdLowerFactor.comp
      ((((continuous_const.sub hx).sub hy).sub hz).div hden hne)).sub
        (continuous_actualExtendedThirdLowerFactor.comp
          ((((continuous_const.sub hx).sub hy).sub hz).div hden hne)))).div hden hne

def actualExtendedThirdCompactCellPrimeRegion (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : Set (Fin 3 → ℝ) :=
  actualExtendedThirdOwnedCell m j ∩ actualExtendedThirdClosedOrderRegion thirdPrefixRho

theorem measurableSet_actualExtendedThirdCompactCellPrimeRegion (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) :
    MeasurableSet (actualExtendedThirdCompactCellPrimeRegion m j) :=
  (measurableSet_actualExtendedThirdOwnedCell m j).inter
    (measurableSet_actualExtendedThirdClosedOrderRegion thirdPrefixRho)

def actualExtendedThirdCompactOrderForms : Fin 2 → (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ![ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1 -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0,
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2 -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1]

theorem actualExtendedThirdCompactOrderForms_ne_zero :
    ∀ i, actualExtendedThirdCompactOrderForms i ≠ 0 := by
  intro i h
  have he := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L ![0, 1, 2]) h
  fin_cases i
  · change (1 : ℝ) - 0 = 0 at he
    norm_num at he
  · change (2 : ℝ) - 1 = 0 at he
    norm_num at he

def actualExtendedThirdCompactCellForms : Fin (3 + (3 + 2)) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
  primeIcoBoxGateForms actualExtendedThirdCompactOrderForms

def actualExtendedThirdCompactCellBounds (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) :
    Fin (3 + (3 + 2)) → ℝ :=
  primeIcoBoxGateBounds (actualExtendedThirdDyadicLo m j)
    (actualExtendedThirdDyadicHi m j) (fun _ : Fin 2 => 0)

theorem actualExtendedThirdCompactCellForms_ne_zero :
    ∀ i, actualExtendedThirdCompactCellForms i ≠ 0 :=
  primeIcoBoxGateForms_ne_zero _ actualExtendedThirdCompactOrderForms_ne_zero

theorem actualExtendedThirdCompactCellPrimeRegion_sandwich {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) :
    primeAffineGateRegion actualExtendedThirdCompactCellForms
        (actualExtendedThirdCompactCellBounds m j) ⊆ actualExtendedThirdCompactCellPrimeRegion m j ∧
      ∀ t ∈ actualExtendedThirdCompactCellPrimeRegion m j, ∀ i,
        actualExtendedThirdCompactCellForms i t ≤ actualExtendedThirdCompactCellBounds m j i := by
  constructor
  · intro t ht
    obtain ⟨hb, hg⟩ := (mem_primeIcoBoxStrictGateRegion
      (actualExtendedThirdDyadicLo m j) (actualExtendedThirdDyadicHi m j)
      actualExtendedThirdCompactOrderForms (fun _ : Fin 2 => 0) t).mp ht
    have hyx : t 1 < t 0 := by
      have hg0 := hg 0
      change t 1 - t 0 < 0 at hg0
      linarith
    have hzy : t 2 < t 1 := by
      have hg1 := hg 1
      change t 2 - t 1 < 0 at hg1
      linarith
    have hz : 0 < t 2 := hh.trans_le ((Finset.mem_filter.mp hj).2.trans (hb 2).1.le)
    have hxrho : t 0 ≤ thirdPrefixRho :=
      (hb 0).2.le.trans (actualExtendedThirdDyadic_bounds m j 0).2.2
    have hzrho : t 2 ≤ thirdPrefixRho := (hzy.le.trans hyx.le).trans hxrho
    exact ⟨⟨fun i _ => ⟨(hb i).1.le, (hb i).2⟩, ⟨hz.le, hzy.le, hyx.le⟩⟩,
      ⟨hz, hzrho, hzy.le, hyx.le, hxrho⟩⟩
  · intro t ht
    simp only [actualExtendedThirdCompactCellForms, actualExtendedThirdCompactCellBounds,
      primeIcoBoxGateForms, primeIcoBoxGateBounds, Fin.forall_fin_add,
      Fin.append_left, Fin.append_right, neg_apply, ContinuousLinearMap.proj_apply,
      neg_le_neg_iff]
    refine ⟨fun i => (ht.1.1 i (mem_univ _)).1,
      fun i => (ht.1.1 i (mem_univ _)).2.le, ?_⟩
    intro i
    fin_cases i
    · change t 1 - t 0 ≤ 0
      linarith only [ht.2.2.2.2.1]
    · change t 2 - t 1 ≤ 0
      linarith only [ht.2.2.2.1]

theorem actualExtendedThirdCompactCellPrimeRegion_subset_cube {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) :
    actualExtendedThirdCompactCellPrimeRegion m j ⊆
      logPrimeBox (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1) := by
  intro t ht
  have hz : h ≤ t 2 := (Finset.mem_filter.mp hj).2.trans (ht.1.1 2 (mem_univ _)).1
  have hlow (i : Fin 3) : h ≤ t i := by
    fin_cases i
    · exact (hz.trans ht.2.2.2.1).trans ht.2.2.2.2.1
    · exact hz.trans ht.2.2.2.1
    · exact hz
  have hhigh (i : Fin 3) : t i ≤ thirdPrefixRho := by
    fin_cases i
    · exact ht.2.2.2.2.2
    · exact ht.2.2.2.2.1.trans ht.2.2.2.2.2
    · exact (ht.2.2.2.1.trans ht.2.2.2.2.1).trans ht.2.2.2.2.2
  apply mem_logPrimeBox.mpr
  intro i
  exact ⟨(by linarith : h / 2 ≤ h).trans (hlow i),
    (hhigh i).trans_lt (by linarith)⟩

theorem actualExtendedThirdCompactHarmonicProfile_density {e h lam : ℝ}
    (hh : 0 < h) {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdClosedOrderRegion thirdPrefixRho) (hz : h ≤ t 2) :
    actualExtendedThirdCompactHarmonicProfile e h lam t * (∏ i : Fin 3, 1 / t i) =
      actualExtendedThirdCapKernel e lam (t 0) (t 1) (t 2) := by
  have hx0 : t 0 ≠ 0 := ne_of_gt (ht.1.trans_le (ht.2.2.1.trans ht.2.2.2.1))
  have hy0 : t 1 ≠ 0 := ne_of_gt (ht.1.trans_le ht.2.2.1)
  have hz0 : t 2 ≠ 0 := ne_of_gt ht.1
  have hfield (A : ℝ) :
      (4 * A / t 2) * (∏ i : Fin 3, 1 / t i) = 4 * A / (t 0 * t 1 * t 2 ^ 2) := by
    rw [Fin.prod_univ_three]
    field_simp [hx0, hy0, hz0]
  unfold actualExtendedThirdCompactHarmonicProfile actualExtendedThirdCapKernel
  simp only [max_eq_right (by linarith : h / 2 ≤ t 2)]
  exact hfield _

end

end ImbalancedChen
