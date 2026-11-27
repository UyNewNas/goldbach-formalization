import ImbalancedChen.ActualExtendedThirdOrderedIntegral
import ImbalancedChen.AffinePrimeGates

/-!
# Closed manuscript faces and the actual extended third-tail integral

The manuscript uses `0 < z <= y <= x <= rho` and a non-strict old cube.
The ordered Tonelli module uses its fixed half-open ownership. The sole
additional ordering face is contained in the actual proper affine wall
`y = z`, whose volume is proved zero. The old-cube equality is paid more
strongly: both clamped lower factors vanish there, so the kernel is zero
pointwise. No boundary-nullness or integrability assumption is supplied.

This concerns the ideal continuous functional. Robust finite coarse policy
coverage, convergence of its caps, and its arithmetic mean remain separate.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ENNReal

def actualExtendedThirdOrderWallForm : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (1 : Fin 3) -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (2 : Fin 3)

theorem actualExtendedThirdOrderWallForm_ne_zero : actualExtendedThirdOrderWallForm ≠ 0 := by
  intro hz
  have hh := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L ![0, 1, 0]) hz
  norm_num [actualExtendedThirdOrderWallForm, Matrix.cons_val_two] at hh

theorem actualExtendedThirdOrderWall_volume_zero :
    volume {t : Fin 3 → ℝ | t 1 = t 2} = 0 := by
  simpa [actualExtendedThirdOrderWallForm, sub_eq_zero] using
    affinePrimeWall_volume_zero actualExtendedThirdOrderWallForm
      actualExtendedThirdOrderWallForm_ne_zero 0

def actualExtendedThirdClosedOrderRegion (h : ℝ) : Set (Fin 3 → ℝ) :=
  {t | 0 < t 2 ∧ t 2 ≤ h ∧ t 2 ≤ t 1 ∧ t 1 ≤ t 0 ∧ t 0 ≤ thirdPrefixRho}

theorem measurableSet_actualExtendedThirdClosedOrderRegion (h : ℝ) :
    MeasurableSet (actualExtendedThirdClosedOrderRegion h) := by
  have hx : Continuous (fun t : Fin 3 → ℝ => t 0) := continuous_apply 0
  have hy : Continuous (fun t : Fin 3 → ℝ => t 1) := continuous_apply 1
  have hz : Continuous (fun t : Fin 3 → ℝ => t 2) := continuous_apply 2
  exact (isOpen_lt continuous_const hz).measurableSet.inter
    ((isClosed_le hz continuous_const).measurableSet.inter
      ((isClosed_le hz hy).measurableSet.inter
        ((isClosed_le hy hx).measurableSet.inter (isClosed_le hx continuous_const).measurableSet)))

theorem actualExtendedThirdClosedOrderRegion_ae_eq (h : ℝ) :
    actualExtendedThirdClosedOrderRegion h =ᵐ[volume] actualExtendedThirdOrderedTailRegion h := by
  have hne : ∀ᵐ t : Fin 3 → ℝ ∂volume, t 1 ≠ t 2 := by
    rw [ae_iff]
    simpa only [not_not] using actualExtendedThirdOrderWall_volume_zero
  rw [Filter.eventuallyEq_set]
  filter_upwards [hne] with t ht
  change (0 < t 2 ∧ t 2 ≤ h ∧ t 2 ≤ t 1 ∧ t 1 ≤ t 0 ∧ t 0 ≤ thirdPrefixRho) ↔
    (0 < t 2 ∧ t 2 ≤ h ∧ t 2 < t 0 ∧ t 0 ≤ thirdPrefixRho ∧ t 2 < t 1 ∧ t 1 ≤ t 0)
  constructor
  · rintro ⟨hz, hzh, hzy, hyx, hx⟩
    have hzy' : t 2 < t 1 := lt_of_le_of_ne hzy ht.symm
    exact ⟨hz, hzh, hzy'.trans_le hyx, hx, hzy', hyx⟩
  · rintro ⟨hz, hzh, _hzx, hx, hzy, hyx⟩
    exact ⟨hz, hzh, hzy.le, hyx, hx⟩

/-- The non-strict old-cube face has zero kernel pointwise. -/
theorem actualExtendedThirdOrderedKernel_eq_zero_on_oldCube {e x y z : ℝ}
    (hz : 0 < z) (hcube : x + y + 3 * z = thirdPrefixTheta - 2 * e) :
    actualExtendedThirdOrderedKernel e x y z = 0 := by
  have hold : (thirdPrefixTheta - 2 * e - x - y - z) / z = 2 :=
    (div_eq_iff hz.ne').mpr (by linarith)
  have hcap := thirdPrefixBufferedCap_le_root e (actualExtendedThirdEnvelope x y z)
  have hnew : (actualExtendedThirdBufferedCap e x y z - x - y - z) / z ≤ 2 := by
    apply (div_le_iff₀ hz).mpr
    change actualExtendedThirdBufferedCap e x y z ≤ thirdPrefixTheta - 2 * e at hcap
    linarith
  unfold actualExtendedThirdOrderedKernel
  rw [hold, actualExtendedThirdLowerFactor_of_le_two le_rfl,
    actualExtendedThirdLowerFactor_of_le_two hnew]
  simp only [sub_self, mul_zero, zero_div]

/-- The manuscript's literal ordered tail domain, including its old-cube face. -/
def actualExtendedThirdManuscriptTailRegion (e h : ℝ) : Set (Fin 3 → ℝ) :=
  actualExtendedThirdClosedOrderRegion h ∩
    {t | t 0 + t 1 + 3 * t 2 ≤ thirdPrefixTheta - 2 * e}

theorem measurableSet_actualExtendedThirdManuscriptTailRegion (e h : ℝ) :
    MeasurableSet (actualExtendedThirdManuscriptTailRegion e h) := by
  have hx : Continuous (fun t : Fin 3 → ℝ => t 0) := continuous_apply 0
  have hy : Continuous (fun t : Fin 3 → ℝ => t 1) := continuous_apply 1
  have hz : Continuous (fun t : Fin 3 → ℝ => t 2) := continuous_apply 2
  exact (measurableSet_actualExtendedThirdClosedOrderRegion h).inter
    (isClosed_le ((hx.add hy).add (hz.const_mul 3)) continuous_const).measurableSet

theorem actualExtendedThirdManuscript_indicator (e h : ℝ) (t : Fin 3 → ℝ) :
    (actualExtendedThirdManuscriptTailRegion e h).indicator
        (fun t => actualExtendedThirdOrderedKernel e (t 0) (t 1) (t 2)) t =
      (actualExtendedThirdClosedOrderRegion h).indicator
        (fun t => actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)) t := by
  by_cases ho : t ∈ actualExtendedThirdClosedOrderRegion h
  · rw [indicator_of_mem ho]
    by_cases hc : t 0 + t 1 + 3 * t 2 < thirdPrefixTheta - 2 * e
    · have hm : t ∈ actualExtendedThirdManuscriptTailRegion e h := ⟨ho, hc.le⟩
      rw [indicator_of_mem hm, actualExtendedThirdGatedKernel, if_pos hc]
    · by_cases hle : t 0 + t 1 + 3 * t 2 ≤ thirdPrefixTheta - 2 * e
      · have hm : t ∈ actualExtendedThirdManuscriptTailRegion e h := ⟨ho, hle⟩
        have hzero := actualExtendedThirdOrderedKernel_eq_zero_on_oldCube ho.1
          (le_antisymm hle (not_lt.mp hc))
        rw [indicator_of_mem hm, actualExtendedThirdGatedKernel, if_neg hc, hzero]
      · have hm : t ∉ actualExtendedThirdManuscriptTailRegion e h := fun ht => hle ht.2
        rw [indicator_of_notMem hm, actualExtendedThirdGatedKernel, if_neg hc]
  · have hm : t ∉ actualExtendedThirdManuscriptTailRegion e h := fun ht => ho ht.1
    rw [indicator_of_notMem hm, indicator_of_notMem ho]

theorem actualExtendedThirdManuscript_indicator_ae (e h : ℝ) :
    (actualExtendedThirdManuscriptTailRegion e h).indicator
        (fun t => actualExtendedThirdOrderedKernel e (t 0) (t 1) (t 2)) =ᵐ[volume]
      (actualExtendedThirdOrderedTailRegion h).indicator
        (fun t => actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)) := by
  filter_upwards [(actualExtendedThirdClosedOrderRegion_ae_eq h).mem_iff] with t ht
  rw [actualExtendedThirdManuscript_indicator]
  by_cases hc : t ∈ actualExtendedThirdClosedOrderRegion h
  · rw [indicator_of_mem hc, indicator_of_mem (ht.mp hc)]
  · rw [indicator_of_notMem hc, indicator_of_notMem (fun ho => hc (ht.mpr ho))]

/-- Genuine integrability on the manuscript domain follows from the already
verified positive tail mass, after paying every changed boundary. -/
theorem integrableOn_actualExtendedThirdManuscriptKernel {e h : ℝ}
    (he : e ≤ 1 / 384) (hh : 0 < h) (hsmall : h ≤ thirdPrefixTailMargin / 4) :
    IntegrableOn (fun t : Fin 3 → ℝ => actualExtendedThirdOrderedKernel e (t 0) (t 1) (t 2))
      (actualExtendedThirdManuscriptTailRegion e h) := by
  have hI : Integrable ((actualExtendedThirdOrderedTailRegion h).indicator
      (fun t => actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2))) :=
    (integrable_indicator_iff (measurableSet_actualExtendedThirdOrderedTailRegion h)).2
      (integrableOn_actualExtendedThirdGatedKernel he hh hsmall)
  exact (integrable_indicator_iff (measurableSet_actualExtendedThirdManuscriptTailRegion e h)).1
    (hI.congr (actualExtendedThirdManuscript_indicator_ae e h).symm)

/-- The closed ordered manuscript functional equals the Core's finite real mass. -/
theorem integral_actualExtendedThirdManuscriptKernel_eq_core {e h : ℝ}
    (he : e ≤ 1 / 384) (hsmall : h ≤ thirdPrefixTailMargin / 4) :
    (∫ t in actualExtendedThirdManuscriptTailRegion e h,
      actualExtendedThirdOrderedKernel e (t 0) (t 1) (t 2)) =
      (actualExtendedThirdIdealTailMass e h).toReal := by
  rw [← integral_indicator (measurableSet_actualExtendedThirdManuscriptTailRegion e h)]
  calc
    _ = ∫ t, (actualExtendedThirdOrderedTailRegion h).indicator
        (fun t => actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)) t :=
      integral_congr_ae (actualExtendedThirdManuscript_indicator_ae e h)
    _ = _ := by
      rw [integral_indicator (measurableSet_actualExtendedThirdOrderedTailRegion h)]
      exact integral_actualExtendedThirdGatedKernel_eq_core he hsmall

end

end ImbalancedChen
