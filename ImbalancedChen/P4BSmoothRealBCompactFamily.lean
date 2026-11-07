import ImbalancedChen.P4BSmoothProfileCommonCompactSupport
import ImbalancedChen.P4BSmoothProfileFirstDerivativeBudget

/-!
# Common support and quantitative first derivative over real parameter bands

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual smoothPhysicalProfile is used throughout. The lower endpoint
of the real b band and the upper endpoint of the kappa band determine one
roughness gap. A single cube then contains every profile in the family,
including every width below the chosen width cap and every N >= 2.
The first derivative constant is uniform on a positive width band.

The precision epsilon below is a width cap, not an asserted mass error.
Mass approximation, all mixed Euler orders, the actual source/rho
coefficient class, and whole-box actualwinner licensing remain separate
obligations before genuineUniformPP(A3) can be invoked.
-/

namespace ImbalancedChen.P4B

noncomputable section

open ImbalancedChen.P4BOuterRampRoughness
open ImbalancedChen.P4BSmoothProfileCommonCompactSupport

/-- The worst roughness baseline on a real parameter rectangle occurs at
its lower b endpoint and upper kappa endpoint. -/
theorem baseline_endpoint_le
    {bLo b kappa kappaHi : ℝ} (hbLo : 0 < bLo) (hb : bLo ≤ b)
    (hkappaHi : kappaHi ≤ 1) (hkappa : kappa ≤ kappaHi) :
    baseline bLo kappaHi ≤ baseline b kappa := by
  have hbpos : 0 < b := hbLo.trans_le hb
  have hdLo : 0 < 1 + bLo := by linarith
  have hd : 0 < 1 + b := by linarith
  have hratio : bLo / (1 + bLo) ≤ b / (1 + b) := by
    apply (div_le_div_iff₀ hdLo hd).mpr
    nlinarith only [hb]
  have hratio0 : 0 ≤ b / (1 + b) := div_nonneg hbpos.le hd.le
  calc
    baseline bLo kappaHi = (1 - kappaHi) * (bLo / (1 + bLo)) := by
      unfold baseline
      ring
    _ ≤ (1 - kappaHi) * (b / (1 + b)) :=
      mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr hkappaHi)
    _ ≤ (1 - kappa) * (b / (1 + b)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hkappa]) hratio0
    _ = baseline b kappa := by unfold baseline; ring

/-- Choose one positive smoothing width before varying b, kappa or N.
An arbitrary positive precision cap is allowed, with its dependence visible. -/
theorem exists_realB_family_width
    {bLo kappaHi theta epsilon : ℝ}
    (hgap : theta < baseline bLo kappaHi) (hepsilon : 0 < epsilon) :
    ∃ widthMax : ℝ, 0 < widthMax ∧ widthMax ≤ epsilon ∧
      2 * widthMax ≤ baseline bLo kappaHi - theta := by
  refine ⟨min epsilon ((baseline bLo kappaHi - theta) / 4),
    lt_min hepsilon (by linarith only [hgap]), min_le_left _ _, ?_⟩
  have hcap := min_le_right epsilon ((baseline bLo kappaHi - theta) / 4)
  linarith only [hcap, hgap]

/-- Width enlargement enlarges the common cube; no b or N enters it. -/
theorem commonCube_mono_width {theta width widthMax : ℝ}
    (hwidth : width ≤ widthMax) :
    commonCube theta width ⊆ commonCube theta widthMax := by
  intro v hv
  refine ⟨hv.1, fun i => (hv.2 i).trans ?_⟩
  unfold commonUpper
  exact add_le_add_left
    (div_le_div_of_nonneg_right hwidth (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le) 1

/-- A common compact support is fixed before every member of the real-b
family. In fact no upper b bound is needed for support alone. -/
theorem realB_family_common_compact_support
    {bLo kappaHi theta widthMax : ℝ}
    (hbLo : 0 < bLo) (hkappaHi : kappaHi ≤ 1) (htheta : 0 < theta)
    (hgap : 2 * widthMax ≤ baseline bLo kappaHi - theta) :
    IsCompact (commonCube theta widthMax) ∧
      ∀ b kappa width : ℝ, bLo ≤ b → kappa ≤ kappaHi →
        0 < width → width ≤ widthMax → ∀ N : ℕ, 2 ≤ N →
          tsupport (smoothPhysicalProfile b N (manuscriptHalfProductCutoff kappa N)
            width) ⊆ commonCube theta widthMax := by
  refine ⟨isCompact_commonCube theta widthMax, ?_⟩
  intro b kappa width hb hkappa hwidth hwidthMax N hN
  have hbase := baseline_endpoint_le hbLo hb hkappaHi hkappa
  have hgap' : 2 * width ≤ baseline b kappa - theta := by
    linarith only [hwidthMax, hgap, hbase]
  exact (tsupport_smoothPhysicalProfile_subset_commonCube
    (hbLo.trans_le hb) htheta hN hwidth hgap').trans
      (commonCube_mono_width hwidthMax)

/-- Quantitative first-order control with its constant chosen before b,
width, N, cutoff and point. A positive minimum width is indispensable. -/
theorem exists_realB_family_first_derivative_budget
    {bHi widthMin : ℝ} (hbHi : 0 ≤ bHi) (hwidthMin : 0 < widthMin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b width : ℝ, 0 ≤ b → b ≤ bHi → widthMin ≤ width →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ v : Fin 2 → ℝ,
        ‖fderiv ℝ (smoothPhysicalProfile b N T width) v‖ ≤
          C * (1 + Real.log (N : ℝ)) := by
  obtain ⟨C1, hC1, hderiv⟩ := exists_smoothPhysicalProfile_first_derivative_budget
  have hC1pos : 0 ≤ C1 := zero_le_one.trans hC1
  have hnum : 0 ≤ 4 * C1 * (2 + bHi) :=
    mul_nonneg (mul_nonneg (by norm_num) hC1pos) (by linarith only [hbHi])
  refine ⟨4 * C1 * (2 + bHi) / widthMin, div_nonneg hnum hwidthMin.le, ?_⟩
  intro b width hb hbMax hwidth N hN T v
  have hwidthPos : 0 < width := hwidthMin.trans_le hwidth
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_pos hN1
    linarith
  have hcoeff : 4 * C1 * (2 + |b|) / width ≤
      4 * C1 * (2 + bHi) / widthMin := by
    rw [abs_of_nonneg hb]
    calc
      _ ≤ 4 * C1 * (2 + bHi) / width :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add_left hbMax 2)
            (mul_nonneg (by norm_num) hC1pos)) hwidthPos.le
      _ ≤ _ := div_le_div_of_nonneg_left hnum hwidthMin hwidth
  exact (hderiv b width hwidthPos N hN T v).trans
    (mul_le_mul_of_nonneg_right hcoeff hlog)

end

end ImbalancedChen.P4B
