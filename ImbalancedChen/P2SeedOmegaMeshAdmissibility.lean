import ImbalancedChen.P2SeedOmegaFiniteMesh
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual finite sampler is admissible: measurability, actual sampled
kernel bound128, inner integrability at EVERY outer point, and outer
integrability through the genuine product integral are all proved.
The original closed bad region is preserved in the integration, including
its max boundary and both pieces. No integral/error/certificate premise.
-/

namespace ImbalancedChen.P2SeedOmegaMeshAdmissibility
noncomputable section
open Set MeasureTheory Filter
open scoped Interval
open P2SeedOmegaLiteralFibre
open P2SeedOmegaBadCellSemantics (actualBadKernel)
open P2SeedOmegaBadSpatialModulus
open P2SeedOmegaBadUniformIntegralError
open P2SeedOmegaFiniteMesh

theorem actual_bad_kernel_measurable (alpha : ℝ) :
    Measurable (fun p : ℝ×ℝ => actualBadKernel alpha p.1 p.2) := by
  have harg : Measurable (fun p : ℝ×ℝ => badArgument alpha p.1 p.2) := by
    unfold badArgument
    fun_prop
  exact (measurable_const.mul (LiLiuPrereqBuchstab.continuous_buchstab.measurable.comp harg)).div
    (measurable_fst.mul measurable_snd)

theorem mesh_kernel_measurable (alpha : ℝ) (n : ℕ) :
    Measurable (fun p : ℝ×ℝ => sampledKernel alpha (meshSample n) p.1 p.2) :=
  (actual_bad_kernel_measurable alpha).comp (meshSample_measurable n)

theorem actual_bad_kernel_rectangle_bound {alpha : ℝ} (ha : 2≤alpha)
    {p : ℝ×ℝ} (hp : p ∈ primeRectangle) :
    ‖actualBadKernel alpha p.1 p.2‖≤128 := by
  have harg := bad_argument_lower ha hp.2.1 hp.2.2
  have harg1 : 1≤badArgument alpha p.1 p.2 := by linarith only [harg]
  have hω : |LiLiuPrereqBuchstab.buchstab (badArgument alpha p.1 p.2)|≤1 := by
    rw [abs_of_nonneg (LiLiuPrereqBuchstab.buchstab_nonneg harg1)]
    exact LiLiuPrereqBuchstab.buchstab_le_one harg1
  have hu4 : (1/4:ℝ)≤p.1 := by dsimp [corner] at hp; linarith only [hp.1.1]
  have hv4 : (1/4:ℝ)≤p.2 := by dsimp [corner] at hp; linarith only [hp.1.2]
  have hu0 : 0<p.1 := lt_of_lt_of_le (by norm_num) hu4
  have hv0 : 0<p.2 := lt_of_lt_of_le (by norm_num) hv4
  have hden : (1/16:ℝ)≤p.1*p.2 := by
    have h := mul_le_mul hu4 hv4 (by norm_num : (0:ℝ)≤1/4) hu0.le
    simpa only [show (1/4:ℝ)*(1/4)=1/16 by norm_num] using h
  have hcoef : 0≤K*s0/4 := by norm_num [K,s0]
  have hcoef8 : K*s0/4≤8 := by norm_num [K,s0]
  have hn := (mul_le_mul_of_nonneg_left hω hcoef).trans
    (by simpa only [mul_one] using hcoef8)
  rw [Real.norm_eq_abs,actualBadKernel,abs_div,abs_mul,abs_of_nonneg hcoef,
    abs_of_pos (mul_pos hu0 hv0)]
  calc
    _ ≤ 8/(p.1*p.2) := div_le_div_of_nonneg_right hn (mul_pos hu0 hv0).le
    _ ≤ 8/(1/16) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    _ = 128 := by norm_num

theorem mesh_kernel_rectangle_bound {alpha : ℝ} (ha : 2≤alpha) (n : ℕ)
    {p : ℝ×ℝ} (hp : p ∈ primeRectangle) :
    ‖sampledKernel alpha (meshSample n) p.1 p.2‖≤128 :=
  actual_bad_kernel_rectangle_bound ha (meshSample_coordinates n hp).1

def badClosed : Set (ℝ×ℝ) := primeRectangle ∩ {p | badLower p.1≤p.2}

theorem badClosed_dictionary (u v : ℝ) :
    (u,v) ∈ badClosed ↔ u ∈ Icc corner a2 ∧ v ∈ Icc (badLower u) a2 := by
  constructor
  · rintro ⟨hp,hg⟩
    exact ⟨⟨hp.1.1,hp.2.1⟩,⟨hg,hp.2.2⟩⟩
  · rintro ⟨hu,hv⟩
    exact ⟨bad_support_in_primeRectangle hu hv,hv.1⟩

theorem badClosed_measurable : MeasurableSet badClosed := by
  have hL : Continuous (fun p : ℝ×ℝ => badLower p.1) := by unfold badLower; fun_prop
  exact (isClosed_Icc.inter (isClosed_le hL continuous_snd)).measurableSet

theorem mesh_kernel_integrableOn_rectangle {alpha : ℝ} (ha : 2≤alpha) (n : ℕ) :
    IntegrableOn (fun p : ℝ×ℝ => sampledKernel alpha (meshSample n) p.1 p.2) primeRectangle := by
  apply Measure.integrableOn_of_bounded
    (ne_of_lt (isCompact_Icc.measure_lt_top : volume primeRectangle<⊤))
    (mesh_kernel_measurable alpha n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet primeRectangle)] with p hp
  exact mesh_kernel_rectangle_bound ha n hp

theorem mesh_inner_intervalIntegrable {alpha : ℝ} (ha : 2≤alpha) (n : ℕ) {u : ℝ}
    (hu : u ∈ Icc corner a2) :
    IntervalIntegrable (sampledKernel alpha (meshSample n) u) volume (badLower u) a2 := by
  have hm := (mesh_kernel_measurable alpha n).comp (measurable_const.prodMk measurable_id)
  have hi : IntegrableOn (sampledKernel alpha (meshSample n) u) (Icc (badLower u) a2) := by
    apply Measure.integrableOn_of_bounded
      (ne_of_lt (isCompact_Icc.measure_lt_top : volume (Icc (badLower u) a2)<⊤))
      hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact mesh_kernel_rectangle_bound ha n (bad_support_in_primeRectangle hu hv)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (bad_fibre_geometry hu).2.2.1).mpr hi

private def jointKernel (alpha : ℝ) (n : ℕ) : ℝ×ℝ → ℝ :=
  badClosed.indicator (fun p => sampledKernel alpha (meshSample n) p.1 p.2)

private theorem jointKernel_integrable {alpha : ℝ} (ha : 2≤alpha) (n : ℕ) :
    Integrable (jointKernel alpha n) :=
  ((mesh_kernel_integrableOn_rectangle ha n).mono_set inter_subset_left).integrable_indicator
    badClosed_measurable

private theorem jointKernel_fibre (alpha : ℝ) (n : ℕ) {u : ℝ}
    (hu : u ∈ Icc corner a2) :
    (∫ v : ℝ,jointKernel alpha n (u,v))=
      ∫ v in badLower u..a2,sampledKernel alpha (meshSample n) u v := by
  have he (v : ℝ) : jointKernel alpha n (u,v)=
      (Icc (badLower u) a2).indicator (sampledKernel alpha (meshSample n) u) v := by
    by_cases hv : v ∈ Icc (badLower u) a2
    · have hp := (badClosed_dictionary u v).mpr ⟨hu,hv⟩
      simp only [jointKernel,indicator_of_mem hp,indicator_of_mem hv]
    · have hp : (u,v) ∉ badClosed := fun hp => hv ((badClosed_dictionary u v).mp hp).2
      simp only [jointKernel,indicator_of_notMem hp,indicator_of_notMem hv]
  simp_rw [he]
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (bad_fibre_geometry hu).2.2.1]

theorem mesh_outer_intervalIntegrable {alpha : ℝ} (ha : 2≤alpha) (n : ℕ) :
    IntervalIntegrable (fun u => ∫ v in badLower u..a2,
      sampledKernel alpha (meshSample n) u v) volume corner a2 := by
  have h := (jointKernel_integrable ha n).integral_prod_left.intervalIntegrable
    (a:=corner) (b:=a2)
  apply h.congr
  intro u hu
  rw [uIoc_of_le (by norm_num [corner,a2])] at hu
  exact jointKernel_fibre alpha n ⟨hu.1.le,hu.2⟩

/-- The finite sampler actually PRODUCES every analytic obligation of
the previously proved actual integral-error theorem. -/
theorem finite_mesh_admissible {alpha : ℝ} (ha : 2≤alpha) (n : ℕ) :
    AdmissibleSample alpha (meshError n) (meshSample n) where
  nonnegative := meshError_nonnegative n
  coordinates := by
    intro u hu v hv
    exact meshSample_coordinates n (bad_support_in_primeRectangle hu hv)
  inner := fun u hu => mesh_inner_intervalIntegrable ha n hu
  outer := mesh_outer_intervalIntegrable ha n

end
end ImbalancedChen.P2SeedOmegaMeshAdmissibility
