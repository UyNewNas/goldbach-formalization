import ImbalancedChen.P2SeedOmegaGlobalEnvelope
import ImbalancedChen.P2SeedOmegaBadCellSemantics

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original bad Gamma5 cost is now bounded for EVERY alpha>=2, using
the actual analytic global cap. There is no alpha upper cutoff, no cell
array, no presumed pointwise/integral cap, and no new seed premise.
Continuity pays both integrals with the moving original max(u,1-2u)
lower endpoint; the positive envelope integrates to the literal log mass
consumed by certify_second_seed_omega_envelope.py.
-/

namespace ImbalancedChen.P2SeedOmegaBadGlobalCost
noncomputable section
open Set MeasureTheory
open scoped Interval
open P2SeedOmegaLiteralFibre
open P2SeedOmegaGlobalEnvelope
open P2SeedOmegaLiteralFunctional (badMassLog)
open P2SeedOmegaBadCellSemantics (actualBadKernel)

def envelopeCoefficient : ℝ := K*omegaCap*s0/4
def actualBadCost (alpha : ℝ) : ℝ :=
  ∫ u in corner..a2,∫ v in badLower u..a2,actualBadKernel alpha u v

theorem actual_bad_kernel_global_upper {alpha u v : ℝ} (ha : 2≤alpha)
    (hu : u ∈ Icc corner a2) (hv : v ∈ Icc (badLower u) a2) :
    actualBadKernel alpha u v≤envelopeCoefficient*roughPairKernel u v := by
  have hg := bad_closed_geometry hu hv
  have harg := bad_argument_lower ha hu.2 hv.2
  have hω := actual_buchstab_global_cap
    (by linarith only [harg] : 2≤badArgument alpha u v)
  have hcoef : (0:ℝ)≤K*s0/4 := by norm_num [K,s0]
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hω hcoef) (mul_pos hg.1 hg.2.1).le
  convert h using 1 <;> dsimp [actualBadKernel,envelopeCoefficient,roughPairKernel] <;> ring

private def safeActual (alpha : ℝ) (p : ℝ×ℝ) : ℝ :=
  actualBadKernel alpha (max a0 p.1) (max a0 p.2)
private def safeEnvelope (p : ℝ×ℝ) : ℝ :=
  envelopeCoefficient*roughPairKernel (max a0 p.1) (max a0 p.2)

private theorem safeActual_continuous (alpha : ℝ) : Continuous (safeActual alpha) := by
  have hu : Continuous (fun p : ℝ×ℝ => max a0 p.1) := continuous_const.max continuous_fst
  have hv : Continuous (fun p : ℝ×ℝ => max a0 p.2) := continuous_const.max continuous_snd
  have ha0 : 0<a0 := by norm_num [a0]
  have harg : Continuous (fun p : ℝ×ℝ => badArgument alpha
      (max a0 p.1) (max a0 p.2)) := continuous_const.mul ((continuous_const.sub hu).sub hv)
  exact (continuous_const.mul (LiLiuPrereqBuchstab.continuous_buchstab.comp harg)).div
    (hu.mul hv) (fun p => (mul_pos (ha0.trans_le (le_max_left _ _))
      (ha0.trans_le (le_max_left _ _))).ne')

private theorem safeEnvelope_continuous : Continuous safeEnvelope := by
  have hu : Continuous (fun p : ℝ×ℝ => max a0 p.1) := continuous_const.max continuous_fst
  have hv : Continuous (fun p : ℝ×ℝ => max a0 p.2) := continuous_const.max continuous_snd
  have ha0 : 0<a0 := by norm_num [a0]
  exact continuous_const.mul (continuous_const.div (hu.mul hv)
    (fun p => (mul_pos (ha0.trans_le (le_max_left _ _))
      (ha0.trans_le (le_max_left _ _))).ne'))

private theorem unclamp_on_bad {u v : ℝ}
    (hu : u ∈ Icc corner a2) (hv : v ∈ Icc (badLower u) a2) :
    max a0 u=u ∧ max a0 v=v := by
  have h0 : a0≤u := (by norm_num [a0,corner] : a0≤corner).trans hu.1
  have h1 : u≤v := (le_max_left u (1-2*u)).trans hv.1
  exact ⟨max_eq_right h0,max_eq_right (h0.trans h1)⟩

private theorem continuous_moving_inner (F : ℝ×ℝ → ℝ) (hF : Continuous F) :
    Continuous (fun u : ℝ => ∫ v in badLower u..a2,F (u,v)) := by
  have hLower : Continuous badLower := by unfold badLower; fun_prop
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (a₀:=a2) (f:=fun u v => F (u,v)) hF hLower
  have he : (fun u : ℝ => ∫ v in badLower u..a2,F (u,v))=
      (fun u : ℝ => -(∫ v in a2..badLower u,F (u,v))) := by
    funext u
    exact intervalIntegral.integral_symm
  rw [he]
  exact h.neg

/-- Both actual iterated integrals are genuinely integrable, including
the moving lower boundary and its kink at one third. -/
theorem actual_bad_outer_intervalIntegrable (alpha : ℝ) :
    IntervalIntegrable (fun u => ∫ v in badLower u..a2,
      actualBadKernel alpha u v) volume corner a2 := by
  have h := (continuous_moving_inner _ (safeActual_continuous alpha)).intervalIntegrable corner a2
  apply h.congr
  intro u hu
  rw [uIoc_of_le (by norm_num [corner,a2])] at hu
  apply intervalIntegral.integral_congr
  intro v hv
  have hU : u ∈ Icc corner a2 := ⟨hu.1.le,hu.2⟩
  have hg := bad_fibre_geometry hU
  rw [uIcc_of_le hg.2.2.1] at hv
  obtain ⟨huc,hvc⟩ := unclamp_on_bad hU hv
  simp only [safeActual,huc,hvc]

theorem actual_bad_inner_intervalIntegrable (alpha : ℝ) {u : ℝ}
    (hu : u ∈ Icc corner a2) :
    IntervalIntegrable (actualBadKernel alpha u) volume (badLower u) a2 := by
  have h := ((safeActual_continuous alpha).comp
    (continuous_const.prodMk continuous_id)).intervalIntegrable (badLower u) a2
  apply h.congr
  intro v hv
  rw [uIoc_of_le (bad_fibre_geometry hu).2.2.1] at hv
  obtain ⟨huc,hvc⟩ := unclamp_on_bad hu ⟨hv.1.le,hv.2⟩
  simp only [safeActual,huc,hvc]

/-- The exact original real envelope cost, valid uniformly over the
ENTIRE alpha>=2 tail. It replaces the earlier finite-alpha-strip input. -/
theorem actual_bad_cost_le_original_mass {alpha : ℝ} (ha : 2≤alpha) :
    actualBadCost alpha≤envelopeCoefficient*badMassLog := by
  have huLR : corner≤a2 := by norm_num [corner,a2]
  have hA := continuous_moving_inner _ (safeActual_continuous alpha)
  have hE := continuous_moving_inner _ safeEnvelope_continuous
  have hinner : ∀ u ∈ Icc corner a2,
      (∫ v in badLower u..a2,safeActual alpha (u,v))≤
        (∫ v in badLower u..a2,safeEnvelope (u,v)) := by
    intro u hu
    have hvLR := (bad_fibre_geometry hu).2.2.1
    apply intervalIntegral.integral_mono_on hvLR
      (((safeActual_continuous alpha).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      ((safeEnvelope_continuous.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    intro v hv
    obtain ⟨huc,hvc⟩ := unclamp_on_bad hu hv
    simp only [safeActual,safeEnvelope,huc,hvc]
    exact actual_bad_kernel_global_upper ha hu hv
  have houter := intervalIntegral.integral_mono_on huLR
    (hA.intervalIntegrable corner a2) (hE.intervalIntegrable corner a2) hinner
  have heA : (∫ u in corner..a2,∫ v in badLower u..a2,safeActual alpha (u,v))=
      actualBadCost alpha := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le huLR] at hu
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (bad_fibre_geometry hu).2.2.1] at hv
    obtain ⟨huc,hvc⟩ := unclamp_on_bad hu hv
    simp only [safeActual,huc,hvc,actualBadCost]
  have heE : (∫ u in corner..a2,∫ v in badLower u..a2,safeEnvelope (u,v))=
      envelopeCoefficient*badMassLog := by
    calc
      _ = ∫ u in corner..a2,∫ v in badLower u..a2,
          envelopeCoefficient*roughPairKernel u v := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le huLR] at hu
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le (bad_fibre_geometry hu).2.2.1] at hv
        obtain ⟨huc,hvc⟩ := unclamp_on_bad hu hv
        simp only [safeEnvelope,huc,hvc]
      _ = envelopeCoefficient*(∫ u in corner..a2,∫ v in badLower u..a2,
          roughPairKernel u v) := by simp_rw [intervalIntegral.integral_const_mul]
      _ = envelopeCoefficient*badMassLog := by
        rw [bad_rough_partition]
        exact congrArg (fun z => envelopeCoefficient*z)
          P2SeedOmegaLiteralFunctional.badRoughDouble_eq_original_log
  rw [heA,heE] at houter
  exact houter

end
end ImbalancedChen.P2SeedOmegaBadGlobalCost
