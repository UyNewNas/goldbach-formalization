import ImbalancedChen.Part3ActualKPolarizedFourier
import ImbalancedChen.Part3ActualKZeroPairEnergy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED (2026-10-24).  Polarized cross energy for two
physical q amplitudes and the genuine K₀(q+r) pairing. Absolute
integrability of the mixed q-r-u product is proved before Fubini.
-/

namespace ImbalancedChen.Part3.ActualKPolarizedKZero20261024z
noncomputable section

open Classical Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ImaginaryOrderKBesselSourceOnly
open ActualCommonHeightKGramSourceOnly (kTestTransform)
open ActualKTransformFourier20261024z
open ActualKFullHeightEnergy20261024z
open ActualKPolarizedFourier20261024z

variable {ι : Type*}

def crossLaplace (a b : ℝ → ℂ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  a p.1.1 * Complex.conj (b p.1.2) *
    (Real.exp (-(p.1.1 + p.1.2) * Real.cosh p.2) : ℂ)

def crossKZero (a b : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  a p.1 * Complex.conj (b p.2) *
    (imaginaryOrderK 0 (p.1 + p.2) : ℂ)

private theorem crossLaplace_norm_le (P : PacketData ι) (a b : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (hb : PhysicalAmplitude P b)
    (p : (ℝ × ℝ) × ℝ) :
    ‖crossLaplace a b p‖ ≤
      (‖a p.1.1‖ * ‖b p.1.2‖) *
        Real.exp (-(P.Y0 / 16) * p.2) := by
  by_cases hq : p.1.1 ∈ P.region
  · by_cases hr : p.1.2 ∈ P.region
    · have hY : 0 < P.Y0 / 8 := by
        have := P.Y0_pos
        positivity
      have hsum : P.Y0 / 8 ≤ p.1.1 + p.1.2 := by
        have hqlo : P.Y0 / 16 ≤ p.1.1 := hq.1
        have hrlo : P.Y0 / 16 ≤ p.1.2 := hr.1
        linarith
      have hk := kIntegrand_norm_le hY hsum 0 p.2
      have hexp : Real.exp (-(p.1.1 + p.1.2) * Real.cosh p.2) ≤
          Real.exp (-(P.Y0 / 16) * p.2) := by
        simpa only [kIntegrand, zero_mul, Real.cos_zero, mul_one,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          show P.Y0 / 8 / 2 = P.Y0 / 16 by ring] using hk
      simpa only [crossLaplace, norm_mul, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), mul_assoc] using
        (mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    · simp [crossLaplace, hb.2 p.1.2 hr]
  · simp [crossLaplace, ha.2 p.1.1 hq]

theorem crossLaplace_integrable (P : PacketData ι) (a b : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (hb : PhysicalAmplitude P b) :
    Integrable (crossLaplace a b)
      ((volume.prod volume).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hq : Integrable (fun q : ℝ => ‖a q‖) := (amplitude_integrable P a ha).norm
  have hr : Integrable (fun r : ℝ => ‖b r‖) := (amplitude_integrable P b hb).norm
  have hqr : Integrable (fun p : ℝ × ℝ => ‖a p.1‖ * ‖b p.2‖)
      (volume.prod volume) := hq.mul_prod hr
  have hY : 0 < P.Y0 / 8 := by
    have := P.Y0_pos
    positivity
  have hu : Integrable (fun u : ℝ => Real.exp (-(P.Y0 / 16) * u))
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [show -(P.Y0 / 8 / 2) = -(P.Y0 / 16) by ring] using
      (exponential_majorant_integrable (a := P.Y0 / 8) hY)
  have hmaj : Integrable (fun p : (ℝ × ℝ) × ℝ =>
      (‖a p.1.1‖ * ‖b p.1.2‖) * Real.exp (-(P.Y0 / 16) * p.2))
      ((volume.prod volume).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hqr.mul_prod hu
  have hc : Continuous (crossLaplace a b) := by
    unfold crossLaplace
    have haC : Continuous a := ha.1
    have hbC : Continuous b := hb.1
    fun_prop
  exact hmaj.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (crossLaplace_norm_le P a b ha hb))

private theorem crossLaplace_eq_factors (a b : ℝ → ℂ) (q r u : ℝ) :
    crossLaplace a b ((q, r), u) =
      (a q * (Real.exp (-q * Real.cosh u) : ℂ)) *
        Complex.conj (b r * (Real.exp (-r * Real.cosh u) : ℂ)) := by
  have he : Real.exp (-q * Real.cosh u) * Real.exp (-r * Real.cosh u) =
      Real.exp (-(q + r) * Real.cosh u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcast : (Real.exp (-q * Real.cosh u) : ℂ) *
      (Real.exp (-r * Real.cosh u) : ℂ) =
      (Real.exp (-(q + r) * Real.cosh u) : ℂ) := by
    rw [← Complex.ofReal_mul, he]
  simp only [crossLaplace, map_mul, Complex.conj_ofReal]
  rw [← hcast]
  ring

private theorem crossLaplace_qr_integral (P : PacketData ι)
    (a b : ℝ → ℂ) (u : ℝ) :
    (∫ p : ℝ × ℝ, crossLaplace a b (p, u) ∂(volume.prod volume)) =
      qLaplaceProfile P a u * Complex.conj (qLaplaceProfile P b u) := by
  have he : (fun p : ℝ × ℝ => crossLaplace a b (p, u)) =
      (fun p : ℝ × ℝ =>
        (a p.1 * (Real.exp (-p.1 * Real.cosh u) : ℂ)) *
          Complex.conj (b p.2 *
            (Real.exp (-p.2 * Real.cosh u) : ℂ))) := by
    funext p
    exact crossLaplace_eq_factors a b p.1 p.2 u
  rw [he, integral_prod_mul, integral_conj]
  rfl

private theorem crossLaplace_u_integral (a b : ℝ → ℂ) (p : ℝ × ℝ) :
    (∫ u in Ioi (0 : ℝ), crossLaplace a b (p, u)) = crossKZero a b p := by
  have he (u : ℝ) : crossLaplace a b (p, u) =
      (a p.1 * Complex.conj (b p.2)) *
        (kIntegrand 0 (p.1 + p.2) u : ℂ) := by
    simp [crossLaplace, kIntegrand]
  simp_rw [he]
  rw [integral_const_mul, integral_complex_ofReal]
  rfl

theorem crossKZero_integrable (P : PacketData ι) (a b : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (hb : PhysicalAmplitude P b) :
    Integrable (crossKZero a b) (volume.prod volume) := by
  have hf := (crossLaplace_integrable P a b ha hb).integral_prod_left
  simpa only [crossLaplace_u_integral] using hf

private theorem crossKZero_zero_off (P : PacketData ι) (a b : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (hb : PhysicalAmplitude P b)
    (p : ℝ × ℝ) (hp : p ∉ P.region ×ˢ P.region) :
    crossKZero a b p = 0 := by
  have hp' : p.1 ∉ P.region ∨ p.2 ∉ P.region := by
    simpa only [Set.mem_prod, not_and_or] using hp
  rcases hp' with hq | hr
  · simp [crossKZero, ha.2 p.1 hq]
  · simp [crossKZero, hb.2 p.2 hr]

theorem crossKZero_integral_eq_region (P : PacketData ι) (a b : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (hb : PhysicalAmplitude P b) :
    (∫ p : ℝ × ℝ, crossKZero a b p ∂(volume.prod volume)) =
      ∫ q in P.region, ∫ r in P.region,
        a q * Complex.conj (b r) *
          (imaginaryOrderK 0 (q + r) : ℂ) := by
  have hs :
      (∫ p : ℝ × ℝ, crossKZero a b p ∂(volume.prod volume)) =
        ∫ p in P.region ×ˢ P.region, crossKZero a b p
          ∂(volume.prod volume) := by
    rw [← setIntegral_univ]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      MeasurableSet.univ (subset_univ (P.region ×ˢ P.region))
      (fun p hp => crossKZero_zero_off P a b ha hb p
        (notMem_of_mem_sdiff hp))
  rw [hs]
  change ∫ p : ℝ × ℝ, crossKZero a b p
    ∂((volume.prod volume).restrict (P.region ×ˢ P.region)) = _
  rw [← Measure.prod_restrict P.region P.region]
  have hi : Integrable (crossKZero a b)
      ((volume.restrict P.region).prod (volume.restrict P.region)) := by
    simpa only [Measure.prod_restrict] using
      (crossKZero_integrable P a b ha hb).integrableOn
  rw [integral_prod _ hi]
  rfl

theorem positive_profile_cross_eq_KZero (P : PacketData ι) (a b : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (hb : PhysicalAmplitude P b) :
    (∫ u in Ioi (0 : ℝ), qLaplaceProfile P a u *
      Complex.conj (qLaplaceProfile P b u)) =
      ∫ p : ℝ × ℝ, crossKZero a b p ∂(volume.prod volume) := by
  have hf := crossLaplace_integrable P a b ha hb
  calc
    _ = ∫ u in Ioi (0 : ℝ), ∫ p : ℝ × ℝ,
          crossLaplace a b (p, u) ∂(volume.prod volume) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      exact (crossLaplace_qr_integral P a b u).symm
    _ = ∫ p : ℝ × ℝ, ∫ u in Ioi (0 : ℝ), crossLaplace a b (p, u) :=
      (integral_integral_swap hf).symm
    _ = _ := by simp only [crossLaplace_u_integral]

private theorem profile_cross_integrable (P : PacketData ι) (a b : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (hb : PhysicalAmplitude P b) :
    Integrable (fun u : ℝ => qLaplaceProfile P a u *
      Complex.conj (qLaplaceProfile P b u)) := by
  have hY : 0 < P.Y0 / 16 := by
    have := P.Y0_pos
    positivity
  have hmaj : Integrable (fun u : ℝ =>
      ((∫ q : ℝ, ‖a q‖) * (∫ r : ℝ, ‖b r‖)) *
        Real.exp (-(P.Y0 / 16) * |u|)) :=
    (exp_neg_abs_integrable hY).const_mul _
  have hc : Continuous (fun u : ℝ => qLaplaceProfile P a u *
      Complex.conj (qLaplaceProfile P b u)) := by
    exact (qLaplaceProfile_continuous P a ha).mul
      (Complex.continuous_conj.comp (qLaplaceProfile_continuous P b hb))
  apply hmaj.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  have hA := qLaplaceProfile_norm_le P a ha u
  have hB := qLaplaceProfile_norm_le P b hb u
  have hCA : 0 ≤ ∫ q : ℝ, ‖a q‖ := integral_nonneg (fun q => norm_nonneg _)
  have hCB : 0 ≤ ∫ r : ℝ, ‖b r‖ := integral_nonneg (fun r => norm_nonneg _)
  have hE : 0 ≤ Real.exp (-(P.Y0 / 32) * |u|) := (Real.exp_pos _).le
  calc
    ‖qLaplaceProfile P a u * Complex.conj (qLaplaceProfile P b u)‖ =
        ‖qLaplaceProfile P a u‖ * ‖qLaplaceProfile P b u‖ := by
      simp only [norm_mul, Complex.norm_conj]
    _ ≤ ((∫ q : ℝ, ‖a q‖) * Real.exp (-(P.Y0 / 32) * |u|)) *
        ((∫ r : ℝ, ‖b r‖) * Real.exp (-(P.Y0 / 32) * |u|)) := by
      exact mul_le_mul hA hB (norm_nonneg _)
        (mul_nonneg hCA hE)
    _ = ((∫ q : ℝ, ‖a q‖) * (∫ r : ℝ, ‖b r‖)) *
        (Real.exp (-(P.Y0 / 32) * |u|) *
          Real.exp (-(P.Y0 / 32) * |u|)) := by ring
    _ = ((∫ q : ℝ, ‖a q‖) * (∫ r : ℝ, ‖b r‖)) *
        Real.exp (-(P.Y0 / 16) * |u|) := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem even_profile_cross_integral (P : PacketData ι) (a b : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (hb : PhysicalAmplitude P b) :
    (∫ u : ℝ, qLaplaceProfile P a u *
      Complex.conj (qLaplaceProfile P b u)) =
      2 * ∫ u in Ioi (0 : ℝ), qLaplaceProfile P a u *
        Complex.conj (qLaplaceProfile P b u) := by
  let F : ℝ → ℂ := fun u => qLaplaceProfile P a u *
    Complex.conj (qLaplaceProfile P b u)
  have hF : Integrable F := profile_cross_integrable P a b ha hb
  have hleft : IntegrableOn F (Iic (0 : ℝ)) := hF.integrableOn
  have hright : IntegrableOn F (Ioi (0 : ℝ)) := hF.integrableOn
  have hreflect : (∫ u in Iic (0 : ℝ), F u) =
      ∫ u in Ioi (0 : ℝ), F (-u) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi (0 : ℝ) F).symm
  calc
    (∫ u : ℝ, F u) =
        (∫ u in Iic (0 : ℝ), F u) + ∫ u in Ioi (0 : ℝ), F u :=
      (integral_Iic_add_Ioi hleft hright).symm
    _ = (∫ u in Ioi (0 : ℝ), F (-u)) +
          ∫ u in Ioi (0 : ℝ), F u := by rw [hreflect]
    _ = 2 * ∫ u in Ioi (0 : ℝ), F u := by
      have he : (fun u : ℝ => F (-u)) = F := by
        funext u
        simp only [F, qLaplaceProfile_even]
      rw [he]
      ring

theorem amplitudeK_full_height_cross_KZero (P : PacketData ι) (a b : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (hb : PhysicalAmplitude P b) :
    (∫ t : ℝ, amplitudeK P a t * Complex.conj (amplitudeK P b t)) =
      ((Real.pi / 2 : ℝ) : ℂ) *
        ∫ p : ℝ × ℝ, crossKZero a b p ∂(volume.prod volume) := by
  calc
    _ = ((Real.pi / 4 : ℝ) : ℂ) *
        ∫ u : ℝ, qLaplaceProfile P a u *
          Complex.conj (qLaplaceProfile P b u) :=
      amplitudeK_full_height_cross_fourier P a b ha hb
    _ = ((Real.pi / 4 : ℝ) : ℂ) *
        (2 * ∫ u in Ioi (0 : ℝ), qLaplaceProfile P a u *
          Complex.conj (qLaplaceProfile P b u)) := by
      rw [even_profile_cross_integral P a b ha hb]
    _ = _ := by
      rw [positive_profile_cross_eq_KZero P a b ha hb]
      ring

theorem amplitudeK_full_height_cross_regionKZero (P : PacketData ι)
    (a b : ℝ → ℂ) (ha : PhysicalAmplitude P a)
    (hb : PhysicalAmplitude P b) :
    (∫ t : ℝ, amplitudeK P a t * Complex.conj (amplitudeK P b t)) =
      ((Real.pi / 2 : ℝ) : ℂ) *
        ∫ q in P.region, ∫ r in P.region,
          a q * Complex.conj (b r) *
            (imaginaryOrderK 0 (q + r) : ℂ) := by
  rw [amplitudeK_full_height_cross_KZero P a b ha hb,
    crossKZero_integral_eq_region P a b ha hb]

theorem kTestTransform_full_height_cross_regionKZero (P : PacketData ι)
    (k l : D4 → ℤ) :
    (∫ t : ℝ, kTestTransform P k t *
      Complex.conj (kTestTransform P l t)) =
      ((Real.pi / 2 : ℝ) : ℂ) *
        ∫ q in P.region, ∫ r in P.region,
          (spectralTest k P.Y0 q / (q : ℂ)) *
            Complex.conj (spectralTest l P.Y0 r / (r : ℂ)) *
              (imaginaryOrderK 0 (q + r) : ℂ) := by
  have h := amplitudeK_full_height_cross_regionKZero P
    (actualKAmplitude P k) (actualKAmplitude P l)
    (actualKAmplitude_physical P k) (actualKAmplitude_physical P l)
  simp_rw [← kTestTransform_eq_amplitudeK, actualKAmplitude_eq] at h
  exact h

end
end ImbalancedChen.Part3.ActualKPolarizedKZero20261024z
