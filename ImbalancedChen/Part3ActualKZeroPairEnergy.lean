import ImbalancedChen.Part3ActualKFullHeightEnergy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED (2026-10-24). The q-r-u product below is absolutely
integrable from the same physical lower endpoint q,r >= Y0/16. Fubini gives
the literal K_0(q+r) kernel of the full-height Fourier energy. This is a
Lebesgue-height identity, not an automorphic spectral Plancherel formula.
-/

namespace ImbalancedChen.Part3.ActualKZeroPairEnergy20261024z
noncomputable section

open Classical Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ImaginaryOrderKBesselSourceOnly
open ActualCommonHeightKGramSourceOnly (kTestTransform)
open ActualKTransformFourier20261024z
open ActualKFullHeightEnergy20261024z

variable {ι : Type*}

/-- The real even Laplace product before taking its positive-u integral. -/
def qPairLaplace (a : ℝ → ℂ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  a p.1.1 * Complex.conj (a p.1.2) *
    (Real.exp (-(p.1.1 + p.1.2) * Real.cosh p.2) : ℂ)

def qPairKZero (a : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  a p.1 * Complex.conj (a p.2) *
    (imaginaryOrderK 0 (p.1 + p.2) : ℂ)

private theorem qPairLaplace_norm_le (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (p : (ℝ × ℝ) × ℝ) :
    ‖qPairLaplace a p‖ ≤
      (‖a p.1.1‖ * ‖a p.1.2‖) *
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
      simpa only [qPairLaplace, norm_mul, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), mul_assoc] using
        (mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    · simp [qPairLaplace, ha.2 p.1.2 hr]
  · simp [qPairLaplace, ha.2 p.1.1 hq]

theorem qPairLaplace_integrable (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    Integrable (qPairLaplace a)
      ((volume.prod volume).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hq : Integrable (fun q : ℝ => ‖a q‖) := (amplitude_integrable P a ha).norm
  have hqq : Integrable (fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖)
      (volume.prod volume) := hq.mul_prod hq
  have hY : 0 < P.Y0 / 8 := by
    have := P.Y0_pos
    positivity
  have hu : Integrable (fun u : ℝ => Real.exp (-(P.Y0 / 16) * u))
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [show -(P.Y0 / 8 / 2) = -(P.Y0 / 16) by ring] using
      (exponential_majorant_integrable (a := P.Y0 / 8) hY)
  have hmaj : Integrable (fun p : (ℝ × ℝ) × ℝ =>
      (‖a p.1.1‖ * ‖a p.1.2‖) * Real.exp (-(P.Y0 / 16) * p.2))
      ((volume.prod volume).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hqq.mul_prod hu
  have hc : Continuous (qPairLaplace a) := by
    unfold qPairLaplace
    have haC : Continuous a := ha.1
    fun_prop
  exact hmaj.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (qPairLaplace_norm_le P a ha))

private theorem qPairLaplace_eq_factors (a : ℝ → ℂ) (q r u : ℝ) :
    qPairLaplace a ((q, r), u) =
      (a q * (Real.exp (-q * Real.cosh u) : ℂ)) *
        Complex.conj (a r * (Real.exp (-r * Real.cosh u) : ℂ)) := by
  have he : Real.exp (-q * Real.cosh u) * Real.exp (-r * Real.cosh u) =
      Real.exp (-(q + r) * Real.cosh u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcast : (Real.exp (-q * Real.cosh u) : ℂ) *
      (Real.exp (-r * Real.cosh u) : ℂ) =
      (Real.exp (-(q + r) * Real.cosh u) : ℂ) := by
    rw [← Complex.ofReal_mul, he]
  simp only [qPairLaplace, map_mul, Complex.conj_ofReal]
  rw [← hcast]
  ring

private theorem qPairLaplace_qr_integral (P : PacketData ι) (a : ℝ → ℂ)
    (u : ℝ) :
    (∫ p : ℝ × ℝ, qPairLaplace a (p, u) ∂(volume.prod volume)) =
      (‖qLaplaceProfile P a u‖ ^ 2 : ℂ) := by
  have he : (fun p : ℝ × ℝ => qPairLaplace a (p, u)) =
      (fun p : ℝ × ℝ =>
        (a p.1 * (Real.exp (-p.1 * Real.cosh u) : ℂ)) *
          Complex.conj (a p.2 *
            (Real.exp (-p.2 * Real.cosh u) : ℂ))) := by
    funext p
    exact qPairLaplace_eq_factors a p.1 p.2 u
  rw [he, integral_prod_mul, integral_conj]
  change qLaplaceProfile P a u * Complex.conj (qLaplaceProfile P a u) = _
  exact Complex.mul_conj' _

private theorem qPairLaplace_u_integral (a : ℝ → ℂ) (p : ℝ × ℝ) :
    (∫ u in Ioi (0 : ℝ), qPairLaplace a (p, u)) = qPairKZero a p := by
  have he (u : ℝ) : qPairLaplace a (p, u) =
      (a p.1 * Complex.conj (a p.2)) *
        (kIntegrand 0 (p.1 + p.2) u : ℂ) := by
    simp [qPairLaplace, kIntegrand]
  simp_rw [he]
  rw [integral_const_mul, integral_complex_ofReal]
  rfl

/-- The positive half-line norm-square is exactly the double physical-q
K_0 kernel integral. Its absolute convergence follows from the displayed
three-variable product majorant. -/
theorem positive_profile_energy_eq_pairKZero (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    (∫ u in Ioi (0 : ℝ), ‖qLaplaceProfile P a u‖ ^ 2) =
      Complex.re (∫ p : ℝ × ℝ, qPairKZero a p ∂(volume.prod volume)) := by
  have hf := qPairLaplace_integrable P a ha
  have hcomplex :
      (∫ u in Ioi (0 : ℝ), (‖qLaplaceProfile P a u‖ ^ 2 : ℂ)) =
        ∫ p : ℝ × ℝ, qPairKZero a p ∂(volume.prod volume) := by
    calc
      _ = ∫ u in Ioi (0 : ℝ), ∫ p : ℝ × ℝ,
            qPairLaplace a (p, u) ∂(volume.prod volume) := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro u
        exact (qPairLaplace_qr_integral P a u).symm
      _ = ∫ p : ℝ × ℝ, ∫ u in Ioi (0 : ℝ), qPairLaplace a (p, u) :=
        (integral_integral_swap hf).symm
      _ = _ := by simp only [qPairLaplace_u_integral]
  rw [integral_complex_ofReal] at hcomplex
  have hr := congrArg Complex.re hcomplex
  simpa using hr

theorem qPairKZero_integrable (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    Integrable (qPairKZero a) (volume.prod volume) := by
  have hf := (qPairLaplace_integrable P a ha).integral_prod_left
  simpa only [qPairLaplace_u_integral] using hf

private theorem qPairKZero_zero_off (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (p : ℝ × ℝ)
    (hp : p ∉ P.region ×ˢ P.region) : qPairKZero a p = 0 := by
  have hp' : p.1 ∉ P.region ∨ p.2 ∉ P.region := by
    simpa only [Set.mem_prod, not_and_or] using hp
  rcases hp' with hq | hr
  · simp [qPairKZero, ha.2 p.1 hq]
  · simp [qPairKZero, ha.2 p.2 hr]

/-- The unrestricted q-r integral is exactly the two physical-region
integrals, with no artificial cutoff inserted into the kernel. -/
theorem qPairKZero_integral_eq_region (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    (∫ p : ℝ × ℝ, qPairKZero a p ∂(volume.prod volume)) =
      ∫ q in P.region, ∫ r in P.region,
        a q * Complex.conj (a r) *
          (imaginaryOrderK 0 (q + r) : ℂ) := by
  have hs :
      (∫ p : ℝ × ℝ, qPairKZero a p ∂(volume.prod volume)) =
        ∫ p in P.region ×ˢ P.region, qPairKZero a p
          ∂(volume.prod volume) := by
    rw [← setIntegral_univ]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      MeasurableSet.univ (subset_univ (P.region ×ˢ P.region))
      (fun p hp => qPairKZero_zero_off P a ha p
        (notMem_of_mem_sdiff hp))
  rw [hs]
  change ∫ p : ℝ × ℝ, qPairKZero a p
    ∂((volume.prod volume).restrict (P.region ×ˢ P.region)) = _
  rw [← Measure.prod_restrict P.region P.region]
  have hi : Integrable (qPairKZero a)
      ((volume.restrict P.region).prod (volume.restrict P.region)) := by
    simpa only [Measure.prod_restrict] using
      (qPairKZero_integrable P a ha).integrableOn
  rw [integral_prod _ hi]
  rfl

private theorem even_profile_norm_sq_integral (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    (∫ u : ℝ, ‖qLaplaceProfile P a u‖ ^ 2) =
      2 * ∫ u in Ioi (0 : ℝ), ‖qLaplaceProfile P a u‖ ^ 2 := by
  let F : ℝ → ℝ := fun u => ‖qLaplaceProfile P a u‖ ^ 2
  have hF : Integrable F := qLaplaceProfile_norm_sq_integrable P a ha
  have hleft : IntegrableOn F (Iic (0 : ℝ)) := hF.integrableOn
  have hright : IntegrableOn F (Ioi (0 : ℝ)) := hF.integrableOn
  have hreflect : (∫ u in Iic (0 : ℝ), F u) =
      ∫ u in Ioi (0 : ℝ), F (-u) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi (0 : ℝ) F).symm
  calc
    (∫ u : ℝ, ‖qLaplaceProfile P a u‖ ^ 2) =
        (∫ u in Iic (0 : ℝ), F u) + ∫ u in Ioi (0 : ℝ), F u :=
      (integral_Iic_add_Ioi hleft hright).symm
    _ = (∫ u in Ioi (0 : ℝ), F (-u)) +
          ∫ u in Ioi (0 : ℝ), F u := by rw [hreflect]
    _ = 2 * ∫ u in Ioi (0 : ℝ), ‖qLaplaceProfile P a u‖ ^ 2 := by
      have he : (fun u : ℝ => F (-u)) = F := by
        funext u
        simp only [F, qLaplaceProfile_even]
      rw [he]
      ring

theorem amplitudeK_full_height_pairKZero (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    (∫ t : ℝ, ‖amplitudeK P a t‖ ^ 2) =
      (Real.pi / 2) *
        Complex.re (∫ p : ℝ × ℝ, qPairKZero a p ∂(volume.prod volume)) := by
  calc
    _ = (Real.pi / 4) * ∫ u : ℝ, ‖qLaplaceProfile P a u‖ ^ 2 :=
      amplitudeK_full_height_energy P a ha
    _ = (Real.pi / 4) *
        (2 * ∫ u in Ioi (0 : ℝ), ‖qLaplaceProfile P a u‖ ^ 2) := by
      rw [even_profile_norm_sq_integral P a ha]
    _ = _ := by
      rw [positive_profile_energy_eq_pairKZero P a ha]
      ring

theorem amplitudeK_full_height_regionKZero (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    (∫ t : ℝ, ‖amplitudeK P a t‖ ^ 2) =
      (Real.pi / 2) * Complex.re
        (∫ q in P.region, ∫ r in P.region,
          a q * Complex.conj (a r) *
            (imaginaryOrderK 0 (q + r) : ℂ)) := by
  rw [amplitudeK_full_height_pairKZero P a ha,
    qPairKZero_integral_eq_region P a ha]

/-- Explicit positive semidefiniteness of the physical K₀(q+r) kernel on
continuous compactly supported amplitudes. This is a consequence of the
actual full-height norm square, not an assumed kernel condition. -/
theorem regionKZero_positive_semidefinite (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    0 ≤ Complex.re
      (∫ q in P.region, ∫ r in P.region,
        a q * Complex.conj (a r) *
          (imaginaryOrderK 0 (q + r) : ℂ)) := by
  have h := amplitudeK_full_height_regionKZero P a ha
  have hE : 0 ≤ ∫ t : ℝ, ‖amplitudeK P a t‖ ^ 2 :=
    integral_nonneg (fun t => sq_nonneg _)
  have hπ : 0 < Real.pi / 2 := by positivity
  nlinarith

theorem kTestTransform_full_height_pairKZero (P : PacketData ι) (k : D4 → ℤ) :
    (∫ t : ℝ, ‖kTestTransform P k t‖ ^ 2) =
      (Real.pi / 2) * Complex.re
        (∫ p : ℝ × ℝ, qPairKZero (actualKAmplitude P k) p ∂(volume.prod volume)) := by
  simpa only [← kTestTransform_eq_amplitudeK] using
    amplitudeK_full_height_pairKZero P (actualKAmplitude P k)
      (actualKAmplitude_physical P k)

theorem kTestTransform_full_height_regionKZero (P : PacketData ι) (k : D4 → ℤ) :
    (∫ t : ℝ, ‖kTestTransform P k t‖ ^ 2) =
      (Real.pi / 2) * Complex.re
        (∫ q in P.region, ∫ r in P.region,
          (spectralTest k P.Y0 q / (q : ℂ)) *
            Complex.conj (spectralTest k P.Y0 r / (r : ℂ)) *
              (imaginaryOrderK 0 (q + r) : ℂ)) := by
  have h := amplitudeK_full_height_regionKZero P (actualKAmplitude P k)
    (actualKAmplitude_physical P k)
  simp_rw [← kTestTransform_eq_amplitudeK, actualKAmplitude_eq] at h
  exact h

theorem actualKZero_positive_semidefinite (P : PacketData ι) (k : D4 → ℤ) :
    0 ≤ Complex.re
      (∫ q in P.region, ∫ r in P.region,
        (spectralTest k P.Y0 q / (q : ℂ)) *
          Complex.conj (spectralTest k P.Y0 r / (r : ℂ)) *
            (imaginaryOrderK 0 (q + r) : ℂ)) := by
  simpa only [actualKAmplitude_eq] using
    regionKZero_positive_semidefinite P (actualKAmplitude P k)
      (actualKAmplitude_physical P k)

end
end ImbalancedChen.Part3.ActualKZeroPairEnergy20261024z
