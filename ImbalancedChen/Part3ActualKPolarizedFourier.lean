import ImbalancedChen.Part3ActualKFullHeightEnergy
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED (2026-10-24). The complex polarized L² pairing
of two genuine physical K transforms is obtained from Mathlib's L²
Fourier inner-product isometry and the proved L¹/L² compatibility bridge.
No spectral Plancherel hypothesis is introduced.
-/

namespace ImbalancedChen.Part3.ActualKPolarizedFourier20261024z
noncomputable section

open Classical Set MeasureTheory
open scoped FourierTransform
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualKTransformFourier20261024z
open ActualKFullHeightEnergy20261024z
open FourierL1L2PlancherelSourceOnly

variable {ι : Type*}

/-- Complex polarization of the integral Fourier transform. The order of
the L² inner product is reversed because `⟪g,f⟫ = f * conj(g)` for scalars. -/
theorem integral_fourier_cross {f g : ℝ → ℂ}
    (h₁f : Integrable f) (h₂f : MemLp f 2)
    (h₁g : Integrable g) (h₂g : MemLp g 2) :
    (∫ ξ : ℝ, 𝓕 f ξ * Complex.conj (𝓕 g ξ)) =
      ∫ u : ℝ, f u * Complex.conj (g u) := by
  let F : Lp (α := ℝ) ℂ 2 := 𝓕 (h₂f.toLp f)
  let G : Lp (α := ℝ) ℂ 2 := 𝓕 (h₂g.toLp g)
  have hF : (F : ℝ → ℂ) =ᵐ[volume] 𝓕 f :=
    fourier_toLp_ae_eq h₁f h₂f
  have hG : (G : ℝ → ℂ) =ᵐ[volume] 𝓕 g :=
    fourier_toLp_ae_eq h₁g h₂g
  calc
    (∫ ξ : ℝ, 𝓕 f ξ * Complex.conj (𝓕 g ξ)) =
        ∫ ξ : ℝ, F ξ * Complex.conj (G ξ) := by
      apply integral_congr_ae
      filter_upwards [hF, hG] with ξ hfξ hgξ
      rw [hfξ, hgξ]
    _ = ⟪G, F⟫ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [RCLike.inner_apply]
    _ = ⟪h₂g.toLp g, h₂f.toLp f⟫ := by
      exact Lp.inner_fourier_eq (h₂g.toLp g) (h₂f.toLp f)
    _ = ∫ u : ℝ, f u * Complex.conj (g u) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [h₂f.coeFn_toLp, h₂g.coeFn_toLp] with u hfu hgu
      rw [hfu, hgu]
      simp only [RCLike.inner_apply]

/-- The physical full-height cross energy is exactly π/4 times the
full-line Laplace-profile cross energy. -/
theorem amplitudeK_full_height_cross_fourier (P : PacketData ι)
    (a b : ℝ → ℂ) (ha : PhysicalAmplitude P a)
    (hb : PhysicalAmplitude P b) :
    (∫ t : ℝ, amplitudeK P a t * Complex.conj (amplitudeK P b t)) =
      ((Real.pi / 4 : ℝ) : ℂ) *
        ∫ u : ℝ, qLaplaceProfile P a u *
          Complex.conj (qLaplaceProfile P b u) := by
  let A := qLaplaceProfile P a
  let B := qLaplaceProfile P b
  have h₁A : Integrable A := qLaplaceProfile_integrable P a ha
  have h₂A : MemLp A 2 := qLaplaceProfile_memLp_two P a ha
  have h₁B : Integrable B := qLaplaceProfile_integrable P b hb
  have h₂B : MemLp B 2 := qLaplaceProfile_memLp_two P b hb
  have hF := integral_fourier_cross h₁A h₂A h₁B h₂B
  have hscale := Measure.integral_comp_div
    (fun ξ : ℝ => 𝓕 A ξ * Complex.conj (𝓕 B ξ)) Real.pi
  have hπ : |Real.pi| = Real.pi := abs_of_pos Real.pi_pos
  have hhalf : Complex.conj (1 / 2 : ℂ) = (1 / 2 : ℂ) := by simp
  calc
    (∫ t : ℝ, amplitudeK P a t * Complex.conj (amplitudeK P b t)) =
        ∫ t : ℝ, (1 / 4 : ℂ) *
          (𝓕 A (t / Real.pi) * Complex.conj (𝓕 B (t / Real.pi))) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [amplitudeK_half_fourier P a ha t,
        amplitudeK_half_fourier P b hb t]
      simp only [map_mul, hhalf]
      ring
    _ = (1 / 4 : ℂ) *
        ∫ t : ℝ, 𝓕 A (t / Real.pi) *
          Complex.conj (𝓕 B (t / Real.pi)) := by
      rw [integral_const_mul]
    _ = (1 / 4 : ℂ) *
        ((Real.pi : ℂ) * ∫ ξ : ℝ, 𝓕 A ξ * Complex.conj (𝓕 B ξ)) := by
      rw [hscale, hπ]
      simp only [Complex.real_smul]
    _ = _ := by
      rw [hF]
      ring

end
end ImbalancedChen.Part3.ActualKPolarizedFourier20261024z
