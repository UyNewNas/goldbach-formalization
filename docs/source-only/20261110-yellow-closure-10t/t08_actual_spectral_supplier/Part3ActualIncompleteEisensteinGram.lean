import ImbalancedChen.Part3ActualIncompleteEisensteinTransform
import ImbalancedChen.Part3NativeAllCuspEisensteinVerticalBound

/-! Genuine spatial Gram matrix of the sharp compact-height generators.
Fubini on the actual quotient is paid using the physical real-axis
Eisenstein majorant in exactly the same observing frame. -/
namespace ImbalancedChen.Part3.ActualIncompleteEisensteinGram20261110

noncomputable section
open Set Filter Topology MeasureTheory Complex UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators Classical
open ActualCharacterCuspExpansion20261110 ActualYoungCriticalCusps20261110 ActualCriticalScatteringEntry20261110
open ActualRegularEisensteinQuotient20261110 ActualIncompleteEisensteinTransform20261110
open SmoothZeroHeightSeedProfiles20261026b CompactHeightMellinInversion20261027
open NativeCuspCompactMellinSynthesis20261027 OriginalFrameZeroSeedMellin20261027
open NativeAllCuspEisenstein20261026b NativeAllCuspEisenstein20261027
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open NormalizedCuspCompactPoincare20261026b AllNormalizedCuspAnnihilator20261026b

private theorem regular {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1/2 ≤ (verticalParameter σ t).re ∧ verticalParameter σ t ≠ 0 ∧ verticalParameter σ t ≠ 1 := by
  have h := verticalParameter_re σ t
  refine ⟨by linarith,?_,?_⟩ <;> intro e <;> rw [e] at h <;> norm_num at h <;> linarith

private def column (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :=
  descended (nativeFrameOrbit N g) (verticalParameter σ t) (regular hσ t).2.1 (regular hσ t).2.2

private theorem up (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (σ : ℝ) (hσ : 1 < σ) (t : ℝ) (z : ℍ) :
    column N g σ hσ t (orbitProjection N z) = cuspEisenstein N g (verticalParameter σ t) z :=
  cuspFamily_initial N g _ (by simpa using hσ) z

private theorem domination (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (u : Gamma0OrbitSpace N) : ‖column N g σ hσ t u‖ ≤ ‖column N g σ hσ 0 u‖ := by
  induction u using Quotient.inductionOn with
  | _ z =>
    change ‖column N g σ hσ t (orbitProjection N z)‖ ≤ ‖column N g σ hσ 0 (orbitProjection N z)‖
    rw [up,up,show verticalParameter σ 0 = σ by simp [verticalParameter]]
    exact (norm_cuspEisenstein_vertical_le N (NeZero.pos N) g σ hσ t z).trans (Complex.re_le_norm _)

private theorem jointly_measurable (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (σ : ℝ) (hσ : 1 < σ) :
    Measurable (Function.uncurry (column N g σ hσ)) := by
  apply measurable_uncurry_of_continuous_of_measurable
  · intro u
    induction u using Quotient.inductionOn with
    | _ z =>
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (parameterFamily_differentiable ((youngCuspEquiv N).symm (nativeFrameOrbit N g))
        z _ (regular hσ t).1 (regular hσ t).2.2).continuousAt.comp (show Continuous (verticalParameter σ) by
          unfold verticalParameter
          fun_prop).continuousAt
  · intro t
    exact (descended_continuous_measurable _ _ _ _).2

def gramIntegrand (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed)
    (σ t : ℝ) : ℂ :=
  let s := verticalParameter σ t
  mellinAngular φ σ t*((if nativeFrameOrbit N h = nativeFrameOrbit N g then moment ψ.toHeightSeed s else 0) +
    continuedEntry N (NeZero.pos N) g h s*moment ψ.toHeightSeed (1-s))

private theorem mellin_rep (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (φ : SmoothHeightSeed)
    (σ : ℝ) (hσ : 1 < σ) :
    zeroPoincare N g φ.toHeightSeed =ᵐ[carrierPushforward N] fun u =>
      (2*Real.pi)⁻¹ • ∫ t : ℝ,mellinAngular φ σ t*column N g σ hσ t u := by
  rw [← reducedProjection_map_measure N,(reducedProjection_measurableEmbedding N).ae_map_iff]
  apply ae_of_all
  intro w
  exact (original_frame_zero_Poincare_mellin_projection N (NeZero.pos N) g φ σ hσ w).trans (by
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun t => congrArg (fun c : ℂ => mellinAngular φ σ t*c) (up N g σ hσ t w).symm))

/-- Both vectors are the actual quotient L² elements, with the original
sharp half-open strip and stabilizer multiplicity at the two frames.
The scalar contour is absolutely integrable for every σ>1. -/
theorem initial_spatial_gram (N : ℕ) [NeZero N] (h g : SL(2,ℤ)) (ψ φ : SmoothHeightSeed)
    (σ : ℝ) (hσ : 1 < σ) :
    Integrable (gramIntegrand N g h ψ φ σ) ∧
    inner ℂ (frameZeroSeedL2 N (NeZero.pos N) h ψ.toHeightSeed)
      (frameZeroSeedL2 N (NeZero.pos N) g φ.toHeightSeed) =
      (2*Real.pi)⁻¹ • ∫ t : ℝ,gramIntegrand N g h ψ φ σ t := by
  classical
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  let P := zeroPoincare N h ψ.toHeightSeed
  let F := column N g σ hσ
  let G (u : Gamma0OrbitSpace N) (t : ℝ) := mellinAngular φ σ t*(star (P u)*F t u)
  have T (t : ℝ) := physical_zero_transform N g h ψ.toHeightSeed (verticalParameter σ t)
    (regular hσ t).1 (regular hσ t).2.2
  have A : Integrable (fun u => star (P u)*F 0 u) (carrierPushforward N) := (T 0).1
  have hP := (framePoincare_memLp_two N (NeZero.pos N) h 0 ψ.toFun ψ.continuous ψ.compact ψ.positive).1
  have hfreq : Continuous (mellinAngular φ σ) :=
    (mellinFrequency_continuous φ σ).comp (continuous_const.mul continuous_id)
  have H : Integrable (Function.uncurry G) ((carrierPushforward N).prod volume) := by
    apply (A.norm.mul_prod (mellinAngular_integrable φ σ).norm).mono'
    · have hF := (jointly_measurable N g σ hσ).comp measurable_swap
      exact (hfreq.measurable.comp measurable_snd).aestronglyMeasurable.mul
        ((hP.comp_fst.star).mul hF.aestronglyMeasurable)
    · apply ae_of_all
      intro p
      dsimp only [Function.uncurry,G]
      simp only [norm_mul,norm_star]
      calc
        ‖mellinAngular φ σ p.2‖*(‖P p.1‖*‖F p.2 p.1‖) ≤
            ‖mellinAngular φ σ p.2‖*(‖P p.1‖*‖F 0 p.1‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (domination N g σ hσ _ _) (norm_nonneg _)) (norm_nonneg _)
        _ = _ := mul_comm _ _
  have eval (t : ℝ) : (∫ u,G u t ∂carrierPushforward N) = gramIntegrand N g h ψ φ σ t := by
    rw [show (∫ u,G u t ∂carrierPushforward N) = mellinAngular φ σ t*
        (∫ u,star (P u)*F t u ∂carrierPushforward N) from integral_const_mul _ _,(T t).2]
    rfl
  refine ⟨H.integral_prod_right.congr (ae_of_all _ eval),?_⟩
  rw [L2.inner_def]
  calc
    _ = ∫ u,star (P u)*zeroPoincare N g φ.toHeightSeed u ∂carrierPushforward N := by
      apply integral_congr_ae
      filter_upwards [original_frameZeroSeedL2_ae_representative N (NeZero.pos N) h ψ,
        original_frameZeroSeedL2_ae_representative N (NeZero.pos N) g φ] with u hu hv
      simpa only [RCLike.inner_apply',← Complex.star_def,hu,hv]
    _ = ∫ u,(2*Real.pi)⁻¹ • (∫ t : ℝ,G u t) ∂carrierPushforward N := by
      apply integral_congr_ae
      filter_upwards [mellin_rep N g φ σ hσ] with u hu
      rw [hu,mul_smul_comm,← integral_const_mul]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by dsimp [G,F]; ring)
    _ = _ := by
      rw [integral_smul,integral_integral_swap H]
      simp_rw [eval]

end
end ImbalancedChen.Part3.ActualIncompleteEisensteinGram20261110
