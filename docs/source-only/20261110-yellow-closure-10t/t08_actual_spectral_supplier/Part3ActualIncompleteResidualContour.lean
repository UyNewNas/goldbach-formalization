import ImbalancedChen.Part3ActualIncompleteContinuousGram
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The actual scalar meromorphic integrand, its spatial residue on all
compact zero-mode tests, and the pole-free finite rectangle containing
the original Mellin line and the true continuous boundary. -/
namespace ImbalancedChen.Part3.ActualIncompleteResidualContour20261110

noncomputable section
open Set Filter Topology MeasureTheory Matrix Complex UpperHalfPlane
open scoped UpperHalfPlane MatrixGroups BigOperators Classical Interval
open ActualCharacterCuspExpansion20261110 ActualCriticalScatteringEntry20261110
open ActualNativeResidualChannel20261110 ActualResidualVolumeNormalization20261110
open OriginalResidualPoincarePackets20261110 Gamma0ActualConstantMode20261025a
open Gamma0QuotientCellPushforward20261025a NormalizedCuspCompactPoincare20261026b
open NormalizedCuspCompactFourierFubini20261026b AllNormalizedCuspAnnihilator20261026b
open SmoothZeroHeightSeedProfiles20261026b NativeCuspCompactMellinSynthesis20261027 OriginalFrameZeroSeedMellin20261027
open ActualIncompleteEisensteinTransform20261110 ActualIncompleteEisensteinGram20261110
open ActualIncompleteMellinFactors20261110 ActualIncompleteCriticalColumns20261110 ActualIncompleteContinuousGram20261110

def scalar (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) (s : ℂ) : ℂ :=
  heightMellin φ.toHeightSeed s *
    ((if nativeFrameOrbit N h = nativeFrameOrbit N g then moment ψ.toHeightSeed s else 0) +
      continuedEntry N (NeZero.pos N) g h s*moment ψ.toHeightSeed (1-s))

def residue (N : ℕ) [NeZero N] (ψ φ : SmoothHeightSeed) : ℂ :=
  heightMellin φ.toHeightSeed 1 * (((actualVolume N : ℝ) : ℂ)⁻¹*moment ψ.toHeightSeed 0)

theorem scalar_on_line (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) (σ t : ℝ) :
    scalar N g h ψ φ (verticalParameter σ t) = gramIntegrand N g h ψ φ σ t := by
  simp only [scalar,gramIntegrand,heightMellin_angular]

private theorem scalar_regular (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed)
    {s : ℂ} (hs : 1/2 ≤ s.re) (h₁ : s ≠ 1) :
    DifferentiableAt ℂ (scalar N g h ψ φ) s := by
  have H := (continuedEntry_regularity N (NeZero.pos N) g h).2 s hs h₁
  apply (heightMellin_entire φ.toHeightSeed s).mul
  apply DifferentiableAt.add
  · by_cases e : nativeFrameOrbit N h = nativeFrameOrbit N g <;> simp only [e,if_true,if_false]
    · exact moment_entire ψ.toHeightSeed s
    · exact differentiableAt_const _
  · exact H.mul ((moment_entire _ _).comp s ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id))

theorem scalar_pole (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    Tendsto (fun s : ℂ => (s-1)*scalar N g h ψ φ s) (𝓝[≠] 1) (𝓝 (residue N ψ φ)) := by
  let c := if nativeFrameOrbit N h = nativeFrameOrbit N g then (1 : ℂ) else 0
  have v : Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 0) := by
    simpa using ((continuous_id.sub continuous_const).tendsto (1 : ℂ)).mono_left nhdsWithin_le_nhds
  have P := ((heightMellin_entire φ.toHeightSeed 1).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have J := ((moment_entire ψ.toHeightSeed 1).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have W : Tendsto (fun s : ℂ => moment ψ.toHeightSeed (1-s)) (𝓝[≠] 1) (𝓝 (moment ψ.toHeightSeed 0)) := by
    simpa using (((moment_entire ψ.toHeightSeed).continuous.comp (continuous_const.sub continuous_id)).tendsto
      (1 : ℂ)).mono_left nhdsWithin_le_nhds
  have H := P.mul ((v.mul (tendsto_const_nhds.mul J : Tendsto (fun s : ℂ => c*moment ψ.toHeightSeed s)
      (𝓝[≠] 1) _)).add ((entry_pole N g h).mul W))
  simp only [zero_mul,zero_add] at H
  apply H.congr' (Eventually.of_forall (fun s => ?_))
  by_cases e : nativeFrameOrbit N h = nativeFrameOrbit N g <;>
    simp [scalar,c,e] <;> ring

private theorem zero_mean (N : ℕ) [NeZero N] (h : SL(2,ℤ)) (ψ : SmoothHeightSeed) :
    (∫ u,star (zeroPoincare N h ψ.toHeightSeed u) ∂carrierPushforward N) = moment ψ.toHeightSeed 0 := by
  have J := framePoincare_pairing_eq_fourier N (NeZero.pos N) h 0 ψ.toFun ψ.continuous ψ.compact ψ.positive
    (fun _ => (1 : ℂ)) (constant_memLp_two N)
  have Y {y : ℝ} (hy : 0 < y) : frameFourier N (NeZero.pos N) h (fun _ => (1 : ℂ)) 0 y = 1 := by
    rw [frameFourier_positive_height _ _ _ _ _ hy,integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one]
    simp
  simp only [mul_one] at J
  rw [zeroPoincare,J,moment]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  simp only [Y hy,Complex.cpow_zero,mul_one]

/-- The residue of this Gram integrand is the actual constant-line
projection pairing with the same order of its two genuine quotient vectors. -/
theorem residue_is_physical (N : ℕ) [NeZero N] (h g : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    residue N ψ φ = inner ℂ (frameZeroSeedL2 N (NeZero.pos N) h ψ.toHeightSeed)
      ((ℂ ∙ constantL2 N).starProjection (frameZeroSeedL2 N (NeZero.pos N) g φ.toHeightSeed)) := by
  let V := frameZeroSeedL2 N (NeZero.pos N) h ψ.toHeightSeed
  let W := frameZeroSeedL2 N (NeZero.pos N) g φ.toHeightSeed
  have Q (j : SL(2,ℤ)) (f : SmoothHeightSeed) :
      (∫ u,(frameZeroSeedL2 N (NeZero.pos N) j f.toHeightSeed) u ∂carrierPushforward N) =
        heightMellin f.toHeightSeed 1 := by
    rw [integral_congr_ae (original_frameZeroSeedL2_ae_representative N (NeZero.pos N) j f)]
    have J := congrArg star (zero_mean N j f)
    simpa only [Complex.star_def,← integral_conj,Complex.conj_conj,zeroPoincare,moment_conjugated,
      map_zero,sub_zero] using J
  have H : inner ℂ V (constantL2 N) = moment ψ.toHeightSeed 0 := by
    rw [L2.inner_def]
    calc
      _ = ∫ u,star (zeroPoincare N h ψ.toHeightSeed u) ∂carrierPushforward N := by
        apply integral_congr_ae
        filter_upwards [original_frameZeroSeedL2_ae_representative N (NeZero.pos N) h ψ,
          (constant_memLp_two N).coeFn_toLp] with u hu hv
        change inner ℂ ((frameZeroSeedL2 N (NeZero.pos N) h ψ.toHeightSeed) u)
          ((constant_memLp_two N).toLp (fun _ => (1 : ℂ)) u) = _
        simp only [RCLike.inner_apply',hu,hv,mul_one,Complex.star_def,zeroPoincare]
      _ = _ := zero_mean N h ψ
  change residue N ψ φ = inner ℂ V ((ℂ ∙ constantL2 N).starProjection W)
  rw [actual_residual_projection N (nativeFrameOrbit N g),native_residue_inverse_volume,Q,
    inner_smul_right,H,residue]
  ring

private def regularPart (F : ℂ → ℂ) (r : ℂ) : ℂ → ℂ :=
  dslope (Function.update (fun s : ℂ => (s-1)*F s) 1 r) 1

private theorem regularPart_formula (F : ℂ → ℂ) (r : ℂ) {s : ℂ} (h : s ≠ 1) :
    regularPart F r s = F s-r/(s-1) := by
  rw [regularPart,dslope_of_ne _ h,slope_def_module,Function.update_of_ne h,Function.update_self,smul_eq_mul]
  field_simp [sub_ne_zero.mpr h] <;> ring

private theorem regularPart_diff (F : ℂ → ℂ) (r : ℂ)
    (H : ∀ s : ℂ, 1/2 ≤ s.re → s ≠ 1 → DifferentiableAt ℂ F s)
    (R : Tendsto (fun s : ℂ => (s-1)*F s) (𝓝[≠] 1) (𝓝 r)) :
    DifferentiableOn ℂ (regularPart F r) {s : ℂ | 1/2 ≤ s.re} := by
  let D := {s : ℂ | 1/2 ≤ s.re}
  have nh : D ∈ 𝓝 (1 : ℂ) := Filter.mem_of_superset
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (1/2 : ℝ) < (1 : ℂ).re))
    (fun _ h => h.le)
  apply (Complex.differentiableOn_dslope nh).mpr
  apply (Complex.differentiableOn_compl_singleton_and_continuousAt_iff nh).mp
  refine ⟨?_,continuousAt_update_same.mpr R⟩
  intro s hs
  have hn : s ≠ 1 := hs.2
  apply (((differentiableAt_id.sub_const 1).mul (H s hs.1 hn)).congr_of_eventuallyEq _).differentiableWithinAt
  filter_upwards [isOpen_ne.mem_nhds hn] with u hu
  exact Function.update_of_ne hu _ _

def edge (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) (T : ℝ) :=
  let U := regularPart (scalar N g h ψ φ) (residue N ψ φ)
  Complex.I * ((∫ x : ℝ in (1/2)..(3/2),U (verticalParameter x T)) -
    ∫ x : ℝ in (1/2)..(3/2),U (verticalParameter x (-T)))

private theorem rectangle (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) (T : ℝ) :
    let U := regularPart (scalar N g h ψ φ) (residue N ψ φ)
    (∫ t : ℝ in (-T)..T,U (verticalParameter (3/2) t)) -
      (∫ t : ℝ in (-T)..T,U (verticalParameter (1/2) t)) = -edge N g h ψ φ T := by
  let U := regularPart (scalar N g h ψ φ) (residue N ψ φ)
  have HD : DifferentiableOn ℂ U {s : ℂ | 1/2 ≤ s.re} :=
    regularPart_diff _ _ (fun _ => scalar_regular N g h ψ φ) (scalar_pole N g h ψ φ)
  let R := ∫ t : ℝ in (-T)..T,U (verticalParameter (3/2) t)
  let L := ∫ t : ℝ in (-T)..T,U (verticalParameter (1/2) t)
  let A := ∫ x : ℝ in (1/2)..(3/2),U (verticalParameter x T)
  let B := ∫ x : ℝ in (1/2)..(3/2),U (verticalParameter x (-T))
  have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn U (⟨1/2,-T⟩ : ℂ) (⟨3/2,T⟩ : ℂ)
    (HD.mono (fun z hz => (show z.re ∈ [[(1/2 : ℝ),3/2]] from hz.1).1.trans' (by norm_num)))
  have J : B-A+Complex.I*R-Complex.I*L = 0 := by
    simpa only [A,B,R,L,verticalParameter,Complex.real_smul,smul_eq_mul] using H
  have X : Complex.I*(R-L) = A-B := by linear_combination J
  change R-L = -(Complex.I*(A-B))
  rw [← X,← mul_assoc,Complex.I_mul_I,neg_one_mul,neg_neg]


private theorem pole_kernel (t : ℝ) :
    (verticalParameter (3/2) t-1)⁻¹-(verticalParameter (1/2) t-1)⁻¹ =
      (((((1/2 : ℝ)^2+t^2)⁻¹ : ℝ)) : ℂ) := by
  have A : verticalParameter (3/2) t-1 = (⟨1/2,t⟩ : ℂ) := by
    apply Complex.ext <;> norm_num [verticalParameter,Complex.mul_re,Complex.mul_im]
  have B : verticalParameter (1/2) t-1 = (⟨-(1/2),t⟩ : ℂ) := by
    apply Complex.ext <;> norm_num [verticalParameter,Complex.mul_re,Complex.mul_im]
  have ha : Complex.normSq (⟨1/2,t⟩ : ℂ) = (1/2 : ℝ)^2+t^2 := by rw [Complex.normSq_apply]; ring
  have hb : Complex.normSq (⟨-(1/2),t⟩ : ℂ) = (1/2 : ℝ)^2+t^2 := by rw [Complex.normSq_apply]; ring
  rw [A,B]
  apply Complex.ext <;> simp only [Complex.sub_re,Complex.sub_im,Complex.inv_re,Complex.inv_im,
    Complex.ofReal_re,Complex.ofReal_im,ha,hb] <;> ring

private theorem vertical_regular (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed)
    (c : ℝ) (hc : 1/2 ≤ c) (hn : c ≠ 1) (T : ℝ) :
    let r := residue N ψ φ
    (∫ t : ℝ in (-T)..T,regularPart (scalar N g h ψ φ) r (verticalParameter c t)) =
      (∫ t : ℝ in (-T)..T,gramIntegrand N g h ψ φ c t) -
        r*(∫ t : ℝ in (-T)..T,(verticalParameter c t-1)⁻¹) := by
  have hne (t : ℝ) : verticalParameter c t ≠ 1 := fun E => hn (by
    simpa only [verticalParameter_re,Complex.one_re] using congrArg Complex.re E)
  have V : Continuous (verticalParameter c) := by unfold verticalParameter; fun_prop
  have C : Continuous (gramIntegrand N g h ψ φ c) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    simp_rw [← scalar_on_line]
    exact (scalar_regular N g h ψ φ (by simpa using hc) (hne t)).continuousAt.comp V.continuousAt
  have K : Continuous (fun t : ℝ => (verticalParameter c t-1)⁻¹) :=
    (V.sub continuous_const).inv₀ (fun t => sub_ne_zero.mpr (hne t))
  calc
    _ = ∫ t : ℝ in (-T)..T,gramIntegrand N g h ψ φ c t-residue N ψ φ*(verticalParameter c t-1)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t _
      rw [regularPart_formula _ _ (hne t),scalar_on_line,div_eq_mul_inv]
    _ = _ := by
      rw [intervalIntegral.integral_sub (C.intervalIntegrable _ _) ((K.const_mul _).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul]

/-- Exact finite-height flux across the two vertical lines, with the
closed-contour pole kernel evaluated. No condition on horizontal growth
enters the finite rectangle. -/
theorem finite_contour (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) (T : ℝ) :
    edge N g h ψ φ T =
      (∫ t : ℝ in (-T)..T,gramIntegrand N g h ψ φ (1/2) t) -
      (∫ t : ℝ in (-T)..T,gramIntegrand N g h ψ φ (3/2) t) +
      residue N ψ φ * (4*(Real.arctan (2*T) : ℂ)) := by
  have H := rectangle N g h ψ φ T
  rw [vertical_regular N g h ψ φ (3/2) (by norm_num) (by norm_num),
    vertical_regular N g h ψ φ (1/2) le_rfl (by norm_num)] at H
  have K (c : ℝ) (hc : c ≠ 1) : Continuous (fun t : ℝ => (verticalParameter c t-1)⁻¹) := by
    apply (show Continuous (fun t : ℝ => verticalParameter c t-1) by unfold verticalParameter; fun_prop).inv₀
    intro t
    apply sub_ne_zero.mpr
    intro E
    exact hc (by simpa using congrArg Complex.re E)
  have J : (∫ t : ℝ in (-T)..T,(verticalParameter (3/2) t-1)⁻¹) -
      (∫ t : ℝ in (-T)..T,(verticalParameter (1/2) t-1)⁻¹) = 4*(Real.arctan (2*T) : ℂ) := by
    rw [← intervalIntegral.integral_sub ((K _ (by norm_num)).intervalIntegrable _ _)
      ((K _ (by norm_num)).intervalIntegrable _ _)]
    simp_rw [pole_kernel]
    rw [intervalIntegral.integral_ofReal,integral_inv_sq_add_sq (by norm_num : (1/2 : ℝ) ≠ 0)]
    rw [show T/(1/2 : ℝ) = 2*T by ring,show -T/(1/2 : ℝ) = -(2*T) by ring,Real.arctan_neg]
    push_cast
    ring
  linear_combination H + residue N ψ φ * J

/-- The finite-height error has a limit fixed by the original spatial
Gram, the correctly normalized physical continuous product and the
actual residual projection. Closing the remaining contour requires its
tending to zero. -/
theorem physical_contour_limit (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    let V := frameZeroSeedL2 N (NeZero.pos N) h ψ.toHeightSeed
    let W := frameZeroSeedL2 N (NeZero.pos N) g φ.toHeightSeed
    Tendsto (fun T : ℝ => (2*Real.pi)⁻¹ • edge N g h ψ φ T) atTop
      (𝓝 ((4*Real.pi)⁻¹ • (∫ t : ℝ,physicalProduct N h g ψ φ t) -
        inner ℂ V W + inner ℂ V ((ℂ ∙ constantL2 N).starProjection W))) := by
  have A := initial_spatial_gram N h g ψ φ (3/2) (by norm_num)
  have J := gram_critical_integrable N g h ψ φ
  have L := intervalIntegral_tendsto_integral J (tendsto_neg_atTop_atBot) (tendsto_id (α := ℝ))
  have R := intervalIntegral_tendsto_integral A.1 (tendsto_neg_atTop_atBot) (tendsto_id (α := ℝ))
  have v : Tendsto (fun T : ℝ => 2*T) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  have H := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp v)
  have Q := ((L.sub R).add (tendsto_const_nhds.mul (tendsto_const_nhds.mul H) :
    Tendsto (fun T : ℝ => residue N ψ φ*(4*(Real.arctan (2*T) : ℂ))) atTop _)).const_smul ((2*Real.pi)⁻¹ : ℝ)
  simp only [finite_contour,full_line_normalization,A.2,← residue_is_physical]
  convert Q using 1
  push_cast
  simp only [Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

end
end ImbalancedChen.Part3.ActualIncompleteResidualContour20261110
