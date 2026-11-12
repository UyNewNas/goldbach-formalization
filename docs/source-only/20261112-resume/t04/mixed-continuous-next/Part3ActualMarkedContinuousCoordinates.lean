import ImbalancedChen.Part3ActualInitialHorocycleLaplace
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness

/-! The actual unit-leading, normalized native Eisenstein spectrum of
the signed physical packets is the conjugate of a bounded Hilbert
analysis coordinate. Compact spectral probes and all L² probes use the
same full-line density. -/
namespace ImbalancedChen.Part3.ActualMarkedContinuousCoordinates20261112

noncomputable section
open Set Filter Topology Complex MeasureTheory Matrix
open scoped UpperHalfPlane MatrixGroups BigOperators
open AngularFourierUnitary20261026b ActualLogHorocycleAdjoint20261112
open ActualMarkedHorocycleSupport20261112 LogHorocycleLaplaceBoundary20261112
open ActualCompactPacketParameter20261112 ActualInitialHorocycleLaplace20261112
open ActualCharacterCuspExpansion20261110 ActualYoungCriticalCusps20261110 ActualCuspDenominatorClasses20261110
open ActualCriticalCuspEvaluation20261110 ActualRegularEisensteinQuotient20261110 ActualIncompleteCriticalColumns20261110
open ActualContinuousSpatialProfiles20261110 ActualYoungFormalClass20261110
open Gamma0ActualConstantMode20261025a Gamma0QuotientCellPushforward20261025a
open OriginalContinuousPoincarePackets20261110 OriginalContinuousCuspGram20261110
open Gamma0CarrierMeasurableInverse20261025a

private theorem continue_pair (N : ℕ) [NeZero N] (g : SL(2,ℤ)) {V : Gamma0OrbitSpace N → ℂ}
    (hV : MemLp V 2 (carrierPushforward N)) (hc : supportedInQuotientCompact N V)
    (h0 : (ℂ ∙ constantL2 N).starProjection (hV.toLp V)=0) {s : ℂ} (hs : 1/2 < s.re) (hs' : s.im ≠ 0) :
    spatial (nativeFrameOrbit N g) V s = laplace (logMean N g V) s := by
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  have hH := ((synthesis N g).adjoint (hV.toLp V)).memLp.congr (mean_zero_adjoint N g hV h0)
  obtain ⟨A,hA⟩ := compact_logMean_cutoff N g hc
  let U := {w : ℂ | 1/2 < w.re} ∩ (if 0 < s.im then {w : ℂ | 0 < w.im} else {w : ℂ | w.im < 0})
  have ho : IsOpen U := by
    unfold U
    split <;> exact (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt (by fun_prop) (by fun_prop))
  have hU : IsPreconnected U := by
    unfold U
    split
    · exact ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)).isPreconnected
    · exact ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt _)).isPreconnected
  have reg {w : ℂ} (hw : w ∈ U) : 1/2 < w.re ∧ w ≠ 1 := by
    refine ⟨hw.1,?_⟩
    rintro rfl
    have J := hw.2
    dsimp only at J
    split at J <;> simpa using J
  have h₁ : AnalyticOnNhd ℂ (spatial (nativeFrameOrbit N g) V) U :=
    DifferentiableOn.analyticOnNhd (fun w hw => (spatial_differentiable _ hc
      (hV.integrable (by norm_num)) (reg hw).1 (reg hw).2).differentiableWithinAt) ho
  have h₂ : AnalyticOnNhd ℂ (laplace (logMean N g V)) U :=
    DifferentiableOn.analyticOnNhd (fun w hw => (laplace_differentiable hH hA (reg hw).1).differentiableWithinAt) ho
  let p : ℂ := ⟨2,s.im⟩
  have hp : p ∈ U := by
    refine ⟨by norm_num [p],?_⟩
    by_cases h : 0 < s.im
    · simpa only [if_pos h,mem_setOf_eq,p] using h
    · simpa only [if_neg h,mem_setOf_eq,p] using lt_of_le_of_ne (le_of_not_gt h) hs'
  have hS : s ∈ U := by
    refine ⟨hs,?_⟩
    by_cases h : 0 < s.im
    · simpa only [if_pos h,mem_setOf_eq] using h
    · simpa only [if_neg h,mem_setOf_eq] using lt_of_le_of_ne (le_of_not_gt h) hs'
  exact h₁.eqOn_of_preconnected_of_eventuallyEq h₂ hU hp
    (((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show 1 < p.re by norm_num [p])).mono
      (fun w hw => initial_laplace N g hV hc h0 hw)) hS

def analysis (N : ℕ) [NeZero N] (a : Parameters N) (v : QuotientL2 N) : AngularL2 :=
  angularFourierUnitary ((synthesis N (parameterFrame a)).adjoint v)

private theorem physical_boundary (N : ℕ) [NeZero N] (a : Parameters N) {V : Gamma0OrbitSpace N → ℂ}
    (hV : MemLp V 2 (carrierPushforward N)) (hc : supportedInQuotientCompact N V)
    (h0 : (ℂ ∙ constantL2 N).starProjection (hV.toLp V)=0) :
    (analysis N a (hV.toLp V) : ℝ → ℂ) =ᵐ[angularMeasure] fun t => star (spectrum N V a t) := by
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  let g := parameterFrame a
  let b := nativeFrameOrbit N g
  let H := logMean N g V
  have A := mean_zero_adjoint N g hV h0
  have hH : MemLp H 2 volume := ((synthesis N g).adjoint (hV.toLp V)).memLp.congr A
  have ID : hH.toLp H = (synthesis N g).adjoint (hV.toLp V) := Lp.ext (hH.coeFn_toLp.trans A.symm)
  obtain ⟨Y,hY⟩ := compact_logMean_cutoff N g hc
  obtain ⟨k,hk,T⟩ := laplace_fourier_boundary hH hY
  rw [ID] at T
  have ne : ∀ᵐ t : ℝ ∂angularMeasure, t ≠ 0 :=
    Measure.ae_smul_measure (volume.ae_ne (0 : ℝ)) _
  filter_upwards [T,ne] with t ht hne
  have R := (critical_parameters t).2
  have Z : Tendsto (fun n => criticalPoint t+(step (k n) : ℂ)) atTop (𝓝 (criticalPoint t)) := by
    have B := Complex.continuous_ofReal.continuousAt.tendsto.comp (step_zero.comp hk.tendsto_atTop)
    simpa using B.const_add (criticalPoint t)
  have E (n : ℕ) : laplace H (criticalPoint t+(step (k n) : ℂ)) =
      spatial b V (criticalPoint t+(step (k n) : ℂ)) :=
    (continue_pair N g hV hc h0 (by simp [criticalPoint,Complex.mul_re,step_pos])
      (by simpa [criticalPoint,Complex.mul_im] using hne)).symm
  have L := (spatial_continuousAt b hc (hV.integrable (by norm_num)) R.1 R.2.2).tendsto.comp Z
  have S : spatial b V (criticalPoint t) = spectrum N V a t := by
    unfold spatial spectrum
    have B : (youngCuspEquiv N).symm b = a := (youngCuspEquiv N).symm_apply_apply a
    simp only [column,dif_pos R.2,descended_critical,B]
  change angularFourierUnitary ((synthesis N g).adjoint (hV.toLp V)) t = _
  exact tendsto_nhds_unique ht (by simpa only [E,S,Function.comp_apply] using L.star)

/-- Synthesis is a finite sum on the actual physical quotient. Each
angular component uses dt/(2π), with the factor 1/2 dictated by the
two reflected Weyl waves on the full line. -/
def nativeSynthesis (N : ℕ) [NeZero N] (h : Parameters N → AngularL2) : QuotientL2 N :=
  (1/2 : ℂ) • ∑ a : Parameters N, synthesis N (parameterFrame a) (angularFourierUnitary.symm (h a))

private theorem angular_L1_iff (f : ℝ → ℂ) : Integrable f angularMeasure ↔ Integrable f volume := by
  unfold angularMeasure
  exact integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top

theorem mixed_adjoint (N : ℕ) [NeZero N] {V : Gamma0OrbitSpace N → ℂ}
    (hV : MemLp V 2 (carrierPushforward N)) (hc : supportedInQuotientCompact N V)
    (h0 : (ℂ ∙ constantL2 N).starProjection (hV.toLp V)=0) :
    (∀ a : Parameters N, (analysis N a (hV.toLp V) : ℝ → ℂ) =ᵐ[angularMeasure]
      fun t => star (spectrum N V a t)) ∧ ∀ h : Parameters N → AngularL2,
      Integrable (fun t => ∑ a : Parameters N, spectrum N V a t*h a t) ∧
      inner ℂ (hV.toLp V) (nativeSynthesis N h) =
        ((4*Real.pi)⁻¹ : ℝ) • ∫ t, ∑ a : Parameters N,spectrum N V a t*h a t := by
  classical
  let v := hV.toLp V
  have A := fun a => physical_boundary N a hV hc h0
  refine ⟨A,?_⟩
  intro h
  let f := fun a (t : ℝ) => spectrum N V a t*h a t
  have Q (a : Parameters N) : (fun t => star (analysis N a v t)*h a t) =ᵐ[angularMeasure] f a := by
    filter_upwards [A a] with t ht
    simp only [v,ht,star_star,f]
  have I (a : Parameters N) : Integrable (f a) angularMeasure :=
    ((analysis N a v).memLp.star.integrable_mul (h a).memLp).congr (Q a)
  have H (a : Parameters N) : inner ℂ v (synthesis N (parameterFrame a) (angularFourierUnitary.symm (h a))) =
      ∫ t, f a t ∂angularMeasure := by
    rw [← ContinuousLinearMap.adjoint_inner_left,← angularFourierUnitary.inner_map_eq_flip,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Q a] with t ht
    simpa only [RCLike.inner_apply',← Complex.star_def,mul_comm,analysis] using ht
  have J := integrable_finsetSum Finset.univ (fun a _ => I a)
  refine ⟨(angular_L1_iff _).mp J,?_⟩
  rw [nativeSynthesis,inner_smul_right,inner_sum]
  simp_rw [H]
  rw [← integral_finsetSum Finset.univ (fun a _ => I a),angularMeasure_integral]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_ofNat]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

end
end ImbalancedChen.Part3.ActualMarkedContinuousCoordinates20261112
