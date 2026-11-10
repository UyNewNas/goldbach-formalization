import ImbalancedChen.Part3ActualParabolicScatteringRows
import ImbalancedChen.Part3ActualYoungCriticalCusps
import ImbalancedChen.Part3NativeAllCuspEisensteinSpatialConvergence
import ImbalancedChen.Part3RealPowerSeedConstantMode
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The physical constant term in every normalized pair of native cusp
frames. Its outgoing coefficient is the earlier absolutely convergent
residue-count Dirichlet series times the beta integral. -/
namespace ImbalancedChen.Part3.ActualNativeScatteringConstant20261110

noncomputable section
open Complex Set MeasureTheory Filter Topology Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane BigOperators
open PowerSeedFourierLaplaceFubini PowerSeedGaussianLaplace
open ActualEisensteinFourierInterchange20261025a NativeCuspComplexPowerFourier20261027
open NativeCuspComplexPeriodization20261027 Gamma0GeneralCuspWidth20261025a
open Gamma0GeneralCuspUnitPeriod20261025a NativeAllCuspEisenstein20261026b
open NativeAllCuspEisensteinSpatialConvergence20261026b NativeCuspScatteringRowArithmetic20261027
open NativeCuspScatteringDirichlet20261027 ActualParabolicScatteringRows20261110
open ActualYoungCriticalCusps20261110 ActualCharacterCuspExpansion20261110

def gammaFactor (s : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s-1/2) / Complex.Gamma s

private theorem zero_real (y : ℝ) (hy : 0 < y) (t : ℝ) (ht : 1 < t) :
    actualPowerFourier y 0 (t : ℂ) = gammaFactor (t : ℂ) * (y : ℂ)^(1-(t : ℂ)) := by
  have h := ImbalancedChen.Part3RealPowerSeedConstantMode.integral_powerSeed
    (by linarith : 1/2 < t) hy
  rw [actualPowerFourier,oscillatoryKernel]
  simp only [fourierPhase,Int.cast_zero,mul_zero,neg_zero,zero_mul,Complex.ofReal_zero,
    Complex.exp_zero,one_mul,complexPowerSeed_ofReal hy,integral_complex_ofReal]
  change ((∫ x : ℝ, y^t/(x^2+y^2)^t : ℝ) : ℂ) = _
  rw [h,gammaFactor,show (t : ℂ)-1/2=((t-1/2 : ℝ) : ℂ) by push_cast,
    show 1-(t : ℂ)=((1-t : ℝ) : ℂ) by push_cast,
    Complex.Gamma_ofReal,Complex.Gamma_ofReal,← Complex.ofReal_cpow hy.le]
  push_cast <;> rfl

private theorem outgoing_analytic (y : ℝ) (hy : 0 < y) :
    AnalyticOnNhd ℂ (fun s : ℂ => gammaFactor s*(y : ℂ)^(1-s)) {s : ℂ | 1 < s.re} := by
  have hG (v : ℂ) (hv : 0 < v.re) : DifferentiableAt ℂ Complex.Gamma v := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have h := congrArg Complex.re hn
    simp only [Complex.neg_re,Complex.natCast_re] at h
    linarith [Nat.cast_nonneg n]
  apply DifferentiableOn.analyticOnNhd _ (isOpen_Ioi.preimage Complex.continuous_re)
  intro s hs
  change 1 < s.re at hs
  have h1 : 0 < (s-(1/2 : ℂ)).re := by simp; linarith
  have hg := (hG _ h1).comp s (differentiableAt_id.sub_const (1/2 : ℂ))
  have h2 := hG s (by linarith)
  have hden : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hp := (differentiableAt_const (c := (1 : ℂ)) (x := s)).sub differentiableAt_id
  exact (((differentiableAt_const.mul hg).div h2 hden).mul
    (hp.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne')))).differentiableWithinAt

/-- The zero mode of the same complex power kernel whose nonzero modes
were evaluated in the native Fourier supplier. -/
theorem actualPowerFourier_zero (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    actualPowerFourier y 0 s = gammaFactor s*(y : ℂ)^(1-s) := by
  let U : Set ℂ := {v : ℂ | 1 < v.re}
  have hu : IsPreconnected U := (Complex.convex_halfSpace_re_gt (r := 1)).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by norm_num [U]
  have hcl : (2 : ℂ) ∈ closure
      ({v : ℂ | actualPowerFourier y 0 v = gammaFactor v*(y : ℂ)^(1-v)} \ {2}) := by
    have hi : (2 : ℂ) ∈ closure (Complex.ofReal '' Ioi (2 : ℝ)) :=
      mem_closure_image Complex.continuous_ofReal.continuousAt (by simp)
    apply (closure_mono ?_) hi
    rintro z ⟨t,ht,rfl⟩
    refine ⟨zero_real y hy t (by linarith),?_⟩
    intro he
    have h : t = 2 := by exact_mod_cast (show (t : ℂ) = 2 from he)
    linarith
  exact ((actualPowerFourier_analyticOnNhd hy 0).eqOn_of_preconnected_of_mem_closure
    (outgoing_analytic y hy) hu h2 hcl) s hs

private theorem weight_card (N : ℕ) (g h : SL(2,ℤ)) (c : ℕ) (s : ℂ) :
    denominatorWeight N g h c s * ((residueBlock N g h c).card : ℂ) =
      scatteringDirichletTerm N g h s c := by
  by_cases hc : c = 0
  · subst c
    simp [residueBlock,scatteringDirichletTerm]
  · rw [denominatorWeight,scatteringDirichletTerm,LSeries.term_of_ne_zero hc]
    simp only [scatteringCoeffComplex,scatteringDirichletCoeff,Complex.cpow_neg,div_eq_mul_inv]
    ring

private theorem row_continuous (N : ℕ) (g h : SL(2,ℤ)) (c : ℕ) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) : Continuous (outgoingRow N g h c s y) := by
  exact (continuous_finset_sum _ (fun d _ => (periodizedComplexPowerSeed_continuous hy s hs).comp
    (continuous_id.add_const (residueShift N h c d)))).const_mul _

theorem positive_row_mean (N : ℕ) (g h : SL(2,ℤ)) (c : ℕ+) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, outgoingRow N g h c s y x) =
      scatteringDirichletTerm N g h s c * actualPowerFourier y 0 s := by
  have hr (d : ℕ) : (∫ x in (0 : ℝ)..1, periodizedComplexPowerSeed y s
      (x+residueShift N h c d)) = actualPowerFourier y 0 s := by
    simpa [fourierPhase] using shifted_periodizedComplexPowerSeed_fourier hy s hs 0
      (residueShift N h c d)
  simp only [outgoingRow,intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum (fun d _ =>
    ((periodizedComplexPowerSeed_continuous hy s hs).comp
      (continuous_id.add_const (residueShift N h c d))).intervalIntegrable 0 1)]
  simp only [hr,Finset.sum_const,nsmul_eq_mul,← mul_assoc,weight_card]

private def segment : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
private instance : IsFiniteMeasure segment := ⟨by simp [segment]⟩

/-- Absolute interchange on the literal height-y unit horocycle. All
residue shifts lie in [0,1), so one compact periodized-kernel bound
multiplies the previously proved absolutely summable Dirichlet terms. -/
theorem horocycle_row_norms_summable (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ)) (s : ℂ)
    (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    Summable (fun c : ℕ+ => ∫ x in Ioc (0 : ℝ) 1, ‖outgoingRow N g h c s y x‖) := by
  classical
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 2)).exists_bound_of_continuousOn
    (periodizedComplexPowerSeed_continuous hy s hs).continuousOn
  have hD := ((scatteringDirichletTerm_norm_summable N g h s hs).comp_injective
    PNat.coe_injective).mul_right C
  apply hD.of_nonneg_of_le (fun c => integral_nonneg (fun _ => norm_nonneg _))
  intro c
  have H (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      ‖outgoingRow N g h c s y x‖ ≤ ‖scatteringDirichletTerm N g h s c‖ * C := by
    have hw : 0 < (c : ℝ)*(cuspWidth N h : ℝ) := by
      exact_mod_cast Nat.mul_pos c.2 (cuspWidth_pos N hN h)
    have hshift (d : ℕ) (hd : d ∈ residueBlock N g h c) :
        x + residueShift N h c d ∈ Icc (0 : ℝ) 2 := by
      have hlt : (d : ℝ) < (c : ℝ)*(cuspWidth N h : ℝ) := by
        exact_mod_cast ((mem_residueBlock N g h c d).mp hd).1
      have hlu := (div_lt_one hw).mpr hlt
      have hnon : 0 ≤ (d : ℝ)/((c : ℝ)*(cuspWidth N h : ℝ)) := by positivity
      unfold residueShift
      exact ⟨add_nonneg hx.1.le hnon,by linarith [hx.2]⟩
    have hb := (Finset.sum_le_sum (fun d (hd : d ∈ residueBlock N g h c) =>
      hC _ (hshift d hd)))
    calc
      _ ≤ ‖denominatorWeight N g h c s‖ *
          ∑ d ∈ residueBlock N g h c, ‖periodizedComplexPowerSeed y s (x+residueShift N h c d)‖ := by
        rw [outgoingRow,norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ ≤ ‖denominatorWeight N g h c s‖ * ∑ _d ∈ residueBlock N g h c, C :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by rw [← weight_card,norm_mul,Complex.norm_natCast,Finset.sum_const,nsmul_eq_mul]; ring
  have hmass : segment.real univ = 1 := by simp [segment,measureReal_def]
  have hh : Integrable (outgoingRow N g h c s y) segment :=
    ((row_continuous N g h c s hs y hy).intervalIntegrable 0 1).1
  have Hb : ∀ᵐ x ∂segment, ‖outgoingRow N g h c s y x‖ ≤ ‖scatteringDirichletTerm N g h s c‖*C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact H x hx
  simpa only [integral_const,hmass,one_smul] using
    integral_mono_ae hh.norm (integrable_const (‖scatteringDirichletTerm N g h s c‖*C)) Hb

def scatteringEntry (N : ℕ) (g h : SL(2,ℤ)) (s : ℂ) : ℂ :=
  gammaFactor s * scatteringDirichletSeries N g h s

/-- The actual normalized two-cusp parabolic constant term. The diagonal
is the true cusp orbit delta. The outgoing coefficient uses exactly the
width-dependent Dirichlet series of the native row predicate. -/
theorem parabolic_constant_term (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, cuspEisenstein N g s (normalizedScaling N hN h • horizontalPoint y hy x)) =
      incoming N g h s y + scatteringEntry N g h s * (y : ℂ)^(1-s) := by
  let E (x : ℝ) := cuspEisenstein N g s (normalizedScaling N hN h • horizontalPoint y hy x)
  have hec : Continuous E := by
    apply (cuspEisenstein_spatial_continuous N hN g s hs).comp
    change Continuous (fun x : ℝ =>
      Matrix.SpecialLinearGroup.mapGL ℝ (normalizedScaling N hN h) • horizontalPoint y hy x)
    apply (continuous_const_smul _).comp
    unfold horizontalPoint
    fun_prop
  have hF (c : ℕ+) : Integrable (outgoingRow N g h c s y) segment :=
    ((row_continuous N g h c s hs y hy).intervalIntegrable 0 1).1
  have ht := integral_tsum_of_summable_integral_norm hF
    (horocycle_row_norms_summable N hN g h s hs y hy)
  have he (x : ℝ) : E x - incoming N g h s y = ∑' c : ℕ+, outgoingRow N g h c s y x := by
    rw [E,parabolic_residue_expansion N hN g h s hs y hy x]
    ring
  have hsum : (∫ x in (0 : ℝ)..1, E x - incoming N g h s y) =
      scatteringDirichletSeries N g h s * actualPowerFourier y 0 s := by
    calc
      _ = ∫ x, ∑' c : ℕ+, outgoingRow N g h c s y x ∂segment := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact integral_congr_ae (Filter.Eventually.of_forall he)
      _ = ∑' c : ℕ+, ∫ x, outgoingRow N g h c s y x ∂segment := ht.symm
      _ = (∑' c : ℕ+, scatteringDirichletTerm N g h s c) * actualPowerFourier y 0 s := by
        rw [← tsum_mul_right]
        apply tsum_congr
        intro c
        simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),segment] using
          positive_row_mean N g h c s hs y hy
      _ = _ := by
        rw [tsum_pnat_eq_tsum_of_eq_zero (f := scatteringDirichletTerm N g h s)
          (by simp [scatteringDirichletTerm]),← scatteringDirichletSeries_eq_tsum]
  rw [intervalIntegral.integral_sub (hec.intervalIntegrable 0 1) intervalIntegrable_const,
    intervalIntegral.integral_const,sub_zero,one_smul,actualPowerFourier_zero y hy s hs] at hsum
  change (∫ x in (0 : ℝ)..1, E x) = _
  unfold scatteringEntry
  linear_combination hsum

/-- The same formula for the genuine meromorphic family subsequently used
at the critical line, on its initial half-plane of absolute convergence. -/
theorem cuspFamily_initial_constant_term (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, cuspFamily N (nativeFrameOrbit N g) s
      (normalizedScaling N hN h • horizontalPoint y hy x)) =
      incoming N g h s y + scatteringEntry N g h s * (y : ℂ)^(1-s) := by
  simp only [cuspFamily_initial N g s hs]
  exact parabolic_constant_term N hN g h s hs y hy

end
end ImbalancedChen.Part3.ActualNativeScatteringConstant20261110
