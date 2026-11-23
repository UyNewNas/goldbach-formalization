import ImbalancedChen.Part3ActualNativeScatteringConstant
import ImbalancedChen.Part3ActualEisensteinPositiveCFourier

/-! The geometric Mellin coefficient of each signed nonzero mode on the
actual normalized horocycle. Both integral cusp frames and the primitive
residue condition remain in the sum at every level. -/
namespace ImbalancedChen.Part3.ActualParabolicNonzeroRows20261123

noncomputable section
open Complex Set Matrix MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators
open PowerSeedFourierLaplaceFubini NativeCuspComplexPowerFourier20261027
open NativeCuspComplexPeriodization20261027 ActualEisensteinPositiveCFourier20261025a
open NativeCuspScatteringRowArithmetic20261027 NativeCuspScatteringDirichlet20261027
open ActualParabolicScatteringRows20261110 ActualNativeScatteringConstant20261110
open ActualEisensteinFourierInterchange20261025a NativeAllCuspEisenstein20261026b
open NativeAllCuspEisensteinSpatialConvergence20261026b Gamma0GeneralCuspUnitPeriod20261025a
open ActualYoungCriticalCusps20261110 ActualCharacterCuspExpansion20261110

def geometricTerm (N : ℕ) (g h : SL(2,ℤ)) (s : ℂ) (n : ℤ) (c : ℕ+) : ℂ :=
  denominatorWeight N g h c s *
    ∑ d ∈ residueBlock N g h c, fourierPhase (-n) (residueShift N h c d)

def geometricCoefficient (N : ℕ) (g h : SL(2,ℤ)) (s : ℂ) (n : ℤ) : ℂ :=
  ∑' c : ℕ+, geometricTerm N g h s n c

theorem geometricTerm_norm_summable (N : ℕ) (g h : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re)
    (n : ℤ) : Summable (fun c : ℕ+ => ‖geometricTerm N g h s n c‖) := by
  classical
  apply ((scatteringDirichletTerm_norm_summable N g h s hs).comp_injective
    PNat.coe_injective).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro c
  have hcard : denominatorWeight N g h c s * ((residueBlock N g h c).card : ℂ) =
      scatteringDirichletTerm N g h s c := by
    rw [denominatorWeight, scatteringDirichletTerm, LSeries.term_of_ne_zero c.ne_zero]
    simp only [scatteringCoeffComplex, scatteringDirichletCoeff, Complex.cpow_neg, div_eq_mul_inv]
    ring
  rw [← hcard, geometricTerm, norm_mul, norm_mul, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [fourierPhase_norm, Finset.sum_const, nsmul_eq_mul, mul_one] using
    (norm_sum_le (residueBlock N g h c) (fun d => fourierPhase (-n) (residueShift N h c d)))

theorem positive_row_fourier (N : ℕ) (g h : SL(2,ℤ)) (c : ℕ+) (s : ℂ)
    (hs : 1 < s.re) (n : ℤ) (hn : n ≠ 0) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * outgoingRow N g h c s y x) =
      geometricTerm N g h s n c * nonzeroKExpression y n s := by
  classical
  let a := residueShift N h c
  let P := periodizedComplexPowerSeed y s
  have hpoint (x : ℝ) : fourierPhase n x * outgoingRow N g h c s y x =
      denominatorWeight N g h c s *
        ∑ d ∈ residueBlock N g h c, fourierPhase n x * P (x + a d) := by
    rw [outgoingRow, ← Finset.mul_sum]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (fun d _ => shifted_complex_phase_integrable hy s hs n (a d))]
  simp_rw [show ∀ d, (∫ x in (0 : ℝ)..1, fourierPhase n x * P (x + a d)) =
    fourierPhase (-n) (a d) * nonzeroKExpression y n s from fun d =>
      shifted_periodizedComplexPowerSeed_nonzero hy s hs hn (a d)]
  rw [← Finset.sum_mul, geometricTerm, mul_assoc]

/-- Absolute interchange on the physical horocycle. The incoming orbit
delta has zero projection at every nonzero signed frequency. -/
theorem parabolic_nonzero_fourier (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (n : ℤ) (hn : n ≠ 0) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      cuspEisenstein N g s (normalizedScaling N hN h • horizontalPoint y hy x)) =
        geometricCoefficient N g h s n * nonzeroKExpression y n s := by
  let E x := cuspEisenstein N g s (normalizedScaling N hN h • horizontalPoint y hy x)
  let F (c : ℕ+) (x : ℝ) := fourierPhase n x * outgoingRow N g h c s y x
  have hp : Continuous (fourierPhase n) := by unfold fourierPhase; fun_prop
  have hE : Continuous E := by
    apply (cuspEisenstein_spatial_continuous N hN g s hs).comp
    change Continuous (fun x : ℝ => Matrix.SpecialLinearGroup.mapGL ℝ (normalizedScaling N hN h) •
      horizontalPoint y hy x)
    apply (continuous_const_smul _).comp
    unfold horizontalPoint
    fun_prop
  have hc (c : ℕ+) : Continuous (F c) := hp.mul
    ((continuous_finset_sum _ (fun d _ => (periodizedComplexPowerSeed_continuous hy s hs).comp
      (continuous_id.add_const (residueShift N h c d)))).const_mul _)
  have hnorm : Summable (fun c : ℕ+ => ∫ x in Ioc (0 : ℝ) 1, ‖F c x‖) := by
    simpa only [F, norm_mul, fourierPhase_norm, one_mul] using
      horocycle_row_norms_summable N hN g h s hs y hy
  have hi := integral_tsum_of_summable_integral_norm
    (fun c : ℕ+ => ((hc c).intervalIntegrable 0 1).1) hnorm
  have he (x : ℝ) : fourierPhase n x * E x - fourierPhase n x * incoming N g h s y =
      ∑' c : ℕ+, F c x := by
    simp only [E, F, parabolic_residue_expansion N hN g h s hs y hy x, tsum_mul_left]
    ring
  have H : (∫ x in (0 : ℝ)..1,
        fourierPhase n x * E x - fourierPhase n x * incoming N g h s y) =
      geometricCoefficient N g h s n * nonzeroKExpression y n s := by
    calc
      _ = ∫ x in Ioc (0 : ℝ) 1, ∑' c : ℕ+, F c x := by
        rw [intervalIntegral.integral_of_le zero_le_one]
        exact integral_congr_ae (Filter.Eventually.of_forall he)
      _ = ∑' c : ℕ+, ∫ x in Ioc (0 : ℝ) 1, F c x := hi.symm
      _ = _ := by
        rw [geometricCoefficient, ← tsum_mul_right]
        apply tsum_congr
        intro c
        simpa only [intervalIntegral.integral_of_le zero_le_one, F] using
          positive_row_fourier N g h c s hs n hn y hy
  rwa [intervalIntegral.integral_sub (μ := volume) (f := fun x : ℝ => fourierPhase n x * E x)
      (g := fun x : ℝ => fourierPhase n x * incoming N g h s y)
      ((hp.mul hE).intervalIntegrable 0 1) ((hp.mul_const _).intervalIntegrable 0 1),
    intervalIntegral.integral_mul_const,
    integral_fourierPhase, if_neg hn, zero_mul, sub_zero] at H

theorem native_initial_fourier (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (n : ℤ) (hn : n ≠ 0) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * cuspFamily N (nativeFrameOrbit N g) s
      (normalizedScaling N hN h • horizontalPoint y hy x)) =
        geometricCoefficient N g h s n * nonzeroKExpression y n s := by
  simp only [cuspFamily_initial N g s hs]
  exact parabolic_nonzero_fourier N hN g h s hs n hn y hy

end
end ImbalancedChen.Part3.ActualParabolicNonzeroRows20261123
