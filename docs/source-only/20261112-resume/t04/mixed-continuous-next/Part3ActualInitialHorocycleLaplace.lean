import ImbalancedChen.Part3LogHorocycleLaplaceBoundary
import ImbalancedChen.Part3ActualCompactPacketParameter
import ImbalancedChen.Part3ActualIncompleteEisensteinGram
import ImbalancedChen.Part3RadialScaledSmoothCutoff
import Mathlib.Analysis.Normed.Group.Tannery

/-! Initial unfolding of the continued native column tested against
an actual compact quotient packet. Both limits use the very same
physical zero-mode series with its signed-row factor one half. -/
namespace ImbalancedChen.Part3.ActualInitialHorocycleLaplace20261112

noncomputable section
open Set Filter Topology MeasureTheory Complex UpperHalfPlane Matrix
open scoped UpperHalfPlane MatrixGroups Distributions
open ActualCompactPacketParameter20261112 ActualMarkedHorocycleSupport20261112
open ActualLogHorocycleAdjoint20261112 LogHorocycleLaplaceBoundary20261112
open SmoothZeroHeightSeedProfiles20261026b AllNormalizedCuspAnnihilator20261026b
open ActualIncompleteEisensteinTransform20261110 OriginalFrameZeroSeedMellin20261027
open ActualYoungCriticalCusps20261110 ActualCharacterCuspExpansion20261110
open ActualRegularEisensteinQuotient20261110
open NativeAllCuspEisenstein20261026b NativeAllCuspEisenstein20261027
open NativeOriginalSharpZeroSeedPartition20261027 RadialWeightedCutoffDensity20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open NormalizedCuspCompactFourierFubini20261026b NormalizedCuspCompactPoincare20261026b

private def logTest (s : ℂ) (n : ℕ) : LogTest :=
  ⟨fun u => (cutoff n u : ℂ)*kernel s u,
   (Complex.ofRealCLM.contDiff.comp (cutoff_smooth n)).mul (by fun_prop [kernel]),
   ((cutoff_compact n).comp_left (show ((0 : ℝ) : ℂ)=0 by simp)).mul_right,subset_univ _⟩

private def P (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (s : ℂ) (n : ℕ) :=
  zeroPoincare N g (fromLog (logTest s n)).toHeightSeed

private theorem row_formula (s : ℂ) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    (fromLog (logTest s n)).toFun y =
      (cutoff n (Real.log y) : ℂ)*Complex.exp (s*(Real.log y : ℂ)) := by
  let u := Real.log y
  have X := fromLog_exp (logTest s n) u
  rw [Real.exp_log hy] at X
  rw [X]
  change (Real.exp (u/2) : ℂ)*((cutoff n u : ℂ)*kernel s u) = _
  rw [mul_left_comm,Complex.ofReal_exp,kernel,← Complex.exp_add]
  push_cast
  congr 2 <;> ring

private theorem initial_regular {s : ℂ} (hs : 1 < s.re) : s ≠ 0 ∧ s ≠ 1 := by
  constructor <;> intro e <;> simp [e] at hs

private theorem rows (N : ℕ) [NeZero N] (g : SL(2,ℤ)) {s : ℂ} (hs : 1 < s.re)
    (z : reducedCarrier N) :
    Tendsto (fun n => P N g s n (reducedProjection N z)) atTop
      (𝓝 (column (nativeFrameOrbit N g) s (reducedProjection N z))) ∧
    ∀ n, ‖P N g s n (reducedProjection N z)‖ ≤
      ‖column (nativeFrameOrbit N g) (s.re : ℂ) (reducedProjection N z)‖ := by
  let W := fun n (v : AllowedPair N g) => (cutoff n (Real.log (normalizedBase N g z v.1)) : ℂ)*
    normalizedSeed N g z v.1 s
  have eqP (n : ℕ) : P N g s n (reducedProjection N z) = (1/2 : ℂ)*∑' v,W n v := by
    let ψ := fromLog (logTest s n)
    change zeroPoincare N g ψ.toHeightSeed _ = _
    rw [zeroPoincare,original_sharp_zero_Poincare_projection N _ g ψ.toFun ψ.continuous ψ.compact ψ.positive]
    exact congrArg (fun v : ℂ => (1/2 : ℂ)*v) (tsum_congr (fun v =>
      row_formula s n (normalizedBase_pos N _ g z v.1)))
  have H := rowMass_summable N (NeZero.pos N) g z s.re hs
  have B (n : ℕ) (v : AllowedPair N g) : ‖W n v‖ ≤ rowMass N g z v.1 s.re := by
    rw [W,norm_mul,Complex.norm_real,Real.norm_of_nonneg (cutoff_range n _).1,norm_normalizedSeed_eq_rowMass]
    exact mul_le_of_le_one_left (rowMass_pos _ _ _ _ _).le (cutoff_range n _).2
  have T := tendsto_tsum_of_dominated_convergence H (f := W) (g := fun v => normalizedSeed N g z v.1 s)
    (fun v => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_cutoff_eq_one (Real.log (normalizedBase N g z v.1))] with n hn
      simp only [W,hn,Complex.ofReal_one,one_mul]))
    (Eventually.of_forall B)
  have he (v : ℂ) (hv : 1 < v.re) : column (nativeFrameOrbit N g) v (reducedProjection N z) =
      cuspEisenstein N g v z :=
    (column_up _ (initial_regular hv) z).trans (cuspFamily_initial N g v hv z)
  refine ⟨by simpa only [eqP,he s hs,cuspEisenstein] using T.const_mul (1/2 : ℂ),?_⟩
  intro n
  rw [eqP,he (s.re : ℂ) (by simpa using hs),cuspEisenstein_real_eq_realEnvelope,Complex.norm_real,
    Real.norm_of_nonneg (realEnvelope_nonneg _ _ _ _),norm_mul,show ‖(1/2 : ℂ)‖=(1/2 : ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left (tsum_of_norm_bounded H.hasSum (B n)) (by norm_num)

private theorem height_test (N : ℕ) [NeZero N] (g : SL(2,ℤ)) {V : Gamma0OrbitSpace N → ℂ}
    (hV : MemLp V 2 (carrierPushforward N)) (s : ℂ) (n : ℕ) :
    (∫ q,star (V q)*P N g s n q ∂carrierPushforward N) =
      ∫ u, (cutoff n u : ℂ)*(kernel s u*star (logMean N g V u)) := by
  let f := logTest s n
  let ψ := fromLog f
  let v := hV.toLp V
  let W := frameZeroSeedL2 N (NeZero.pos N) g ψ.toHeightSeed
  have H := congrArg conj (tested_logMean N g v f).2
  rw [← integral_conj,inner_conj_symm] at H
  calc
    _ = inner ℂ v W := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hV.coeFn_toLp,original_frameZeroSeedL2_ae_representative N (NeZero.pos N) g ψ] with q hv hw
      simp only [W,v,RCLike.inner_apply',← Complex.star_def,hv,hw,P,zeroPoincare]
    _ = _ := by
      rw [show inner ℂ v W = _ from H]
      apply integral_congr_ae
      filter_upwards [logMean_congr N g v.memLp hV hV.coeFn_toLp] with u hu
      simp only [f,logTest,map_mul,← Complex.star_def,star_star,hu,mul_assoc]

theorem initial_laplace (N : ℕ) [NeZero N] (g : SL(2,ℤ)) {V : Gamma0OrbitSpace N → ℂ}
    (hV : MemLp V 2 (carrierPushforward N)) (hc : supportedInQuotientCompact N V)
    (hzero : (ℂ ∙ Gamma0ActualConstantMode20261025a.constantL2 N).starProjection (hV.toLp V)=0)
    {s : ℂ} (hs : 1 < s.re) :
    spatial (nativeFrameOrbit N g) V s = laplace (logMean N g V) s := by
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  let a := nativeFrameOrbit N g
  have I := hV.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hH := ((ActualLogHorocycleAdjoint20261112.synthesis N g).adjoint (hV.toLp V)).memLp.congr
    (mean_zero_adjoint N g hV hzero)
  obtain ⟨A,hA⟩ := compact_logMean_cutoff N g hc
  have J := laplace_integrable hH hA (show 1/2 < s.re by linarith)
  have cutmeas (n : ℕ) : AEStronglyMeasurable (fun u => (cutoff n u : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (cutoff_smooth n).continuous).aestronglyMeasurable
  have T := tendsto_integral_of_dominated_convergence (fun u => ‖kernel s u*star (logMean N g V u)‖)
    (fun n => (cutmeas n).mul J.1) J.norm (fun n => ae_of_all _ (fun u => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (cutoff_range n u).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_range n u).2))
    (ae_of_all _ (fun u => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_cutoff_eq_one u] with n hn
      simp only [hn,Complex.ofReal_one,one_mul])))
  have rowAE : ∀ᵐ q ∂carrierPushforward N, Tendsto (fun n => P N g s n q) atTop (𝓝 (column a s q)) ∧
      ∀ n, ‖P N g s n q‖ ≤ ‖column a (s.re : ℂ) q‖ := by
    filter_upwards [reducedProjection_range_ae N] with q hq
    obtain ⟨z,rfl⟩ := hq
    exact rows N g hs z
  obtain ⟨K,hK,HV⟩ := hc
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
    (native_regular_profile a (s.re : ℂ) (initial_regular (by simpa using hs)).1
      (initial_regular (by simpa using hs)).2).1.continuousOn
  have UB (q : Gamma0OrbitSpace N) : ‖V q‖*‖column a (s.re : ℂ) q‖ ≤ max C 0*‖V q‖ := by
    by_cases e : V q=0
    · simp [e]
    · obtain ⟨z,hz,rfl⟩ := HV e
      rw [column_up a (initial_regular (by simpa using hs)),mul_comm (max C 0)]
      exact mul_le_mul_of_nonneg_left ((hC z hz).trans (le_max_left _ _)) (norm_nonneg _)
  have W := tendsto_integral_of_dominated_convergence (μ := carrierPushforward N) (fun q => max C 0*‖V q‖)
    (fun n => hV.1.star.mul (framePoincare_memLp_two N (NeZero.pos N) g 0 _ (fromLog (logTest s n)).continuous
      (fromLog (logTest s n)).compact (fromLog (logTest s n)).positive).1)
    (I.norm.const_mul (max C 0)) (fun n => rowAE.mono (fun q hq => by
      rw [norm_mul,norm_star]
      exact (mul_le_mul_of_nonneg_left (hq.2 n) (norm_nonneg _)).trans (UB q)))
    (rowAE.mono (fun q hq => hq.1.const_mul (star (V q))))
  exact tendsto_nhds_unique W (T.congr (fun n => (height_test N g hV s n).symm))

end
end ImbalancedChen.Part3.ActualInitialHorocycleLaplace20261112
