import ImbalancedChen.Part3LowerSupportedExponentialDamping
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual unshifted exponential damping tends to the SAME raw L2 vector.
The only totalization is max(epsilon,0) outside the positive approach
domain; for EVERY positive epsilon the vector is exactly toLp of the
literal exp(-epsilon*u)*G. The DCT bound is explicit and uniform on
0<epsilon<=1, including arbitrary negative lower support endpoints.
-/

namespace ImbalancedChen.Part3.LowerSupportedDampingL2Limit20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open AngularFourierUnitary20261026b
open HeightMellinUnitary20261026b
open FourierL1L2PlancherelSourceOnly
open LowerSupportedExponentialDamping20261026b

def dampedL2 {G : ℝ → ℂ} {u0 : ℝ} (hG : MemLp G 2 volume)
    (hs : LowerSupported G u0) (ε : ℝ) : RealL2 :=
  (damped_memLp hG hs (le_max_right ε 0)).toLp (damped (max ε 0) G)

theorem dampedL2_ae {G : ℝ → ℂ} {u0 : ℝ} (hG : MemLp G 2 volume)
    (hs : LowerSupported G u0) (ε : ℝ) :
    dampedL2 hG hs ε =ᵐ[volume] damped (max ε 0) G :=
  (damped_memLp hG hs (le_max_right ε 0)).coeFn_toLp

theorem dampedL2_pos {G : ℝ → ℂ} {u0 ε : ℝ} (hG : MemLp G 2 volume)
    (hs : LowerSupported G u0) (hε : 0<ε) :
    dampedL2 hG hs ε=(damped_memLp hG hs hε.le).toLp (damped ε G) := by
  simp only [dampedL2,max_eq_left hε.le]

theorem damping_uniform_bound {u0 ε u : ℝ} (hε : 0≤ε) (hε1 : ε≤1) (hu : u0≤u) :
    ‖(Real.exp (-ε*u) : ℂ)‖≤Real.exp |u0| := by
  have h1 : -ε*u≤-ε*u0 := by nlinarith [mul_nonneg hε (sub_nonneg.mpr hu)]
  have h2 : |ε*u0|≤|u0| := by
    rw [abs_mul,abs_of_nonneg hε]
    nlinarith [abs_nonneg u0]
  have h3 : -ε*u≤|u0| := by nlinarith [neg_le_abs (ε*u0)]
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
    Real.exp_le_exp.mpr h3

theorem damped_difference_square_bound {G : ℝ → ℂ} {u0 : ℝ}
    (hs : LowerSupported G u0) {ε : ℝ} (hε : 0≤ε) (hε1 : ε≤1) :
    ∀ᵐ u ∂volume, ‖damped ε G u-G u‖^2≤(Real.exp |u0|+1)^2*‖G u‖^2 := by
  filter_upwards [hs] with u hu
  by_cases hl : u<u0
  · simp only [damped,hu hl,mul_zero,sub_zero,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero,le_refl]
  · have hd : ‖damped ε G u‖≤Real.exp |u0|*‖G u‖ := by
      rw [damped,norm_mul]
      exact mul_le_mul_of_nonneg_right (damping_uniform_bound hε hε1 (le_of_not_gt hl)) (norm_nonneg _)
    have htri : ‖damped ε G u-G u‖≤(Real.exp |u0|+1)*‖G u‖ := by
      have ht := norm_sub_le (damped ε G u) (G u)
      nlinarith
    have hp := pow_le_pow_left₀ (norm_nonneg _) htri 2
    simpa only [mul_pow] using hp

theorem dampedL2_distance_square {G : ℝ → ℂ} {u0 : ℝ} (hG : MemLp G 2 volume)
    (hs : LowerSupported G u0) (ε : ℝ) :
    ‖dampedL2 hG hs ε-hG.toLp G‖^2 = ∫ u, ‖damped (max ε 0) G u-G u‖^2 := by
  calc
    _ = ∫ u, ‖(dampedL2 hG hs ε-hG.toLp G) u‖^2 := (integral_norm_sq_lp _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (dampedL2 hG hs ε) (hG.toLp G),
        dampedL2_ae hG hs ε,hG.coeFn_toLp] with u hsub hd hraw
      rw [hsub,hd,hraw]

/-- Genuine L2 convergence for epsilon decreasing to zero through the
positive reals. The uniform lower-support DCT is paid, not assumed. -/
theorem dampedL2_tendsto {G : ℝ → ℂ} {u0 : ℝ} (hG : MemLp G 2 volume)
    (hs : LowerSupported G u0) :
    Tendsto (dampedL2 hG hs) (𝓝[>] (0 : ℝ)) (𝓝 (hG.toLp G)) := by
  let C : ℝ := (Real.exp |u0|+1)^2
  have hGi : Integrable (fun u => ‖G u‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0<ε ∧ ε≤1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds]
      with ε hpos hlt
    exact ⟨hpos,hlt.le⟩
  have hm : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun u => ‖damped (max ε 0) G u-G u‖^2) volume :=
    Eventually.of_forall fun ε =>
      ((damped_aestronglyMeasurable hG (max ε 0)).sub hG.aestronglyMeasurable).norm.pow 2
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ u ∂volume,
      ‖‖damped (max ε 0) G u-G u‖^2‖≤C*‖G u‖^2 := by
    filter_upwards [hsmall] with ε hε
    simpa only [max_eq_left hε.1.le,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),C] using
      damped_difference_square_bound hs hε.1.le hε.2
  have hlim : ∀ᵐ u ∂volume, Tendsto
      (fun ε : ℝ => ‖damped (max ε 0) G u-G u‖^2) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro u
    have hc : Continuous (fun ε : ℝ => ‖damped (max ε 0) G u-G u‖^2) := by
      unfold damped
      fun_prop
    simpa only [max_self,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,
      one_mul,sub_self,norm_zero,zero_pow (by norm_num : 2≠0)] using
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hi := tendsto_integral_filter_of_dominated_convergence
    (f := fun _ : ℝ => (0 : ℝ)) (fun u => C*‖G u‖^2) hm hb (hGi.const_mul C) hlim
  have hsq : Tendsto (fun ε => ‖dampedL2 hG hs ε-hG.toLp G‖^2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have he : (fun ε => ‖dampedL2 hG hs ε-hG.toLp G‖^2) =
        (fun ε => ∫ u, ‖damped (max ε 0) G u-G u‖^2) :=
      funext (dampedL2_distance_square hG hs)
    rw [he]
    simpa only [integral_zero] using hi
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hn

theorem angularFourier_dampedL2_tendsto {G : ℝ → ℂ} {u0 : ℝ}
    (hG : MemLp G 2 volume) (hs : LowerSupported G u0) :
    Tendsto (fun ε => angularFourierUnitary (dampedL2 hG hs ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (angularFourierUnitary (hG.toLp G))) :=
  angularFourierUnitary.continuous.continuousAt.tendsto.comp (dampedL2_tendsto hG hs)

theorem angularFourier_dampedL2_ae {G : ℝ → ℂ} {u0 ε : ℝ}
    (hG : MemLp G 2 volume) (hs : LowerSupported G u0) (hε : 0<ε) :
    angularFourierUnitary (dampedL2 hG hs ε) =ᵐ[angularMeasure] angularTransform (damped ε G) := by
  rw [dampedL2_pos hG hs hε]
  exact angularFourierUnitary_toLp_ae (damped_integrable hG hs hε) (damped_memLp hG hs hε.le)

end
end ImbalancedChen.Part3.LowerSupportedDampingL2Limit20261026b
