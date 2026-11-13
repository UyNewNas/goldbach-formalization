import ImbalancedChen.Part3OriginalRegularPreKuznetsovProbe
import ImbalancedChen.Part3ActualUnitBandHeightSeeds
import Batteries.Tactic.OpenPrivate

/-! Smooth compact truncations of the actual exponential Poincaré
seed and their Whittaker coordinates. The published logarithmic
cutoff, normalization and physical frequency are reused verbatim. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPreKuznetsovSeed20261113
open Set Filter MeasureTheory Complex
open scoped Topology Distributions ContDiff
open OriginalRegularPreKuznetsovProbe20261113 (density probe exponential_carrier integrable_density)
open ActualUnitBandHeightSeeds20261112 (window window_bounds window_eventually rate rate_pos modulation)
open private exp_half mod_conj from ImbalancedChen.Part3ActualUnitBandHeightSeeds
open ActualLogHorocycleAdjoint20261112 SmoothZeroHeightSeedProfiles20261026b
open ComplexOrderKBridgeSourceOnly OriginalContinuousPoincarePackets20261110
open ActualHalfOrderKWronskianSourceOnly (halfKNormalization)

def halfCarrier (u : ℝ) : ℂ := (Real.exp u:ℂ)*complexOrderK (1/2:ℂ) (Real.exp u)

private theorem smooth_halfCarrier : ContDiff ℝ ∞ halfCarrier := by
  have E : halfCarrier=fun u : ℝ =>
      (Real.exp u:ℂ)*(halfKNormalization*Real.exp (u*(-1/2))*Real.exp (-Real.exp u):ℝ) := by
    funext u
    rw [halfCarrier,exponential_carrier (Real.exp_pos u),Real.exp_mul]
  rw [E]
  fun_prop

def logSeed (C T : ℝ) (k : ℕ) : LogTest where
  toFun := fun u => (window k (u+Real.log C) : ℂ)*halfCarrier (u+Real.log C)*modulation T (u+Real.log C)
  contDiff' := by
    have S : ContDiff ℝ ∞ (fun u : ℝ => halfCarrier (u+Real.log C)) := smooth_halfCarrier.comp (by fun_prop)
    unfold window modulation
    fun_prop
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (-(k:ℝ)-1-Real.log C) ((k:ℝ)+1-Real.log C)))
    intro u hu
    by_contra H
    rcases not_and_or.mp H with l|r
    · have z := Real.smoothTransition.zero_of_nonpos (show (k:ℝ)+1+(u+Real.log C)≤0 by linarith)
      exact hu (by simp [window,z])
    · have z := Real.smoothTransition.zero_of_nonpos (show (k:ℝ)+1-(u+Real.log C)≤0 by linarith)
      exact hu (by simp [window,z])
  tsupport_subset' := subset_univ _

def seed (C T : ℝ) (k : ℕ) : SmoothHeightSeed := fromLog (logSeed C T k)

theorem cutoff_probe (m : ℤ) (hm : m≠0) (T : ℝ) (k : ℕ) (ν : ℂ) :
    orderProbe m (seed (rate m) T k).toFun ν =
      2*∫ q in Ioi (0:ℝ),(window k (Real.log q):ℂ)*density T ν q := by
  let C := rate m
  have hC : 0<C := rate_pos hm
  let V := fun q : ℝ => (window k (Real.log q):ℂ)*density T ν q
  have J := integral_comp_mul_left_Ioi' V 0 hC
  rw [mul_zero,← integral_smul] at J
  change (∫ y in Ioi (0:ℝ), ((y⁻¹)^2 : ℝ) • (star ((seed C T k).toFun y)*orderRadial m ν y))=2*∫ q in Ioi (0:ℝ),V q
  rw [← J,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have qpos := mul_pos hC hy
  have S := fromLog_exp (logSeed C T k) (Real.log y)
  rw [Real.exp_log hy,exp_half y hy] at S
  have sumlog : Real.log y+Real.log C=Real.log (C*y) := by rw [Real.log_mul hC.ne' hy.ne',add_comm]
  have Kstar : star (complexOrderK (1/2:ℂ) (C*y))=complexOrderK (1/2:ℂ) (C*y) := by
    rw [exponential_carrier qpos,Complex.star_def,Complex.conj_ofReal]
  change (fromLog (logSeed C T k)).toFun y=_ at S
  simp only [logSeed,sumlog,halfCarrier,Real.exp_log qpos] at S
  change ((y⁻¹)^2 : ℝ) • (star ((fromLog (logSeed C T k)).toFun y)*_) = _
  simp only [S,orderRadial,← show C=2*Real.pi*|(m:ℝ)| from rfl,star_mul',Kstar,mod_conj T qpos,
    V,density,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv]
  simp only [Complex.star_def,Complex.conj_ofReal]
  have sq := congrArg (fun x : ℝ => (x:ℂ)) (Real.sq_sqrt hy.le)
  push_cast at sq
  let coeff := 2*(C:ℂ)*(window k (Real.log (C*y)):ℂ)*((C:ℂ)*(y:ℂ))^(-((T:ℂ)*I))*
    complexOrderK (1/2:ℂ) (C*y)*complexOrderK ν (C*y)
  field_simp [Complex.ofReal_ne_zero.mpr hy.ne'] <;> first
    | linear_combination (norm := (dsimp only [coeff]; ring)) coeff*sq
    | linear_combination (norm := (dsimp only [coeff]; ring)) (y:ℂ)*coeff*sq

theorem cutoff_limit (m : ℤ) (hm : m≠0) (T : ℝ) {ν : ℂ} (hν : |ν.re|<1/2) :
    Tendsto (fun k => orderProbe m (seed (rate m) T k).toFun ν) atTop (𝓝 (2*probe T ν)) := by
  have h := integrable_density T hν
  simp_rw [cutoff_probe m hm]
  apply tendsto_const_nhds.mul
  apply tendsto_integral_of_dominated_convergence (fun q => ‖density T ν q‖)
  · intro k
    exact ((Complex.continuous_ofReal.measurable.comp (by unfold window; fun_prop : Measurable (fun q : ℝ => window k (Real.log q)))).aestronglyMeasurable.mul h.aestronglyMeasurable)
  · exact h.norm
  · intro k
    exact ae_of_all _ (fun q => by rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (window_bounds _ _).1]; exact mul_le_of_le_one_left (norm_nonneg _) (window_bounds _ _).2)
  · exact ae_of_all _ (fun q => tendsto_const_nhds.congr' ((window_eventually (Real.log q)).mono (fun k H => by simp [H])))

end ImbalancedChen.Part3.OriginalRegularPreKuznetsovSeed20261113
end
