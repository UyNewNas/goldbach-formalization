import ImbalancedChen.Part3OriginalRegularCutoffModuli

/-! The cutoff diagonal is independent of the Fourier parameter r. Its
limit is the raw π/4 height mass for the very same physical probe. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCutoffDiagonal20261113
open Real Set MeasureTheory Filter
open scoped Topology
open OriginalRegularCutoffPlane20261113 (compact cutoffPair)
open OriginalRegularPreKuznetsovPolar20261113 (physical compact_profile)
open OriginalRegularPreKuznetsovGaussian20261113 (weight)
open OriginalRegularPreKuznetsovFourier20261113 (full_gaussian_diagonal)
open ActualUnitBandHeightSeeds20261112 (window window_bounds window_eventually)
open private rank_pair from ImbalancedChen.Part3OriginalRegularPreKuznetsovPolar

def density (a : ℝ) := π^2*exp (-(4*π)*a)
def height (j : ℕ) := ∫ a in Ioi (0:ℝ),(window j (log (2*π*a)))^2*density a

theorem density_integrable : IntegrableOn density (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (show -(4*π)<0 by linarith only [pi_pos]) 0).const_mul _

theorem density_total : (∫ a in Ioi (0:ℝ),density a)=π/4 := by
  dsimp only [density]
  rw [integral_const_mul,integral_exp_mul_Ioi (show -(4*π)<0 by linarith only [pi_pos]) 0,
    mul_zero,exp_zero]
  field_simp [pi_ne_zero] <;> ring

theorem height_limit : Tendsto height atTop (𝓝 (π/4)) := by
  rw [←density_total]
  apply tendsto_integral_of_dominated_convergence density
  · intro j
    unfold density window
    fun_prop
  · exact density_integrable
  · intro j
    filter_upwards with a
    have h := window_bounds j (log (2*π*a))
    have cap := pow_le_pow_left₀ h.1 h.2 2
    rw [one_pow] at cap
    have d : 0≤density a := by unfold density;positivity
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) d)]
    exact mul_le_of_le_one_left d cap
  · exact ae_of_all _ (fun a => tendsto_const_nhds.congr'
      ((window_eventually (log (2*π*a))).mono (fun j h => by simp only [h,one_pow,one_mul])))

theorem diagonal_value (m n : ℕ+) (j : ℕ) (r : ℝ) :
    OriginalPositiveScalarGeometry20261112.diagonal (cutoffPair j r) 1 m.val (n.val:ℤ)=
      if m=n then (height j:ℂ) else 0 := by
  by_cases eq : m=n
  · subst n
    simp only [OriginalPositiveScalarGeometry20261112.diagonal,eq_self,and_self,if_true]
    rw [height,←integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro a ha
    rw [cutoffPair,show (compact r j).toFun a=
      (window j (log (2*π*a)):ℂ)*physical 0 r a from compact_profile r j ha,star_mul']
    have P := rank_pair ha ha (0:ℝ) r
    rw [div_self ha.ne',log_one] at P
    simp only [Real.rpow_zero,mul_one,Complex.ofReal_zero,mul_zero,Complex.exp_zero] at P
    have e : -(2*π)*(a+a)= -(4*π)*a := by ring
    rw [e] at P
    simp only [←Complex.ofReal_exp] at P
    have point : ((a⁻¹)^2:ℝ) • (physical 0 r a*star (physical 0 r a))=(density a:ℂ) := by
      rw [P]
      dsimp only [density]
      simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv]
      field_simp [Complex.ofReal_ne_zero.mpr ha.ne'] <;> ring
    convert congrArg (fun v : ℂ => ((window j (log (2*π*a)):ℂ)^2)*v) point using 1 <;>
      simp only [Complex.real_smul,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_pow] <;> ring
  · have ne : (m.val:ℤ)≠(n.val:ℤ) := fun h => eq (Subtype.ext (by exact_mod_cast h))
    simp [OriginalPositiveScalarGeometry20261112.diagonal,eq,ne]

theorem averaged_diagonal {K : ℝ} (hp : 0<K) :
    Tendsto (fun j : ℕ => ∫ r : ℝ,weight K r*height j) atTop
      (𝓝 ((π/4)*(sqrt π*K^3/2))) := by
  simp only [integral_mul_const,full_gaussian_diagonal hp]
  simpa only [mul_comm (π/4)] using (height_limit.const_mul (sqrt π*K^3/2))

end ImbalancedChen.Part3.OriginalRegularCutoffDiagonal20261113
end

