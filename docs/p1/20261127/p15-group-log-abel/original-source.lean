import ImbalancedChen.Part3PrimeMellinProfileVariation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The varying denominator is log(A*y), where A is the product of the OTHER
occurrences in the SAME ORIGINAL HB group. H is the product of the logs
of the OTHER ORIGINAL groups. Neither beta nor a modulus gamma is divided
by its own log. The result below is an explicit Abel variation estimate,
not a Siegel--Walfisz assertion for arbitrary coefficients.
-/
namespace ImbalancedChen.P5Z.OriginalGroupLogAbelVariation
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators Topology
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b

def reciprocalGroupLog (A y : ℝ) : ℝ := (Real.log (A*y))⁻¹

def normalizedProfile (Phi : ℝ → ℝ) (t U A H y : ℝ) : ℂ :=
  (H : ℂ)⁻¹ * physicalProfile Phi t U y * (reciprocalGroupLog A y : ℂ)

theorem normalizedProfile_eq_div (Phi : ℝ → ℝ) (t U A H y : ℝ) :
    normalizedProfile Phi t U A H y =
      physicalProfile Phi t U y / ((H*Real.log (A*y) : ℝ) : ℂ) := by
  simp only [normalizedProfile,reciprocalGroupLog,Complex.ofReal_inv,
    Complex.ofReal_mul,div_eq_mul_inv,mul_inv_rev]
  ring

theorem reciprocalGroupLog_hasDerivAt {A y : ℝ} (hA : 0 < A)
    (hy : 0 < y) (hl : Real.log (A*y) ≠ 0) :
    HasDerivAt (reciprocalGroupLog A)
      (-(1/(y*Real.log (A*y)^2))) y := by
  have hh := ((Real.hasDerivAt_log (mul_pos hA hy).ne').comp y
    ((hasDerivAt_id y).const_mul A)).inv hl
  convert hh using 1 <;>
    simp only [reciprocalGroupLog] <;>
    field_simp [hA.ne',hy.ne',hl] <;> ring

theorem reciprocalGroupLog_contDiffAt {A y : ℝ} (hA : 0 < A)
    (hy : 0 < y) (hl : Real.log (A*y) ≠ 0) :
    ContDiffAt ℝ 1 (reciprocalGroupLog A) y := by
  exact ((Real.contDiffAt_log.mpr (mul_pos hA hy).ne').comp y
    (contDiffAt_const.mul contDiffAt_id)).inv hl

private theorem coordinate_mem {U u v y : ℝ} (hU : 0 < U)
    (hlo : U ≤ u) (hhi : v ≤ 2*U) (hy : y ∈ Icc u v) :
    y/U ∈ Icc (1 : ℝ) 2 := by
  exact ⟨(le_div_iff₀ hU).mpr (by linarith [hy.1]),
    (div_le_iff₀ hU).mpr (hy.2.trans hhi)⟩

theorem log_floor_on_interval {A U ell u v : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hlo : U ≤ u)
    (hfloor : ell ≤ Real.log (A*U)) :
    ∀ y ∈ Icc u v, ell ≤ Real.log (A*y) := by
  intro y hy
  exact hfloor.trans (Real.log_le_log (mul_pos hA hU)
    (mul_le_mul_of_nonneg_left (hlo.trans hy.1) hA.le))

theorem reciprocalGroupLog_bounds {A U ell y : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hell : 0 < ell)
    (hUy : U ≤ y) (hlog : ell ≤ Real.log (A*y)) :
    |reciprocalGroupLog A y| ≤ 1/ell ∧
      |deriv (reciprocalGroupLog A) y| ≤ 1/(U*ell^2) := by
  have hy : 0 < y := hU.trans_le hUy
  have hl : 0 < Real.log (A*y) := hell.trans_le hlog
  constructor
  · simp only [reciprocalGroupLog,abs_inv,abs_of_pos hl]
    simpa only [one_div] using one_div_le_one_div_of_le hell hlog
  · rw [(reciprocalGroupLog_hasDerivAt hA hy hl.ne').deriv,
      abs_neg,abs_of_pos (by positivity : 0 < 1/(y*Real.log (A*y)^2))]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul hUy (pow_le_pow_left₀ hell.le hlog 2)
      (sq_nonneg _) hy.le

theorem normalizedProfile_hasDerivAt {Phi : ℝ → ℝ}
    (hPhi : ContDiff ℝ 1 Phi) (t H : ℝ) {U A y : ℝ}
    (hU : 0 < U) (hA : 0 < A) (hy : 0 < y)
    (hl : Real.log (A*y) ≠ 0) :
    HasDerivAt (normalizedProfile Phi t U A H)
      ((H : ℂ)⁻¹ *
        (deriv (physicalProfile Phi t U) y * (reciprocalGroupLog A y : ℂ) +
          physicalProfile Phi t U y * (deriv (reciprocalGroupLog A) y : ℂ))) y := by
  have hp := physicalProfile_hasDerivAt hPhi t hU hy
  have hr := reciprocalGroupLog_hasDerivAt hA hy hl
  have hp' : HasDerivAt (physicalProfile Phi t U)
      (deriv (physicalProfile Phi t U) y) y := by rwa [hp.deriv]
  have hr' : HasDerivAt (reciprocalGroupLog A)
      (deriv (reciprocalGroupLog A) y) y := by rwa [hr.deriv]
  have hh := (hp'.mul hr'.ofReal_comp).const_mul (H : ℂ)⁻¹
  convert hh using 1 <;> simp only [normalizedProfile] <;> ring

theorem normalizedProfile_contDiffOn {Phi : ℝ → ℝ}
    (hPhi : ContDiff ℝ 1 Phi) (t H : ℝ) {U A ell u v : ℝ}
    (hU : 0 < U) (hA : 0 < A) (hell : 0 < ell) (hlo : U ≤ u)
    (hfloor : ell ≤ Real.log (A*U)) :
    ContDiffOn ℝ 1 (normalizedProfile Phi t U A H) (Icc u v) := by
  intro y hy
  have hy0 : 0 < y := hU.trans_le (hlo.trans hy.1)
  have hlog := log_floor_on_interval hA hU hlo hfloor y hy
  have hr := reciprocalGroupLog_contDiffAt hA hy0 (hell.trans_le hlog).ne'
  have hp : ContDiffAt ℝ 1 (physicalProfile Phi t U) y :=
    ((physicalProfile_contDiffOn hPhi t hU).contDiffAt (isOpen_Ioi.mem_nhds hy0))
  exact ((contDiffAt_const.mul hp).mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp y hr)).contDiffWithinAt

/-- Explicit uniform endpoint-plus-variation cost. The reciprocal logs
of all other original groups remain as |H|^{-1}; zero logs use the exact
totalized zero coefficient. The frequency cost is explicitly 1+|t|. -/
theorem normalizedProfile_variation_le {Phi : ℝ → ℝ}
    (hPhi : ContDiff ℝ 1 Phi) {M D U A H ell u v : ℝ}
    (hM0 : 0 ≤ M) (hD0 : 0 ≤ D)
    (hM : ∀ x ∈ Icc (1 : ℝ) 2, |Phi x| ≤ M)
    (hD : ∀ x ∈ Icc (1 : ℝ) 2, |deriv Phi x| ≤ D)
    (hU : 0 < U) (hA : 0 < A) (hell : 0 < ell)
    (hlo : U ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*U)
    (hfloor : ell ≤ Real.log (A*U)) (t : ℝ) :
    ‖normalizedProfile Phi t U A H v‖ +
      (∫ y in Ioc u v, ‖deriv (normalizedProfile Phi t U A H) y‖) ≤
      |H|⁻¹ * ((M+D)/ell+M/ell^2)*(1+|t|) := by
  have hpoint : ∀ y ∈ Icc u v,
      ‖physicalProfile Phi t U y‖ ≤ M ∧
      ‖deriv (physicalProfile Phi t U) y‖ ≤ (D+M*|t|)/U := by
    intro y hy
    have hy0 := hU.trans_le (hlo.trans hy.1)
    have hnorm := coordinate_mem hU hlo hhi hy
    constructor
    · simpa only [physicalProfile,profile,norm_mul,phase_norm,mul_one,
        Complex.norm_real,Real.norm_eq_abs] using hM _ hnorm
    · rw [(physicalProfile_hasDerivAt hPhi t hU hy0).deriv,norm_smul,
        Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hU)]
      exact (mul_le_mul_of_nonneg_left
        (profile_deriv_norm_le hPhi hM hD t hnorm)
        (one_div_pos.mpr hU).le).trans_eq (by ring)
  have hr : ∀ y ∈ Icc u v,
      |reciprocalGroupLog A y| ≤ 1/ell ∧
      |deriv (reciprocalGroupLog A) y| ≤ 1/(U*ell^2) := by
    intro y hy
    exact reciprocalGroupLog_bounds hA hU hell (hlo.trans hy.1)
      (log_floor_on_interval hA hU hlo hfloor y hy)
  let V : ℝ := |H|⁻¹*((D+M*|t|)/ell+M/ell^2)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hder : ∀ y ∈ Icc u v,
      ‖deriv (normalizedProfile Phi t U A H) y‖ ≤ V/U := by
    intro y hy
    have hy0 := hU.trans_le (hlo.trans hy.1)
    have hl := hell.trans_le (log_floor_on_interval hA hU hlo hfloor y hy)
    rw [(normalizedProfile_hasDerivAt hPhi t H hU hA hy0 hl.ne').deriv,
      norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ |H|⁻¹ *
          (‖deriv (physicalProfile Phi t U) y * (reciprocalGroupLog A y : ℂ)‖ +
           ‖physicalProfile Phi t U y * (deriv (reciprocalGroupLog A) y : ℂ)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ |H|⁻¹ * (((D+M*|t|)/U)*(1/ell) + M*(1/(U*ell^2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact add_le_add
          (mul_le_mul (hpoint y hy).2 (hr y hy).1 (abs_nonneg _) (by positivity))
          (mul_le_mul (hpoint y hy).1 (hr y hy).2 (abs_nonneg _) hM0)
      _ = V/U := by dsimp [V]; ring
  have hend : ‖normalizedProfile Phi t U A H v‖ ≤ |H|⁻¹*(M/ell) := by
    simp only [normalizedProfile,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ |H|⁻¹ * M * (1/ell) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hpoint v ⟨huv,le_rfl⟩).1 (by positivity))
          (hr v ⟨huv,le_rfl⟩).1 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hcont : ContinuousOn (deriv (normalizedProfile Phi t U A H)) (Icc u v) := by
    intro y hy
    have hy0 := hU.trans_le (hlo.trans hy.1)
    have hl := hell.trans_le (log_floor_on_interval hA hU hlo hfloor y hy)
    have hp : ContDiffAt ℝ 1 (physicalProfile Phi t U) y :=
      (physicalProfile_contDiffOn hPhi t hU).contDiffAt (isOpen_Ioi.mem_nhds hy0)
    have hr := reciprocalGroupLog_contDiffAt hA hy0 hl.ne'
    have hh : ContDiffAt ℝ 1 (normalizedProfile Phi t U A H) y :=
      (contDiffAt_const.mul hp).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp y hr)
    exact (hh.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hint : (∫ y in Ioc u v, ‖deriv (normalizedProfile Phi t U A H) y‖) ≤ V := by
    calc
      _ ≤ ∫ _y in Ioc u v, V/U := setIntegral_mono_on
        (hcont.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        measurableSet_Ioc (fun y hy => hder y ⟨hy.1.le,hy.2⟩)
      _ = (v-u)*(V/U) := by
        rw [← intervalIntegral.integral_of_le huv,intervalIntegral.integral_const,smul_eq_mul]
      _ ≤ U*(V/U) := mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hV hU.le)
      _ = V := by field_simp [hU.ne']
  have hpos : 0 ≤ |H|⁻¹*((D/ell)+(M/ell^2))*|t| := by positivity
  dsimp [V] at hint
  nlinarith only [hend,hint,hpos]

end
end ImbalancedChen.P5Z.OriginalGroupLogAbelVariation
