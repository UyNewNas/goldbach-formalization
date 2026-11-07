import ImbalancedChen.P5ActualHBAuxiliaryGroupLog

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual logarithm numerator is paid by Abel variation, and the real
Mobius cutoff by a literal prefix stop.  Only the two computed untruncated
rough one/Mobius prefix maxima remain.  No bound for either is a premise.
-/
namespace ImbalancedChen.P5Z.ActualHBRolePrefixReduction
noncomputable section
open Classical Finset Set MeasureTheory
open scoped BigOperators Topology
open ImbalancedChen.Part3
open OriginalBetaPrimeSource ActualRoughHeathBrownWords
open ActualHBGroupLogAbelPrefix ActualHBAuxiliaryPrefixes ActualHBAuxiliaryGroupLog
open OriginalGroupLogAbelVariation

def logNumerator (x : ℝ) : ℂ := (Real.log x : ℂ)

theorem logNumerator_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt logNumerator ((1/x : ℝ) : ℂ) x := by
  simpa only [logNumerator,one_div] using (Real.hasDerivAt_log hx.ne').ofReal_comp

theorem logNumerator_deriv_continuousOn {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (deriv logNumerator) (Icc u v) := by
  intro x hx
  have hx0 : 0 < x := hu.trans_le hx.1
  have hh : ContDiffAt ℝ 1 logNumerator x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx0.ne')
  exact (hh.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

theorem logNumerator_variation_le {U u w v : ℝ}
    (hU : 0 < U) (hu1 : 1 ≤ u) (hlo : U ≤ u)
    (huw : u ≤ w) (hwv : w ≤ v) (hhi : v ≤ 2*U) :
    ‖logNumerator w‖ + (∫ x in Ioc u w, ‖deriv logNumerator x‖) ≤
      Real.log v+1 := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have hw0 : 0 < w := hu0.trans_le huw
  have hend : ‖logNumerator w‖ ≤ Real.log v := by
    simp only [logNumerator,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (hu1.trans huw))]
    exact Real.log_le_log hw0 hwv
  have hcont := logNumerator_deriv_continuousOn (v := w) hu0
  have hint : IntegrableOn (fun x => ‖deriv logNumerator x‖) (Ioc u w) :=
    hcont.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hconst : IntegrableOn (fun _ : ℝ => 1/U) (Ioc u w) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hderiv (x : ℝ) (hx : x ∈ Ioc u w) : ‖deriv logNumerator x‖ ≤ 1/U := by
    have hx0 := hu0.trans hx.1
    rw [(logNumerator_hasDerivAt hx0).deriv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hx0)]
    exact one_div_le_one_div_of_le hU (hlo.trans hx.1.le)
  have hvariation : (∫ x in Ioc u w, ‖deriv logNumerator x‖) ≤ 1 := by
    calc
      _ ≤ ∫ _x in Ioc u w, (1/U) :=
        setIntegral_mono_on hint hconst measurableSet_Ioc hderiv
      _ = (w-u)*(1/U) := by
        rw [← intervalIntegral.integral_of_le huw,intervalIntegral.integral_const,
          smul_eq_mul]
      _ ≤ U*(1/U) := mul_le_mul_of_nonneg_right
        (by linarith : w-u ≤ U) (one_div_pos.mpr hU).le
      _ = 1 := by field_simp [hU.ne']
  exact add_le_add hend hvariation

/-- No logarithm is deleted from the actual HB coefficient.  Its numerator
cost is explicit, even when there is also an original group denominator. -/
theorem logarithm_auxiliaryPrefixNorm_le (z y : ℝ)
    {U u v : ℝ} (hU : 0 < U) (hu1 : 1 ≤ u) (hlo : U ≤ u)
    (huv : u ≤ v) (hhi : v ≤ 2*U) (k q b : ℕ) :
    auxiliaryPrefixNorm (actual z y .logarithm) u v k q b ≤
      auxiliaryPrefixNorm (roughOneSlot z) u v k q b * (Real.log v+1) := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have hv0 : 0 ≤ v := hu0.le.trans huv
  have hlog0 : 0 ≤ Real.log v+1 := by
    have := Real.log_nonneg (hu1.trans huv)
    linarith
  apply Finset.sup'_le
  intro h hh
  by_cases hlow : h ≤ Nat.floor u
  · simp only [prefix,Finset.Ioc_eq_empty_of_le hlow,Finset.sum_empty,norm_zero]
    exact mul_nonneg (auxiliaryPrefixNorm_nonneg _ _ _ _ _ _) hlog0
  have huh : u ≤ (h : ℝ) := ((Nat.floor_lt hu0.le).mp (Nat.lt_of_not_ge hlow)).le
  have hhv : (h : ℝ) ≤ v := (Nat.le_floor_iff hv0).mp
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hh))
  have hfd : ∀ x ∈ Icc u (h : ℝ), DifferentiableAt ℝ logNumerator x := by
    intro x hx
    exact (logNumerator_hasDerivAt (hu0.trans_le hx.1)).differentiableAt
  have hfi := (logNumerator_deriv_continuousOn (v := (h : ℝ)) hu0).integrableOn_Icc
  have hAbel := auxiliary_Abel_bound (roughOneSlot z) hu0.le huh
    logNumerator hfd hfi k q b
  have hvariation := logNumerator_variation_le hU hu1 hlo huh hhv hhi
  rw [prefix_mask_eq_auxiliary]
  change ‖auxiliarySWError (Finset.Ioc (Nat.floor u) h)
    (fun n => logNumerator n*roughOneSlot z n) k q b‖ ≤ _
  rw [Nat.floor_natCast] at hAbel
  refine hAbel.trans ?_
  calc
    _ ≤ auxiliaryPrefixNorm (roughOneSlot z) u (h : ℝ) k q b * (Real.log v+1) :=
      mul_le_mul_of_nonneg_left hvariation (auxiliaryPrefixNorm_nonneg _ _ _ _ _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (prefixNorm_mono_upper (coprimeMask (roughOneSlot z) k) u hhv q b) hlog0

def baseRole (z : ℝ) : Role → ℕ → ℂ
  | .mobius => roughMoebiusSlot z
  | .one => roughOneSlot z
  | .logarithm => roughOneSlot z

def numeratorCost (role : Role) (v : ℝ) : ℝ :=
  match role with
  | .logarithm => Real.log v+1
  | _ => 1

/-- Real cutoff, logarithm and every auxiliary k have been reduced to the
two literal untruncated arithmetic slots, with no cancellation assumption. -/
theorem actual_auxiliaryPrefixNorm_le_base (z y : ℝ) (role : Role)
    {U u v : ℝ} (hU : 0 < U) (hu1 : 1 ≤ u) (hlo : U ≤ u)
    (huv : u ≤ v) (hhi : v ≤ 2*U) (k q b : ℕ) :
    auxiliaryPrefixNorm (actual z y role) u v k q b ≤
      auxiliaryPrefixNorm (baseRole z role) u v k q b*numeratorCost role v := by
  cases role with
  | mobius =>
    simpa only [baseRole,numeratorCost,mul_one] using
      truncated_mobius_auxiliaryPrefixNorm_le z y u v k q b
  | one => simp only [baseRole,numeratorCost,actual,mul_one,le_refl]
  | logarithm =>
    exact logarithm_auxiliaryPrefixNorm_le z y hU hu1 hlo huv hhi k q b

theorem mask_one (c : ℕ → ℂ) : coprimeMask c 1 = c := by
  funext n
  simp [coprimeMask]

theorem actual_prefixNorm_le_base (z y : ℝ) (role : Role)
    {U u v : ℝ} (hU : 0 < U) (hu1 : 1 ≤ u) (hlo : U ≤ u)
    (huv : u ≤ v) (hhi : v ≤ 2*U) (q b : ℕ) :
    prefixNorm (actual z y role) u v q b ≤
      prefixNorm (baseRole z role) u v q b*numeratorCost role v := by
  simpa only [auxiliaryPrefixNorm,mask_one] using
    actual_auxiliaryPrefixNorm_le_base z y role hU hu1 hlo huv hhi 1 q b

/-- Final normalized role reduction into the two remaining arithmetic
prefix maxima.  A, H and ell are the SAME original group-log quantities. -/
theorem normalized_role_bound_by_basePrefixes (z y : ℝ) (role : Role)
    {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ 1 Phi)
    {M D U A H ell u v : ℝ} (hM0 : 0 ≤ M) (hD0 : 0 ≤ D)
    (hM : ∀ x ∈ Icc (1 : ℝ) 2, |Phi x| ≤ M)
    (hD : ∀ x ∈ Icc (1 : ℝ) 2, |deriv Phi x| ≤ D)
    (hU : 0 < U) (hA : 0 < A) (hell : 0 < ell)
    (hu1 : 1 ≤ u) (hlo : U ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*U)
    (hfloor : ell ≤ Real.log (A*U)) (hz : 0 < z)
    (t : ℝ) (k q b : ℕ) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError (Finset.Ioc (Nat.floor u) (Nat.floor v))
      (fun n => normalizedProfile Phi t U A H n*actual z y role n) k q b‖ ≤
      (prefixNorm (baseRole z role) u v q b*numeratorCost role v +
        2*roleAmplitude role (Nat.floor v)*(k.divisors.card : ℝ)*(Nat.floor v : ℝ)/z) *
        (|H|⁻¹*((M+D)/ell+M/ell^2)*(1+|t|)) := by
  refine (actual_role_auxiliary_groupLog_bound z y role hPhi hM0 hD0 hM hD
    hU hA hell hlo huv hhi hfloor hz t k q b hk hq).trans ?_
  exact mul_le_mul_of_nonneg_right
    (add_le_add_right (actual_prefixNorm_le_base z y role hU hu1 hlo huv hhi q b) _)
    (by positivity)

end
end ImbalancedChen.P5Z.ActualHBRolePrefixReduction
