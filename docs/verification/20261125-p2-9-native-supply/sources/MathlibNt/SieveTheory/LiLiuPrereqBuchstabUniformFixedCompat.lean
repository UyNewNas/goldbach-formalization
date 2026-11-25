import MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform

/-!
Fixed-cap compatibility extension, extracted from published research
proofs at subfish-zhou/goldbach-lean commit
9d4c3a4010d42aedd9e7231bf94386019cfffccc.
The existing cap-100 providers remain unchanged. Exact source ranges
and proof hashes are recorded in the accompanying overlay manifest.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace LiLiuPrereqBuchstab

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.lean:254-264
private theorem kernel_range {x y t : ℝ} (hy : primeErrorStart ≤ y)
    (hxy : y ^ 2 ≤ x) (ht : t ∈ Icc y (Real.sqrt x)) :
    0 ≤ x ∧ 1 ≤ Real.log t ∧ 2 ≤ Real.log x / Real.log t := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have ht1 := hy1.trans_le ht.1
  have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
  refine ⟨hx0, one_le_log_of_start_le (hy.trans ht.1), ?_⟩
  apply (le_div_iff₀ (Real.log_pos ht1)).2
  have hs : t ^ 2 ≤ x := (Real.le_sqrt (by linarith) hx0).1 ht.2
  have hl := Real.log_le_log (sq_pos_of_pos (by linarith : 0 < t)) hs
  simpa only [Real.log_pow, Nat.cast_ofNat] using hl

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.lean:366-386
private theorem kernel_hasDerivAt_on_band {x y t : ℝ}
    (hy : primeErrorStart ≤ y)
    (ht : t ∈ Ioo y (Real.sqrt x)) (htc : t ≠ Real.exp (Real.log x / 3)) :
    HasDerivAt (buchstabPrimeKernel x) (buchstabPrimeKernelSlope x t) t := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have ht1 : 1 < t := hy1.trans ht.1
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hl0 := Real.log_pos ht1
  have hu : 1 < Real.log x / Real.log t - 1 := by
    have hs : t ^ 2 < x := (Real.lt_sqrt ht0.le).1 ht.2
    have hl := Real.log_lt_log (sq_pos_of_pos ht0) hs
    rw [Real.log_pow] at hl
    have : 2 < Real.log x / Real.log t := (lt_div_iff₀ hl0).2 (by simpa using hl)
    linarith
  apply hasDerivAt_buchstabPrimeKernel ht1 hu
  intro heq
  have hdiv : Real.log x / Real.log t = 3 := by linarith
  have hlog : Real.log t = Real.log x / 3 := by
    have := (div_eq_iff hl0.ne').1 hdiv
    linarith
  exact htc ((Real.exp_log ht0).symm.trans (congrArg Real.exp hlog))

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.lean:715-730
private theorem kernel_endpoint_le {x y t : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x) (ht : t ∈ Icc y (Real.sqrt x)) :
    |buchstabPrimeKernel x t| ≤ x / Real.log y ^ 2 := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hy0 : 0 < y := zero_lt_one.trans hy1
  have ht0 : 0 < t := hy0.trans_le ht.1
  have hly := Real.log_pos hy1
  have hlt := Real.log_pos (hy1.trans_le ht.1)
  have hr := kernel_range hy hxy ht
  have hlyt : Real.log y ≤ t :=
    (le_trans (Real.log_le_sub_one_of_pos hy0) (by linarith)).trans ht.1
  have hden : Real.log y ^ 2 ≤ t * Real.log t := by
    rw [pow_two]
    exact mul_le_mul hlyt (Real.log_le_log hy0 ht.1) hly.le ht0.le
  exact (abs_buchstabPrimeKernel_le hr.1 (hy1.trans_le ht.1) (by linarith [hr.2.2])).trans
    (div_le_div_of_nonneg_left hr.1 (sq_pos_of_pos hly) hden)

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.lean:276-292
theorem abs_shift_mul_buchstabSlope_le_two {u : ℝ} (hu : 1 ≤ u) :
    |(u+1)*buchstabSlope u| ≤ 2 := by
  have hu0 : 0 < u := by linarith
  rw [abs_mul, abs_of_pos (by linarith : 0 < u+1)]
  by_cases h : u ≤ 2
  · rw [buchstabSlope, if_pos h, abs_neg, abs_of_pos (by positivity : 0 < 1/u^2)]
    rw [mul_one_div]
    apply (div_le_iff₀ (sq_pos_of_pos hu0)).mpr
    nlinarith [sq_nonneg (u-1)]
  · have hu2 : 2 < u := lt_of_not_ge h
    have hd : |buchstabSlope u| ≤ 1/(2*u) := by
      rw [buchstabSlope, if_neg h, ← deriv_buchstab hu2]
      exact abs_deriv_buchstab_le hu2
    apply (mul_le_mul_of_nonneg_left hd (by linarith)).trans
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*u)).mpr
    linarith

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.lean:294-323
theorem abs_buchstabPrimeKernelSlope_le_unrestricted {x t : ℝ} (hx : 0 ≤ x)
    (ht : 0 < t) (hl : 1 ≤ Real.log t)
    (hu : 1 ≤ Real.log x / Real.log t - 1) :
    |buchstabPrimeKernelSlope x t| ≤ 4 * (x / (t ^ 2 * Real.log t)) := by
  have hl0 : 0 < Real.log t := by linarith
  have hi : 0 ≤ 1 / Real.log t := by positivity
  have hi1 : 1 / Real.log t ≤ 1 := (div_le_one hl0).2 hl
  have hw : |(1 + 1 / Real.log t) * buchstab (Real.log x / Real.log t - 1)| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (buchstab_nonneg hu)]
    have hm := mul_le_of_le_one_right (by positivity : 0 ≤ 1 + 1 / Real.log t)
      (buchstab_le_one hu)
    linarith
  have hs : |(Real.log x / Real.log t) / Real.log t *
      buchstabSlope (Real.log x / Real.log t - 1)| ≤ 2 := by
    have he : (Real.log x / Real.log t) / Real.log t *
        buchstabSlope (Real.log x / Real.log t - 1) =
        (1/Real.log t)*((Real.log x / Real.log t - 1 + 1)*
          buchstabSlope (Real.log x / Real.log t - 1)) := by ring
    rw [he,abs_mul,abs_of_nonneg hi]
    have hh := mul_le_mul_of_nonneg_left (abs_shift_mul_buchstabSlope_le_two hu) hi
    linarith
  rw [buchstabPrimeKernelSlope, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  have hb := (abs_add_le
    ((1 + 1 / Real.log t) * buchstab (Real.log x / Real.log t - 1))
    ((Real.log x / Real.log t) / Real.log t *
      buchstabSlope (Real.log x / Real.log t - 1))).trans (add_le_add hw hs)
  calc
    _ ≤ (x / (t ^ 2 * Real.log t)) * (2 + 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.lean:326-332
private theorem abs_buchstabPrimeKernelSlope_le_coarse {x t : ℝ} (hx : 0 ≤ x)
    (ht : 0 < t) (hl : 1 ≤ Real.log t)
    (hu : 1 ≤ Real.log x / Real.log t - 1) :
    |buchstabPrimeKernelSlope x t| ≤ 102 * (x / (t ^ 2 * Real.log t)) := by
  apply (abs_buchstabPrimeKernelSlope_le_unrestricted hx ht hl hu).trans
  have hp : 0 ≤ x / (t ^ 2 * Real.log t) := by positivity
  linarith

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.lean:342-358
theorem integrableOn_buchstabPrimeKernelSlope_unrestricted {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x) :
    IntegrableOn (buchstabPrimeKernelSlope x) (Icc y (Real.sqrt x)) := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hc : ContinuousOn (fun t : ℝ => 102 * (x / (t ^ 2 * Real.log t)))
      (Icc y (Real.sqrt x)) := by
    intro t ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans (hy1.trans_le ht.1)).ne'
    have hl0 : Real.log t ≠ 0 := (Real.log_pos (hy1.trans_le ht.1)).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := simp_all)
  apply hc.integrableOn_Icc.mono' (measurable_buchstabPrimeKernelSlope x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs]
  have hr := kernel_range hy hxy ht
  exact abs_buchstabPrimeKernelSlope_le_coarse hr.1 (by linarith [ht.1]) hr.2.1
    (by linarith [hr.2.2])

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.lean:615-653
theorem buchstabPrimeKernel_sum_Ioc_error_le_unrestricted {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x) :
    |(∑ p ∈ primesIoc y (Real.sqrt x), buchstabPrimeKernel x p) -
      x / Real.log x *
        ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)| ≤
      104 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
  have h := prime_abel_log_error_le (c := Real.exp (Real.log x / 3))
    (X := x) (A := 102) hy (Real.le_sqrt_of_sq_le hxy) hx0 (by norm_num)
    (continuousOn_buchstabPrimeKernel x hy1)
    (fun _ ht htc => kernel_hasDerivAt_on_band hy ht htc)
    (integrableOn_buchstabPrimeKernelSlope_unrestricted hy hxy)
    (fun t ht => by
      have hr := kernel_range hy hxy ht
      exact abs_buchstabPrimeKernel_le hr.1 (hy1.trans_le ht.1) (by linarith [hr.2.2]))
    (fun t ht => by
      have hr := kernel_range hy hxy ht
      exact abs_buchstabPrimeKernelSlope_le_coarse hr.1 (by linarith [ht.1]) hr.2.1
        (by linarith [hr.2.2]))
  have he :
      (∫ t in y..Real.sqrt x, buchstabPrimeKernel x t / Real.log t) =
      x / Real.log x *
        ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1) := by
    rw [← mul_integral_buchstab_log_kernel_sqrt hy1 hxy,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [buchstabPrimeKernel]
    ring
  rw [he] at h
  calc
    _ ≤ (102 + 2) * primeErrorEnvelope y * (x / Real.log y) + x / Real.log y ^ 2 := h
    _ ≤ 104 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) := by
      have hp : 0 ≤ x / Real.log y ^ 2 := by positivity
      have heq : 104 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) =
          104 * primeErrorEnvelope y * (x / Real.log y) + 104 * (x / Real.log y ^ 2) := by ring
      rw [heq]
      nlinarith

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.lean:735-786
theorem buchstabPrimeKernel_sum_Ico_error_le_unrestricted {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x) :
    |(∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p) -
      x / Real.log x *
        ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)| ≤
      106 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) := by
  classical
  have hyb : y ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hxy
  have hlow := sum_primesIcc_eq_sum_primesIoc_add (Real.sqrt_nonneg x) (buchstabPrimeKernel x)
    (y := y)
  have hupp := sum_primesIcc_eq_sum_primesIco_add (Real.sqrt_nonneg x) (buchstabPrimeKernel x)
    (a := y)
  have hL :
      |if ∃ p ∈ primesIcc y (Real.sqrt x), (p : ℝ) = y then buchstabPrimeKernel x y else 0| ≤
        x / Real.log y ^ 2 := by
    split_ifs
    · exact kernel_endpoint_le hy hxy ⟨le_rfl, hyb⟩
    · have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
      simp only [abs_zero]
      positivity
  have hB :
      |if ∃ p ∈ primesIcc y (Real.sqrt x), (p : ℝ) = Real.sqrt x then
        buchstabPrimeKernel x (Real.sqrt x) else 0| ≤ x / Real.log y ^ 2 := by
    split_ifs
    · exact kernel_endpoint_le hy hxy ⟨hyb, le_rfl⟩
    · have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
      simp only [abs_zero]
      positivity
  have hH := buchstabPrimeKernel_sum_Ioc_error_le_unrestricted hy hxy
  have hsum :
      |(∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p) -
        x / Real.log x *
          ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)| ≤
      104 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) +
        2 * (x / Real.log y ^ 2) := by
    apply abs_le.mpr
    constructor <;>
      linarith [(abs_le.mp hL).1, (abs_le.mp hL).2,
        (abs_le.mp hB).1, (abs_le.mp hB).2,
        (abs_le.mp hH).1, (abs_le.mp hH).2]
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
  have hly := Real.log_pos hy1
  have hδ := primeErrorEnvelope_nonneg y
  have hnonneg : 0 ≤ primeErrorEnvelope y * (x / Real.log y) := by positivity
  refine hsum.trans ?_
  have he :
      106 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) =
      104 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) +
        2 * (x / Real.log y ^ 2) + 2 * (primeErrorEnvelope y * (x / Real.log y)) := by ring
  rw [he]
  linarith

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.lean:45-48
private theorem bands_pos {y : ℝ} (hy : primeErrorStart ≤ y) :
    0 < y ∧ 0 < Real.log y := by
  exact ⟨by linarith [primeErrorStart_spec.1],
    lt_of_lt_of_le zero_lt_one (one_le_log_of_start_le hy)⟩

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.lean:250-258
private theorem buchstab_main_decomposition {x y : ℝ}
    (hx : 1 < x) (hy : 1 < y) :
    x * buchstab (Real.log x / Real.log y) / Real.log y =
      x / Real.log x + x / Real.log x *
        ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1) := by
  have hlx := (Real.log_pos hx).ne'
  have hly := (Real.log_pos hy).ne'
  field_simp
  ring

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.lean:286-297
private theorem roughCount_base_band_error (n : ℕ) {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hsq : x ≤ y ^ 2) :
    |(roughCount x y : ℝ) -
        x * buchstab (Real.log x / Real.log y) / Real.log y| ≤
      buchstabBandConstant n *
        (buchstabRemainder y * (x / Real.log y) + y / Real.log y) := by
  have hy0 := (bands_pos hy).1
  have hly := (bands_pos hy).2
  have hx0 := hy0.trans_le hyx
  have hr := buchstabRemainder_nonneg hy
  exact (roughCount_base_remainder_error hy hyx hsq).trans
    (mul_le_mul_of_nonneg_right (by linarith [buchstabBandConstant_ge n]) (by positivity))

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.lean:301-385
theorem roughCount_buchstab_band_error_unrestricted (k : ℕ) {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hxy : x ≤ y ^ k) :
    |(roughCount x y : ℝ) -
        x * buchstab (Real.log x / Real.log y) / Real.log y| ≤
      buchstabBandConstant k *
        (buchstabRemainder y * (x / Real.log y) + y / Real.log y) := by
  induction k generalizing x y with
  | zero =>
    apply roughCount_base_band_error 0 hy hyx
    have hy1 : 1 ≤ y := by linarith [primeErrorStart_spec.1]
    exact hxy.trans (pow_le_pow_right₀ hy1 (by omega))
  | succ k ih =>
    by_cases hsq : x ≤ y ^ 2
    · exact roughCount_base_band_error (k + 1) hy hyx hsq
    have hxy2 : y ^ 2 ≤ x := (lt_of_not_ge hsq).le
    have hy0 := (bands_pos hy).1
    have hly := (bands_pos hy).2
    have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
    have hx1 := hy1.trans_le hyx
    have hx0 : 0 < x := hy0.trans_le hyx
    have hyb : y ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hxy2
    have hC : 0 ≤ buchstabBandConstant k := by linarith [buchstabBandConstant_ge k]
    have hr := buchstabRemainder_nonneg hy
    have hcommon : 0 ≤ buchstabRemainder y * (x / Real.log y) := by positivity
    have hrec :
        |(∑ p ∈ primesIco y (Real.sqrt x), (roughCount (x / p) p : ℝ)) -
          ∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p| ≤
        buchstabBandConstant k * (7 * (buchstabRemainder y * (x / Real.log y))) := by
      calc
        _ = |∑ p ∈ primesIco y (Real.sqrt x),
            ((roughCount (x / p) p : ℝ) - buchstabPrimeKernel x p)| := by
          rw [Finset.sum_sub_distrib]
        _ ≤ ∑ p ∈ primesIco y (Real.sqrt x),
            |(roughCount (x / p) p : ℝ) - buchstabPrimeKernel x p| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ primesIco y (Real.sqrt x), buchstabBandConstant k *
            (buchstabRemainder p * ((x / p) / Real.log p) + (p : ℝ) / Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpstart, hpx, hxp⟩ := buchstab_subproblem_band hy hxy hp
          have hp1 : 1 < (p : ℝ) := by linarith [primeErrorStart_spec.1]
          rw [buchstabPrimeKernel_eq_subproblem hx0 hp1]
          exact ih hpstart hpx hxp
        _ = buchstabBandConstant k *
            ∑ p ∈ primesIco y (Real.sqrt x),
              (buchstabRemainder p * ((x / p) / Real.log p) + (p : ℝ) / Real.log p) := by
          rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_buchstabRemainder_errors_le hy hxy2) hC
    have hterminal := roughCount_sqrt_error_le hy hxy2
    have hkernel := buchstabPrimeKernel_sum_Ico_error_le_unrestricted hy hxy2
    change _ ≤ 106 * buchstabRemainder y * (x / Real.log y) at hkernel
    have he :
        (roughCount x y : ℝ) - x * buchstab (Real.log x / Real.log y) / Real.log y =
        ((roughCount x (Real.sqrt x) : ℝ) - x / Real.log x) +
        ((∑ p ∈ primesIco y (Real.sqrt x), (roughCount (x / p) p : ℝ)) -
          ∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p) +
        ((∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p) -
          x / Real.log x *
            ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)) := by
      rw [roughCount_buchstab_sqrt hx1.le hyb, buchstab_main_decomposition hx1 hy1]
      ring
    have htotal :
        |(roughCount x y : ℝ) -
          x * buchstab (Real.log x / Real.log y) / Real.log y| ≤
        (7 * buchstabBandConstant k + 111) *
          (buchstabRemainder y * (x / Real.log y)) := by
      rw [he]
      calc
        _ ≤ |(roughCount x (Real.sqrt x) : ℝ) - x / Real.log x| +
            |(∑ p ∈ primesIco y (Real.sqrt x), (roughCount (x / p) p : ℝ)) -
              ∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p| +
            |(∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p) -
              x / Real.log x *
                ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ 5 * (buchstabRemainder y * (x / Real.log y)) +
            buchstabBandConstant k * (7 * (buchstabRemainder y * (x / Real.log y))) +
            106 * buchstabRemainder y * (x / Real.log y) :=
          add_le_add (add_le_add hterminal hrec) hkernel
        _ = _ := by ring
    apply htotal.trans
    rw [buchstabBandConstant_succ]
    have hboundary : 0 ≤ y / Real.log y := by positivity
    have hconstant := buchstabBandConstant_ge k
    nlinarith

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.lean:19-41
theorem rpow_cutoff_bounds_fixed (M : ℕ) {x u : ℝ} (hx : 1 < x) (hu : 1 ≤ u) (huM : u ≤ (M : ℝ)) :
    1 < x ^ (1 / u) ∧ x ^ (1 / (M : ℝ) : ℝ) ≤ x ^ (1 / u) ∧
      x ^ (1 / u) ≤ x ∧ x ≤ (x ^ (1 / u)) ^ M ∧
      Real.log x / Real.log (x ^ (1 / u)) = u := by
  have hx0 : 0 < x := by linarith
  have hu0 : 0 < u := by linarith
  have hpow : 1 < x ^ (1 / u) := Real.one_lt_rpow hx (one_div_pos.mpr hu0)
  refine ⟨hpow, Real.rpow_le_rpow_of_exponent_le hx.le
    (one_div_le_one_div_of_le hu0 huM), ?_, ?_, ?_⟩
  · calc
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le
        (by simpa using one_div_le_one_div_of_le zero_lt_one hu)
      _ = x := Real.rpow_one x
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    calc
      x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by
        have h : 1 ≤ (M : ℝ) / u := (le_div_iff₀ hu0).2 (by linarith)
        convert h using 1
        ring)
  · rw [Real.log_rpow hx0]
    have hlx := (Real.log_pos hx).ne'
    field_simp

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.lean:63-102
theorem roughCount_relative_band_error_fixed (M : ℕ) {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hxy : x ≤ y ^ M) :
    |(roughCount x y : ℝ) /
        (x * buchstab (Real.log x / Real.log y) / Real.log y) - 1| ≤
      2 * buchstabBandConstant M * (buchstabRemainder y + y / x) := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hx1 : 1 < x := hy1.trans_le hyx
  have hx0 : 0 < x := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hu : 1 ≤ Real.log x / Real.log y := by
    apply (le_div_iff₀ hly).2
    simpa using Real.log_le_log (by linarith : 0 < y) hyx
  have hw := one_half_le_buchstab hu
  have hw0 := buchstab_pos hu
  have hmain : 0 < x * buchstab (Real.log x / Real.log y) / Real.log y := by
    positivity
  have hC : 0 < buchstabBandConstant M := by linarith [buchstabBandConstant_ge M]
  have hr := buchstabRemainder_nonneg hy
  have hA : 0 ≤ buchstabRemainder y + y / x := by positivity
  have he : (roughCount x y : ℝ) /
      (x * buchstab (Real.log x / Real.log y) / Real.log y) - 1 =
      ((roughCount x y : ℝ) -
        x * buchstab (Real.log x / Real.log y) / Real.log y) /
          (x * buchstab (Real.log x / Real.log y) / Real.log y) := by
    field_simp
  rw [he, abs_div, abs_of_pos hmain]
  apply (div_le_iff₀ hmain).2
  apply (roughCount_buchstab_band_error_unrestricted M hy hyx hxy).trans
  have hb : 0 ≤ buchstabBandConstant M *
      (buchstabRemainder y + y / x) * (x / Real.log y) := by positivity
  have hm := mul_le_mul_of_nonneg_left hw hb
  have heq : buchstabBandConstant M *
      (buchstabRemainder y * (x / Real.log y) + y / Real.log y) =
      buchstabBandConstant M * (buchstabRemainder y + y / x) * (x / Real.log y) := by
    field_simp
  rw [heq]
  calc
    _ ≤ 2 * (buchstabBandConstant M * (buchstabRemainder y + y / x) *
        (x / Real.log y) * buchstab (Real.log x / Real.log y)) := by linarith only [hm]
    _ = _ := by ring

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.lean:112-134
theorem roughCount_uniform_error_bound_fixed (M : ℕ) {x u u₀ : ℝ}
    (hx : 1 < x) (hu₀ : 1 < u₀) (hlo : u₀ ≤ u) (hhi : u ≤ (M : ℝ))
    (hstart : primeErrorStart ≤ x ^ (1 / (M : ℝ) : ℝ)) :
    |(roughCount x (x ^ (1 / u)) : ℝ) /
        (u * buchstab u * x / Real.log x) - 1| ≤
      2 * buchstabBandConstant M *
        (buchstabRemainder (x ^ (1 / (M : ℝ) : ℝ)) + x ^ (1 / u₀ - 1)) := by
  have hu : 1 ≤ u := (hu₀.trans_le hlo).le
  have hu0 : 0 < u := by linarith
  have hu₀0 : 0 < u₀ := by linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨_, hlower, hyx, hxy, hlog⟩ := rpow_cutoff_bounds_fixed M hx hu hhi
  have h := roughCount_relative_band_error_fixed M (hstart.trans hlower) hyx hxy
  rw [hlog, rpow_buchstab_main_eq hx hu0] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by
    have hC : 0 < buchstabBandConstant M := by linarith [buchstabBandConstant_ge M]
    positivity)
  apply add_le_add
  · exact antitoneOn_buchstabRemainder hstart (hstart.trans hlower) hlower
  · rw [Real.rpow_sub hx0, Real.rpow_one]
    apply div_le_div_of_nonneg_right _ hx0.le
    exact Real.rpow_le_rpow_of_exponent_le hx.le (one_div_le_one_div_of_le hu₀0 hlo)

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.lean:146-160
theorem tendsto_uniform_buchstab_majorant_fixed (M : ℕ) (hM : 2 ≤ M) {u₀ : ℝ} (hu₀ : 1 < u₀) :
    Tendsto (fun x : ℝ => 2 * buchstabBandConstant M *
      (buchstabRemainder (x ^ (1 / (M : ℝ) : ℝ)) + x ^ (1 / u₀ - 1)))
      atTop (𝓝 0) := by
  have hroot : Tendsto (fun x : ℝ => x ^ (1 / (M : ℝ) : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (one_div_pos.mpr (by exact_mod_cast (show 0 < M by omega)))
  have hexp : 0 < 1 - 1 / u₀ := by
    have hu₀0 : 0 < u₀ := by linarith
    have h := (div_lt_one hu₀0).2 hu₀
    linarith
  have hp : Tendsto (fun x : ℝ => x ^ (1 / u₀ - 1)) atTop (𝓝 0) := by
    rw [show 1 / u₀ - 1 = -(1 - 1 / u₀) by ring]
    exact tendsto_rpow_neg_atTop hexp
  simpa only [Function.comp_apply, add_zero, mul_zero] using
    (tendsto_const_nhds.mul ((tendsto_buchstabRemainder.comp hroot).add hp))

-- Published source: research/wu2008/src/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.lean:170-186
theorem roughCount_uniform_buchstab_fixed (M : ℕ) (hM : 2 ≤ M) {u₀ : ℝ} (hu₀ : 1 < u₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 1 < X ∧ ∀ x ≥ X, ∀ u ∈ Set.Icc u₀ (M : ℝ),
      0 < u * buchstab u * x / Real.log x ∧
      |(roughCount x (x ^ (1 / u)) : ℝ) /
        (u * buchstab u * x / Real.log x) - 1| < ε := by
  have hroot : Tendsto (fun x : ℝ => x ^ (1 / (M : ℝ) : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (one_div_pos.mpr (by exact_mod_cast (show 0 < M by omega)))
  have hsmall := (tendsto_uniform_buchstab_majorant_fixed M hM hu₀).eventually (gt_mem_nhds hε)
  have hlarge := hroot.eventually (eventually_ge_atTop primeErrorStart)
  obtain ⟨X, hX⟩ := eventually_atTop.1 (hsmall.and hlarge)
  refine ⟨max 2 X, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x hx u hu
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hx)
  obtain ⟨hεx, hstart⟩ := hX x ((le_max_right _ _).trans hx)
  exact ⟨buchstab_normalization_pos hx1 ((hu₀.trans_le hu.1).le),
    (roughCount_uniform_error_bound_fixed M hx1 hu₀ hu.1 hu.2 hstart).trans_lt hεx⟩

end LiLiuPrereqBuchstab
