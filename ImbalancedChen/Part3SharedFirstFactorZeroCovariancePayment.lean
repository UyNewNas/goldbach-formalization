import ImbalancedChen.Part3SharedFirstFactorLowConductorAggregate
import ImbalancedChen.Part3SharedFirstFactorSmallResidualHighConductorZero
import ImbalancedChen.Part3SharedFirstFactorLargeResidualZero

/-!
# Uniform payment of the actual shared-first-factor zero covariance

The finite identity first partitions the original complex character sum.
Low conductor contains every residual gcd; high conductor is split at Y.
The physical first factor, both tail labels, auxiliary coprimality masks,
full unit conditions and the primitive main term are unchanged.

The family endpoint pays both original outside L2 factors. Its constants
and scalar threshold precede the varying atom. The only analytic input
is the original family UniformAuxiliarySW, used by the low-conductor parent.
This is a raw zero-covariance payment. The shared U/V terms, nonzero
frequencies and the complete centered energy are separate obligations.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter
open scoped BigOperators Pointwise Topology
open SharedFirstFactorCharacterDictionary

/-- An exact partition of the actual complex sum, before any norm. -/
theorem MediumAtom.sharedFirstFactorZeroCovariance_eq_three_regions
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y R : ℝ) :
    (∑ p ∈ d.primitiveFirstFactorCarrier,
      ((d.q1SliceAtom p).transposedAtom.complexCRTSmoothZeroPart -
        TransposedZeroCovariance.primitiveZeroMain (d.q1SliceAtom p))) =
      d.sharedFirstFactorLowConductorZero R +
        d.sharedFirstFactorSmallResidualHighConductorZero Y R +
          d.sharedFirstFactorLargeResidualHighConductorZero Y R := by
  unfold MediumAtom.sharedFirstFactorLowConductorZero
    MediumAtom.sharedFirstFactorSmallResidualHighConductorZero
    MediumAtom.sharedFirstFactorLargeResidualHighConductorZero
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [d.q1SliceZero_sub_primitive_eq_characters hd hp]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  let C := (Finset.univ : Finset
    (DirichletCharacter ℂ (p * (u.1 * u.2).gcd (v.1 * v.2)))).erase 1
  let f := fun chi : DirichletCharacter ℂ (p * (u.1 * u.2).gcd (v.1 * v.2)) ↦
    auxiliaryCharacterSum d.alphaCarrier d.alpha
      ((u.1 * u.2) / (u.1 * u.2).gcd (v.1 * v.2))
      (p * (u.1 * u.2).gcd (v.1 * v.2)) chi *
    star (auxiliaryCharacterSum d.alphaCarrier d.alpha
      ((v.1 * v.2) / (u.1 * u.2).gcd (v.1 * v.2))
      (p * (u.1 * u.2).gcd (v.1 * v.2)) chi)
  have hpart := Finset.sum_filter_add_sum_filter_not C
    (fun chi ↦ (chi.conductor : ℝ) ≤ R) f
  simp only [not_le] at hpart
  by_cases hD : ((u.1 * u.2).gcd (v.1 * v.2) : ℝ) ≤ Y
  · simp only [if_pos hD, if_neg (not_lt.mpr hD), add_zero]
    rw [← mul_add]
    exact congrArg (fun z : ℂ ↦
      (((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) /
        (((p * (u.1 * u.2).lcm (v.1 * v.2) : ℕ) : ℂ) *
          ((p * (u.1 * u.2).gcd (v.1 * v.2)).totient : ℂ))) *
        (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) * z)
      hpart.symm
  · simp only [if_neg hD, if_pos (lt_of_not_ge hD), add_zero]
    rw [← mul_add]
    exact congrArg (fun z : ℂ ↦
      (((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) /
        (((p * (u.1 * u.2).lcm (v.1 * v.2) : ℕ) : ℂ) *
          ((p * (u.1 * u.2).gcd (v.1 * v.2)).totient : ℂ))) *
        (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) * z)
      hpart.symm

namespace SharedFirstFactorZeroCovariancePayment

private theorem one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  simpa only [one_mul] using mul_le_mul hd.1 hd.2.1 zero_le_one
    (zero_le_one.trans hd.1)

private theorem U_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : d.U ≤ d.scale :=
  le_mul_of_one_le_right (zero_le_one.trans hd.1) hd.2.1

private theorem V_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : d.V ≤ d.scale := by
  change d.V ≤ d.U * d.V
  exact le_mul_of_one_le_left (zero_le_one.trans hd.2.1) hd.1

private theorem factor_scale_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d) :
    d.Q1 ≤ d.scale ∧ d.Q2 ≤ d.scale ∧ d.Q3 ≤ d.scale := by
  rcases hd with ⟨hU, hV, hQ1, hQ2, hQ3, _, _, _, hfirst, hgeometry, _⟩
  have hU0 : 0 ≤ d.U := zero_le_one.trans hU
  have hQ20 : 0 ≤ d.Q2 := zero_le_one.trans hQ2
  have hU2 : 1 ≤ d.U ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hU 2
  have hQ32 : 1 ≤ d.Q3 ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hQ3 2
  have hscale : 1 ≤ d.scale := by
    unfold MediumAtom.scale
    simpa only [one_mul] using mul_le_mul hU hV zero_le_one hU0
  have hUscale : d.U ≤ d.scale := le_mul_of_one_le_right hU0 hV
  have hsmall : d.scale ^ (-sigma) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hscale (by linarith)
  have hpower : d.scale ^ (1 - 8 * sigma) ≤ d.scale := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hscale (show 1 - 8 * sigma ≤ 1 by linarith)
  have hfirstScale : d.Q1 ≤ d.scale := by
    calc
      _ ≤ d.U * d.scale ^ (-sigma) := hfirst.le
      _ ≤ d.U * 1 := mul_le_mul_of_nonneg_left hsmall hU0
      _ = d.U := mul_one _
      _ ≤ d.scale := hUscale
  have hsecond : d.Q2 ≤ d.U ^ 2 * d.Q2 * d.Q3 ^ 2 := by
    calc
      _ ≤ d.U ^ 2 * d.Q2 := le_mul_of_one_le_left hQ20 hU2
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) hQ20) hQ32
  have hU2Q2 : 1 ≤ d.U ^ 2 * d.Q2 := by
    simpa only [one_mul] using mul_le_mul hU2 hQ2 zero_le_one (zero_le_one.trans hU2)
  have hthird : d.Q3 ≤ d.U ^ 2 * d.Q2 * d.Q3 ^ 2 := by
    calc
      _ ≤ d.Q3 ^ 2 := by
        simpa only [mul_one, pow_two] using
          mul_le_mul_of_nonneg_left hQ3 (zero_le_one.trans hQ3)
      _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) hU2Q2
  exact ⟨hfirstScale, hsecond.trans (hgeometry.le.trans hpower),
    hthird.trans (hgeometry.le.trans hpower)⟩

/-- All physical log factors are paid by the original full scale. -/
private theorem log_envelopes
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d)
    (hlog : 1 ≤ Real.log d.scale) :
    (0 ≤ 1 + Real.log (2 * d.V) ∧
      1 + Real.log (2 * d.V) ≤ 10 * Real.log d.scale) ∧
    (0 ≤ 1 + Real.log (4 * d.Q2 * d.Q3) ∧
      1 + Real.log (4 * d.Q2 * d.Q3) ≤ 10 * Real.log d.scale) ∧
    (0 ≤ 1 + Real.log (32 * d.U * d.Q1 * d.Q2 * d.Q3) ∧
      1 + Real.log (32 * d.U * d.Q1 * d.Q2 * d.Q3) ≤ 10 * Real.log d.scale) := by
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hQ2 : 0 < d.Q2 := zero_lt_one.trans_le hd.2.2.2.1
  have hQ3 : 0 < d.Q3 := zero_lt_one.trans_le hd.2.2.2.2.1
  obtain ⟨h1, h2, h3⟩ := factor_scale_bounds hsigma hd
  have hlU := Real.log_le_log hU (U_le_scale hd)
  have hlV := Real.log_le_log hV (V_le_scale hd)
  have hl1 := Real.log_le_log hQ1 h1
  have hl2 := Real.log_le_log hQ2 h2
  have hl3 := Real.log_le_log hQ3 h3
  have hlog2 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog4 : Real.log 4 ≤ 2 := by
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, Nat.cast_ofNat] using
        Real.log_pow (2 : ℝ) 2
    linarith
  have hlog32 : Real.log 32 ≤ 5 := by
    have he : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      simpa only [show (2 : ℝ) ^ (5 : ℕ) = 32 by norm_num, Nat.cast_ofNat] using
        Real.log_pow (2 : ℝ) 5
    linarith
  have hargT : 1 ≤ 4 * d.Q2 * d.Q3 := by
    calc
      1 ≤ 4 * (1 : ℝ) * 1 := by norm_num
      _ ≤ _ := by gcongr <;> first | exact hd.2.2.2.1 | exact hd.2.2.2.2.1
  have hargH : 1 ≤ 32 * d.U * d.Q1 * d.Q2 * d.Q3 := by
    calc
      1 ≤ 32 * (1 : ℝ) * 1 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr <;> first | exact hd.1 | exact hd.2.2.1 | exact hd.2.2.2.1 | exact hd.2.2.2.2.1
  refine ⟨⟨by linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])], ?_⟩,
    ⟨by linarith [Real.log_nonneg hargT], ?_⟩,
    ⟨by linarith [Real.log_nonneg hargH], ?_⟩⟩
  · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hV.ne']
    linarith
  · rw [Real.log_mul (by positivity : 4 * d.Q2 ≠ 0) hQ3.ne',
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hQ2.ne']
    linarith
  · rw [Real.log_mul (by positivity : 32 * d.U * d.Q1 * d.Q2 ≠ 0) hQ3.ne',
      Real.log_mul (by positivity : 32 * d.U * d.Q1 ≠ 0) hQ2.ne',
      Real.log_mul (by positivity : 32 * d.U ≠ 0) hQ1.ne',
      Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hU.ne']
    linarith

private theorem log_product_bound {t L1 L2 : ℝ}
    (ht : 0 ≤ t) (h1 : 0 ≤ L1) (h1t : L1 ≤ 10 * t)
    (h2 : 0 ≤ L2) (h2t : L2 ≤ 10 * t) (e k : ℕ) :
    L1 ^ e * L2 ^ k ≤ 10 ^ (e + k) * t ^ (e + k) := by
  calc
    _ ≤ (10 * t) ^ e * (10 * t) ^ k :=
      mul_le_mul (pow_le_pow_left₀ h1 h1t e) (pow_le_pow_left₀ h2 h2t k)
        (pow_nonneg h2 k) (pow_nonneg (by positivity : 0 ≤ 10 * t) e)
    _ = _ := by simp only [mul_pow, pow_add]; ring

private theorem inverse_log_payment {t : ℝ} (ht : 1 ≤ t) (A : ℝ) (E : ℕ) :
    t ^ E / t ^ (A + (E : ℝ) + 1) ≤ 1 / t ^ A := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hA : 0 < t ^ A := Real.rpow_pos_of_pos ht0 A
  calc
    _ = 1 / (t ^ A * t) := by
      rw [Real.rpow_add ht0 (A + (E : ℝ)) 1,
        Real.rpow_add ht0 A (E : ℝ), Real.rpow_natCast, Real.rpow_one]
      field_simp [ht0.ne', hA.ne', (pow_pos ht0 E).ne']
    _ ≤ _ := one_div_le_one_div_of_le hA (le_mul_of_one_le_right hA.le ht)

private theorem power_log_payment {X t delta A : ℝ} {E : ℕ}
    (hX : 0 < X) (ht : 0 < t) (hpay : t ^ (A + (E : ℝ)) ≤ X ^ delta) :
    t ^ E * X ^ (-delta) ≤ 1 / t ^ A := by
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht A)).mpr
  calc
    _ = (t ^ A * t ^ E) * X ^ (-delta) := by ring
    _ = t ^ (A + (E : ℝ)) * X ^ (-delta) := by
      rw [Real.rpow_add ht A (E : ℝ), Real.rpow_natCast]
    _ ≤ X ^ delta * X ^ (-delta) :=
      mul_le_mul_of_nonneg_right hpay (Real.rpow_nonneg hX.le _)
    _ = 1 := by rw [← Real.rpow_add hX, add_neg_cancel, Real.rpow_zero]

/-- A scalar real threshold, with no convergence premise on the family. -/
private theorem exists_log_power_threshold (P : ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ X : ℝ, x0 ≤ X →
      1 ≤ Real.log X ∧ (Real.log X) ^ P ≤ X ^ delta := by
  have hb := (isLittleO_log_rpow_rpow_atTop P hdelta).bound
    (by norm_num : (0 : ℝ) < 1)
  have hevent : ∀ᶠ X : ℝ in atTop,
      1 ≤ Real.log X ∧ (Real.log X) ^ P ≤ X ^ delta := by
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with X hx hX hlog
    refine ⟨hlog, ?_⟩
    simpa only [Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log X) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ X) _)] using hx
  obtain ⟨x1, hx1⟩ := eventually_atTop.mp hevent
  refine ⟨max 2 x1, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro X hX
  exact hx1 X ((le_max_right 2 x1).trans hX)

private theorem first_factor_relative_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.Q1 / d.U ≤ d.scale ^ (-sigma) := by
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  apply (div_le_iff₀ hU).mpr
  simpa only [mul_comm] using hd.2.2.2.2.2.2.2.2.1.le

/-- The eta cost in both Q1 and Y is retained and paid by the original
strict Q1/U gate. The intermediate exponent is exactly -11 sigma/16. -/
private theorem small_relative_power_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d) :
    d.Q1 ^ (1 + sigma / 16) * (d.scale ^ (sigma / 4)) ^ (1 + sigma / 16) / d.U ≤
      d.scale ^ (-(sigma / 4)) := by
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hX1 := one_le_scale hd
  have hX : 0 < d.scale := zero_lt_one.trans_le hX1
  have hY : 0 < d.scale ^ (sigma / 4) := Real.rpow_pos_of_pos hX _
  have hbase : d.Q1 * d.scale ^ (sigma / 4) / d.U ≤ d.scale ^ (-3 * sigma / 4) := by
    calc
      _ = (d.Q1 / d.U) * d.scale ^ (sigma / 4) := by ring
      _ ≤ d.scale ^ (-sigma) * d.scale ^ (sigma / 4) :=
        mul_le_mul_of_nonneg_right (first_factor_relative_bound hd) hY.le
      _ = _ := by rw [← Real.rpow_add hX]; congr 1; ring
  have hQY : d.Q1 * d.scale ^ (sigma / 4) ≤ d.scale := by
    calc
      _ = (d.Q1 * d.scale ^ (sigma / 4) / d.U) * d.U := by
        field_simp [hU.ne']
      _ ≤ d.scale ^ (-3 * sigma / 4) * d.scale :=
        mul_le_mul hbase (U_le_scale hd) hU.le (Real.rpow_nonneg hX.le _)
      _ = d.scale ^ (-3 * sigma / 4) * d.scale ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = d.scale ^ (1 - 3 * sigma / 4) := by
        rw [← Real.rpow_add hX]
        congr 1; ring
      _ ≤ d.scale := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1
          (show 1 - 3 * sigma / 4 ≤ 1 by linarith)
  calc
    _ = (d.Q1 * d.scale ^ (sigma / 4) / d.U) *
        (d.Q1 * d.scale ^ (sigma / 4)) ^ (sigma / 16) := by
      rw [Real.mul_rpow hQ.le hY.le, Real.rpow_add hQ 1 (sigma / 16),
        Real.rpow_add hY 1 (sigma / 16), Real.rpow_one, Real.rpow_one]
      ring
    _ ≤ d.scale ^ (-3 * sigma / 4) * d.scale ^ (sigma / 16) :=
      mul_le_mul hbase
        (Real.rpow_le_rpow (mul_nonneg hQ.le hY.le) hQY (by linarith))
        (Real.rpow_nonneg (mul_nonneg hQ.le hY.le) _) (Real.rpow_nonneg hX.le _)
    _ = d.scale ^ (-11 * sigma / 16) := by
      rw [← Real.rpow_add hX]
      congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)

private theorem large_relative_power_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d) :
    1 / d.scale ^ (sigma / 4) + d.Q1 / d.U ≤ 2 * d.scale ^ (-(sigma / 4)) := by
  have hX1 := one_le_scale hd
  have hi : 1 / d.scale ^ (sigma / 4) = d.scale ^ (-(sigma / 4)) := by
    rw [Real.rpow_neg (zero_le_one.trans hX1), one_div]
  have hq : d.Q1 / d.U ≤ d.scale ^ (-(sigma / 4)) :=
    (first_factor_relative_bound hd).trans
      (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith))
  rw [hi]
  linarith

end SharedFirstFactorZeroCovariancePayment

open SharedFirstFactorZeroCovariancePayment

/-- Arbitrary logarithmic saving for the original raw zero covariance,
with both actual outside L2 factors and constants uniform in the family. -/
theorem uniformAuxiliarySW_sharedFirstFactorZeroCovariance
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) (hsigma_small : sigma < 1 / 100)
    (hc0 : 0 < c0) (hkappa : 0 ≤ kappa) (hkappa_small : kappa ≤ sigma / 100)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
        ∀ i : ι, x0 ≤ (F i).scale →
          ((∑ m ∈ (F i).betaCarrier, ‖(F i).beta m‖ ^ 2) *
            (∑ p ∈ (F i).primitiveFirstFactorCarrier, ‖(F i).gamma1 p‖ ^ 2)) *
            ‖∑ p ∈ (F i).primitiveFirstFactorCarrier,
              (((F i).q1SliceAtom p).transposedAtom.complexCRTSmoothZeroPart -
                TransposedZeroCovariance.primitiveZeroMain ((F i).q1SliceAtom p))‖ ≤
              C * (F i).scale ^ 2 / (Real.log (F i).scale) ^ A := by
  have _ := And.intro hc0 (And.intro hkappa hkappa_small)
  clear hc0 hkappa hkappa_small
  intro A hA
  let eB : ℕ := (2 ^ B) ^ 2 - 1
  let eta : ℝ := sigma / 16
  let H0 : ℝ := (A + (eB : ℝ) + 21) / (1 - eta)
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have heta1 : eta < 1 := by dsimp only [eta]; linarith
  have hOneEta : 0 < 1 - eta := sub_pos.mpr heta1
  have hH0 : 0 ≤ H0 := by
    exact (div_pos (by positivity : 0 < A + (eB : ℝ) + 21) hOneEta).le
  have hH0eq : H0 * (1 - eta) = A + (eB : ℝ) + 21 := by
    dsimp only [H0]
    field_simp [(sub_pos.mpr heta1).ne']
  have hAraw : 0 < A + (eB : ℝ) + 1 := by positivity
  obtain ⟨CL, hCL, xL, hxL, hLow⟩ :=
    uniformAuxiliarySW_sharedFirstFactorLowConductorZero F B C0 sigma kappa c0
      hsigma hsigma_small hadmissible hSW (A + (eB : ℝ) + 1) H0 hAraw hH0
  obtain ⟨CS, hCS, hSmall⟩ :=
    actual_outside_mul_smallResidualHighConductorZero_bound heta heta1
  obtain ⟨CG, hCG, hLarge⟩ := actual_outside_mul_largeResidualHighConductorZero_bound
  obtain ⟨xP, hxP, hPower⟩ := exists_log_power_threshold
    (A + ((eB + 20 : ℕ) : ℝ)) (show 0 < sigma / 4 by positivity)
  let C : ℝ := 4 * CL * 10 ^ eB + 2 * CS * 10 ^ (eB + 20) +
    2 * CG * 10 ^ (eB + 8)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, max xL xP, hxL.trans_le (le_max_left _ _), ?_⟩
  intro i hx
  let d := F i
  have hd : MediumAdmissible B sigma kappa c0 d := hadmissible i
  have hxL' : xL ≤ d.scale := (le_max_left xL xP).trans hx
  have hxP' : xP ≤ d.scale := (le_max_right xL xP).trans hx
  obtain ⟨hlog, hpay⟩ := hPower d.scale hxP'
  have hX : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  have ht : 0 < Real.log d.scale := zero_lt_one.trans_le hlog
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  let Y : ℝ := d.scale ^ (sigma / 4)
  let R : ℝ := (Real.log d.scale) ^ H0
  have hY : 1 ≤ Y := Real.one_le_rpow (one_le_scale hd) (by positivity)
  have hR : 1 ≤ R := Real.one_le_rpow hlog hH0
  obtain ⟨hLV, hLT, hLH⟩ := log_envelopes hsigma hd hlog
  let W : ℝ := (∑ m ∈ d.betaCarrier, ‖d.beta m‖ ^ 2) *
    (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hLogsSmall := log_product_bound ht.le hLV.1 hLV.2 hLH.1 hLH.2 eB 20
  have hLogsLarge := log_product_bound ht.le hLV.1 hLV.2 hLT.1 hLT.2 eB 8
  have hLowPaid : W * ‖d.sharedFirstFactorLowConductorZero R‖ ≤
      (4 * CL * 10 ^ eB) * d.scale ^ 2 / (Real.log d.scale) ^ A := by
    have hraw := hLow i hxL'
    have hlogV : (1 + Real.log (2 * d.V)) ^ eB ≤
        10 ^ eB * (Real.log d.scale) ^ eB := by
      calc
        _ ≤ (10 * Real.log d.scale) ^ eB := pow_le_pow_left₀ hLV.1 hLV.2 eB
        _ = _ := mul_pow _ _ _
    calc
      _ ≤ (4 * d.V * d.Q1 * (1 + Real.log (2 * d.V)) ^ eB) *
          (CL * d.V * d.U ^ 2 / (d.Q1 * (Real.log d.scale) ^ (A + (eB : ℝ) + 1))) :=
        mul_le_mul (d.sharedFirstFactor_outside_le hd) hraw (norm_nonneg _)
          (mul_nonneg (by positivity) (pow_nonneg hLV.1 eB))
      _ = 4 * CL * d.scale ^ 2 *
          ((1 + Real.log (2 * d.V)) ^ eB / (Real.log d.scale) ^ (A + (eB : ℝ) + 1)) := by
        unfold MediumAtom.scale
        field_simp [hQ.ne', (Real.rpow_pos_of_pos ht (A + (eB : ℝ) + 1)).ne']
      _ ≤ 4 * CL * d.scale ^ 2 *
          ((10 ^ eB * (Real.log d.scale) ^ eB) /
            (Real.log d.scale) ^ (A + (eB : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlogV
          (Real.rpow_nonneg ht.le _)) (by positivity)
      _ = (4 * CL * 10 ^ eB) * d.scale ^ 2 *
          ((Real.log d.scale) ^ eB / (Real.log d.scale) ^ (A + (eB : ℝ) + 1)) := by ring
      _ ≤ (4 * CL * 10 ^ eB) * d.scale ^ 2 * (1 / (Real.log d.scale) ^ A) :=
        mul_le_mul_of_nonneg_left (inverse_log_payment hlog A eB) (by positivity)
      _ = _ := by ring
  have hRpow : R ^ (1 - eta) = (Real.log d.scale) ^ (A + (eB : ℝ) + 21) := by
    dsimp only [R]
    rw [← Real.rpow_mul ht.le, hH0eq]
  have hSmallRelative :
      (Real.log d.scale) ^ (eB + 20) *
        (1 / R ^ (1 - eta) + d.Q1 ^ (1 + eta) * Y ^ (1 + eta) / d.U) ≤
          2 / (Real.log d.scale) ^ A := by
    have hfirst : (Real.log d.scale) ^ (eB + 20) / R ^ (1 - eta) ≤
        1 / (Real.log d.scale) ^ A := by
      rw [hRpow]
      have he : A + ((eB + 20 : ℕ) : ℝ) + 1 = A + (eB : ℝ) + 21 := by
        push_cast
        ring
      simpa only [he] using inverse_log_payment hlog A (eB + 20)
    have hsecond : (Real.log d.scale) ^ (eB + 20) *
        (d.Q1 ^ (1 + eta) * Y ^ (1 + eta) / d.U) ≤ 1 / (Real.log d.scale) ^ A := by
      calc
        _ ≤ (Real.log d.scale) ^ (eB + 20) * d.scale ^ (-(sigma / 4)) :=
          mul_le_mul_of_nonneg_left (small_relative_power_bound hsigma hd) (by positivity)
        _ ≤ _ := power_log_payment hX ht hpay
    calc
      _ = (Real.log d.scale) ^ (eB + 20) / R ^ (1 - eta) +
          (Real.log d.scale) ^ (eB + 20) *
            (d.Q1 ^ (1 + eta) * Y ^ (1 + eta) / d.U) := by ring
      _ ≤ 1 / (Real.log d.scale) ^ A + 1 / (Real.log d.scale) ^ A :=
        add_le_add hfirst hsecond
      _ = _ := by ring
  have hSmallPaid : W * ‖d.sharedFirstFactorSmallResidualHighConductorZero Y R‖ ≤
      (2 * CS * 10 ^ (eB + 20)) * d.scale ^ 2 / (Real.log d.scale) ^ A := by
    calc
      _ ≤ CS * d.scale ^ 2 * (1 + Real.log (2 * d.V)) ^ eB *
          (1 + Real.log (32 * d.U * d.Q1 * d.Q2 * d.Q3)) ^ 20 *
          (1 / R ^ (1 - eta) + d.Q1 ^ (1 + eta) * Y ^ (1 + eta) / d.U) :=
        hSmall B sigma kappa c0 d hd Y R hY hR
      _ = CS * d.scale ^ 2 *
          ((1 + Real.log (2 * d.V)) ^ eB *
            (1 + Real.log (32 * d.U * d.Q1 * d.Q2 * d.Q3)) ^ 20) *
          (1 / R ^ (1 - eta) + d.Q1 ^ (1 + eta) * Y ^ (1 + eta) / d.U) := by ring
      _ ≤ CS * d.scale ^ 2 * (10 ^ (eB + 20) * (Real.log d.scale) ^ (eB + 20)) *
          (1 / R ^ (1 - eta) + d.Q1 ^ (1 + eta) * Y ^ (1 + eta) / d.U) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLogsSmall (by positivity)) (by positivity)
      _ = (CS * 10 ^ (eB + 20)) * d.scale ^ 2 *
          ((Real.log d.scale) ^ (eB + 20) *
            (1 / R ^ (1 - eta) + d.Q1 ^ (1 + eta) * Y ^ (1 + eta) / d.U)) := by ring
      _ ≤ (CS * 10 ^ (eB + 20)) * d.scale ^ 2 * (2 / (Real.log d.scale) ^ A) :=
        mul_le_mul_of_nonneg_left hSmallRelative (by positivity)
      _ = _ := by ring
  have hLargePay : (Real.log d.scale) ^ (A + ((eB + 8 : ℕ) : ℝ)) ≤
      d.scale ^ (sigma / 4) := by
    refine (Real.rpow_le_rpow_of_exponent_le hlog ?_).trans hpay
    push_cast
    linarith
  have hLargeRelative : (Real.log d.scale) ^ (eB + 8) * (1 / Y + d.Q1 / d.U) ≤
      2 / (Real.log d.scale) ^ A := by
    calc
      _ ≤ (Real.log d.scale) ^ (eB + 8) * (2 * d.scale ^ (-(sigma / 4))) :=
        mul_le_mul_of_nonneg_left (large_relative_power_bound hsigma hd) (by positivity)
      _ = 2 * ((Real.log d.scale) ^ (eB + 8) * d.scale ^ (-(sigma / 4))) := by ring
      _ ≤ 2 * (1 / (Real.log d.scale) ^ A) :=
        mul_le_mul_of_nonneg_left (power_log_payment hX ht hLargePay) (by norm_num)
      _ = _ := by ring
  have hLargePaid : W * ‖d.sharedFirstFactorLargeResidualHighConductorZero Y R‖ ≤
      (2 * CG * 10 ^ (eB + 8)) * d.scale ^ 2 / (Real.log d.scale) ^ A := by
    calc
      _ ≤ CG * d.scale ^ 2 * (1 + Real.log (2 * d.V)) ^ eB *
          (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 8 * (1 / Y + d.Q1 / d.U) :=
        hLarge B sigma kappa c0 d hd Y R hY
      _ = CG * d.scale ^ 2 *
          ((1 + Real.log (2 * d.V)) ^ eB * (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 8) *
          (1 / Y + d.Q1 / d.U) := by ring
      _ ≤ CG * d.scale ^ 2 * (10 ^ (eB + 8) * (Real.log d.scale) ^ (eB + 8)) *
          (1 / Y + d.Q1 / d.U) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLogsLarge (by positivity)) (by positivity)
      _ = (CG * 10 ^ (eB + 8)) * d.scale ^ 2 *
          ((Real.log d.scale) ^ (eB + 8) * (1 / Y + d.Q1 / d.U)) := by ring
      _ ≤ (CG * 10 ^ (eB + 8)) * d.scale ^ 2 * (2 / (Real.log d.scale) ^ A) :=
        mul_le_mul_of_nonneg_left hLargeRelative (by positivity)
      _ = _ := by ring
  have htriangle :
      ‖∑ p ∈ d.primitiveFirstFactorCarrier,
        ((d.q1SliceAtom p).transposedAtom.complexCRTSmoothZeroPart -
          TransposedZeroCovariance.primitiveZeroMain (d.q1SliceAtom p))‖ ≤
        ‖d.sharedFirstFactorLowConductorZero R‖ +
          ‖d.sharedFirstFactorSmallResidualHighConductorZero Y R‖ +
            ‖d.sharedFirstFactorLargeResidualHighConductorZero Y R‖ := by
    rw [d.sharedFirstFactorZeroCovariance_eq_three_regions hd Y R]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  calc
    _ ≤ W * (‖d.sharedFirstFactorLowConductorZero R‖ +
        ‖d.sharedFirstFactorSmallResidualHighConductorZero Y R‖ +
          ‖d.sharedFirstFactorLargeResidualHighConductorZero Y R‖) :=
      mul_le_mul_of_nonneg_left htriangle hW
    _ = W * ‖d.sharedFirstFactorLowConductorZero R‖ +
        W * ‖d.sharedFirstFactorSmallResidualHighConductorZero Y R‖ +
          W * ‖d.sharedFirstFactorLargeResidualHighConductorZero Y R‖ := by ring
    _ ≤ (4 * CL * 10 ^ eB) * d.scale ^ 2 / (Real.log d.scale) ^ A +
        (2 * CS * 10 ^ (eB + 20)) * d.scale ^ 2 / (Real.log d.scale) ^ A +
          (2 * CG * 10 ^ (eB + 8)) * d.scale ^ 2 / (Real.log d.scale) ^ A :=
      add_le_add (add_le_add hLowPaid hSmallPaid) hLargePaid
    _ = _ := by dsimp only [C]; ring

end

end ImbalancedChen.Part3
