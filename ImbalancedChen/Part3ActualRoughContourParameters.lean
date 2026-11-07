import ImbalancedChen.PowerErrorBudget

/-!
SOURCE ONLY / UNCOMPILED. Actual rough-SW contour parameter geometry.
The input x is REAL. The one eventual threshold precedes every positive
natural modulus q<=log(x)^B and the literal floor(T+1)+1 height cutoff.
All decay is supplied by mathlib's proved log-rpow/power little-o theorem.
No zero-free region, character estimate, SW saving or Perron assertion is
an input or a conclusion.
-/
namespace ImbalancedChen.Part3.ActualRoughContourParameters20261026b
noncomputable section
open Filter Topology

def roughZ (x : ℝ) : ℝ := x ^ (1 / (Real.log (Real.log x)) ^ 3)
def roughDelta (d x : ℝ) : ℝ := d / Real.log (roughZ x)
def contourT (C x : ℝ) : ℝ := (Real.log x) ^ C
def heightCutoff (q : ℕ) (C x : ℝ) : ℕ := q * (Nat.floor (contourT C x + 1) + 1)
def heightLog (q : ℕ) (C x : ℝ) : ℝ := 1 + Real.log (heightCutoff q C x)
def heightConstant (B C : ℝ) : ℝ := 2 + |Real.log 3| + B + C

theorem roughDelta_eq (d : ℝ) {x : ℝ} (hx : 1 < x)
    (hll : 0 < Real.log (Real.log x)) :
    roughDelta d x = d * (Real.log (Real.log x)) ^ 3 / Real.log x := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hcube : (Real.log (Real.log x)) ^ 3 ≠ 0 := (pow_pos hll 3).ne'
  rw [roughDelta, roughZ, Real.log_rpow hxpos]
  field_simp [hlog, hcube] <;> ring

/-- A real-parameter loglog power is negligible against any positive
power of log x, including all fixed extra (1+loglog x) losses. -/
theorem eventually_loglog_envelope_le
    (d K alpha c : ℝ) (hd : 0 ≤ d) (hK : 0 ≤ K) (ha : 0 < alpha) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      d * (Real.log (Real.log x)) ^ 3 * (1 + Real.log (Real.log x)) ^ K /
        (Real.log x) ^ alpha ≤ c := by
  have hdecay : Tendsto (fun x : ℝ => (d * (2 : ℝ) ^ K) *
      ((Real.log (Real.log x)) ^ (K + 3) / (Real.log x) ^ alpha)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (((isLittleO_log_rpow_rpow_atTop (K + 3) ha).tendsto_div_nhds_zero).comp
        Real.tendsto_log_atTop).const_mul (d * (2 : ℝ) ^ K)
  have hsmall := hdecay.eventually (gt_mem_nhds hc)
  have hlarge : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlarge,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0)] with x hs hll hL
  have hell : 0 < Real.log (Real.log x) := zero_lt_one.trans_le hll
  have hsum : 1 + Real.log (Real.log x) ≤ 2 * Real.log (Real.log x) := by linarith
  have hpow := Real.rpow_le_rpow (by linarith : 0 ≤ 1 + Real.log (Real.log x)) hsum hK
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hell.le] at hpow
  have hcombine : (Real.log (Real.log x)) ^ 3 * (Real.log (Real.log x)) ^ K =
      (Real.log (Real.log x)) ^ (K + 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hell]
    congr 1
    ring
  calc
    _ ≤ d * (Real.log (Real.log x)) ^ 3 *
        ((2 : ℝ) ^ K * (Real.log (Real.log x)) ^ K) / (Real.log x) ^ alpha :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (mul_nonneg hd (pow_nonneg hell.le 3)))
        (Real.rpow_nonneg hL.le _)
    _ = (d * (2 : ℝ) ^ K) *
        ((Real.log (Real.log x)) ^ (K + 3) / (Real.log x) ^ alpha) := by
      rw [← hcombine]
      ring
    _ ≤ c := hs.le

/-- Literal natural-floor height and actual modulus cap give one common
logarithmic upper bound. The modulus is quantified only after x. -/
theorem heightLog_bound {B C x : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hL : 1 ≤ Real.log x) (hll : 0 ≤ Real.log (Real.log x))
    (q : ℕ) (hq : 1 ≤ q) (hqB : (q : ℝ) ≤ (Real.log x) ^ B) :
    1 ≤ heightLog q C x ∧
      heightLog q C x ≤ heightConstant B C * (1 + Real.log (Real.log x)) := by
  have hLp : 0 < Real.log x := zero_lt_one.trans_le hL
  have hT : 1 ≤ contourT C x := Real.one_le_rpow hL hC
  have hT0 : 0 ≤ contourT C x + 1 := by linarith
  have hfloor : (Nat.floor (contourT C x + 1) : ℝ) + 1 ≤ contourT C x + 2 := by
    linarith [Nat.floor_le hT0]
  have hheight : ((Nat.floor (contourT C x + 1) + 1 : ℕ) : ℝ) ≤ 3 * contourT C x := by
    push_cast
    linarith
  have hprod : (heightCutoff q C x : ℝ) ≤ 3 * (Real.log x) ^ (B + C) := by
    calc
      _ = (q : ℝ) * ((Nat.floor (contourT C x + 1) + 1 : ℕ) : ℝ) := by
        simp only [heightCutoff, Nat.cast_mul]
      _ ≤ (Real.log x) ^ B * (3 * contourT C x) :=
        mul_le_mul hqB hheight (Nat.cast_nonneg _) (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [contourT, Real.rpow_add hLp]; ring
  have hcutpos : 0 < heightCutoff q C x :=
    Nat.mul_pos (by omega) (Nat.succ_pos _)
  have hcut1 : (1 : ℝ) ≤ heightCutoff q C x := by
    exact_mod_cast (show 1 ≤ heightCutoff q C x by omega)
  have hlog := Real.log_le_log (by exact_mod_cast hcutpos) hprod
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hLp (B + C)).ne', Real.log_rpow hLp] at hlog
  have hconst : 1 + Real.log 3 ≤ heightConstant B C := by
    dsimp [heightConstant]
    linarith [le_abs_self (Real.log 3)]
  have hBC : B + C ≤ heightConstant B C := by
    dsimp [heightConstant]
    linarith [abs_nonneg (Real.log 3)]
  refine ⟨le_add_of_nonneg_right (Real.log_nonneg hcut1), ?_⟩
  calc
    heightLog q C x ≤ 1 + Real.log 3 + (B + C) * Real.log (Real.log x) := by
      dsimp [heightLog]
      linarith
    _ ≤ heightConstant B C + heightConstant B C * Real.log (Real.log x) :=
      add_le_add hconst (mul_le_mul_of_nonneg_right hBC hll)
    _ = _ := by ring

/-- The actual width clears an inverse ninth conductor-height logarithm,
uniformly before every natural q in its original log-power range. -/
theorem eventually_roughDelta_le_inverse_heightLog_nine
    (B C d c0 : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hd : 0 < d) (hc : 0 < c0) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ B →
      roughDelta d x ≤ c0 / (heightLog q C x) ^ 9 := by
  let A := heightConstant B C
  have hA : 0 < A := by dsimp [A, heightConstant]; linarith [abs_nonneg (Real.log 3)]
  have hpay := eventually_loglog_envelope_le d 9 1 (c0 / A ^ 9)
    hd.le (by norm_num) (by norm_num) (div_pos hc (pow_pos hA 9))
  have hllLarge : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hpay, hllLarge, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with x hpayx hll hx hL
  intro q hq hqB
  have hheight := heightLog_bound hB hC hL (by linarith) q hq hqB
  have hell : 0 < Real.log (Real.log x) := zero_lt_one.trans_le hll
  have hdelta := roughDelta_eq d hx hell
  have hdelta0 : 0 ≤ roughDelta d x := by rw [hdelta]; positivity
  have hden : 0 < heightLog q C x := zero_lt_one.trans_le hheight.1
  have hp : heightLog q C x ^ 9 ≤ A ^ 9 * (1 + Real.log (Real.log x)) ^ 9 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hden.le hheight.2 9
  have hsmall : roughDelta d x * (1 + Real.log (Real.log x)) ^ 9 ≤ c0 / A ^ 9 := by
    rw [hdelta]
    simpa only [Real.rpow_natCast, Real.rpow_one, div_mul_eq_mul_div] using hpayx
  apply (le_div_iff₀ (pow_pos hden 9)).mpr
  calc
    _ ≤ roughDelta d x * (A ^ 9 * (1 + Real.log (Real.log x)) ^ 9) :=
      mul_le_mul_of_nonneg_left hp hdelta0
    _ = (roughDelta d x * (1 + Real.log (Real.log x)) ^ 9) * A ^ 9 := by ring
    _ ≤ c0 := (le_div_iff₀ (pow_pos hA 9)).mp hsmall

/-- The same literal width is smaller than every prescribed subcritical
log-power saving, including a fixed extra loglog-power denominator. -/
theorem eventually_roughDelta_le_logPower_saving
    (d c1 exponent K : ℝ) (hd : 0 < d) (hc : 0 < c1)
    (hexponent : exponent < 1) (hK : 0 ≤ K) :
    ∀ᶠ x : ℝ in atTop,
      roughDelta d x ≤ c1 * (Real.log x) ^ (-exponent) /
        (1 + Real.log (Real.log x)) ^ K := by
  have hpay := eventually_loglog_envelope_le d K (1 - exponent) c1 hd.le hK
    (sub_pos.mpr hexponent) hc
  filter_upwards [hpay, eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)]
    with x hpayx hx hll
  have hell : 0 < Real.log (Real.log x) := zero_lt_one.trans_le hll
  have hL : 0 < Real.log x := Real.log_pos hx
  have hF : 0 < (1 + Real.log (Real.log x)) ^ K := Real.rpow_pos_of_pos (by linarith) _
  have heq : roughDelta d x * (1 + Real.log (Real.log x)) ^ K =
      (d * (Real.log (Real.log x)) ^ 3 * (1 + Real.log (Real.log x)) ^ K /
        (Real.log x) ^ (1 - exponent)) * (Real.log x) ^ (-exponent) := by
    rw [roughDelta_eq d hx hell, Real.rpow_sub hL, Real.rpow_one, Real.rpow_neg]
    field_simp [hL.ne', (Real.rpow_pos_of_pos hL exponent).ne'] <;> ring
  apply (le_div_iff₀ hF).mpr
  rw [heq]
  exact mul_le_mul_of_nonneg_right hpayx (Real.rpow_nonneg hL.le _)

theorem eventually_roughDelta_le_fourteenB_eta
    (B eta d c1 K : ℝ) (hd : 0 < d) (hc : 0 < c1)
    (hgap : 14 * B * eta < 1) (hK : 0 ≤ K) :
    ∀ᶠ x : ℝ in atTop,
      roughDelta d x ≤ c1 * (Real.log x) ^ (-(14 * B * eta)) /
        (1 + Real.log (Real.log x)) ^ K :=
  eventually_roughDelta_le_logPower_saving d c1 (14 * B * eta) K hd hc hgap hK

/-- Both numerical rectangle-width gates hold at one real threshold
chosen before q, with the literal z, delta, T and floor retained. -/
theorem exists_actual_rough_contour_threshold
    (B C d c0 c1 eta K : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hd : 0 < d) (hc0 : 0 < c0) (hc1 : 0 < c1)
    (hgap : 14 * B * eta < 1) (hK : 0 ≤ K) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x →
      1 < roughZ x ∧ 0 < roughDelta d x ∧ 1 ≤ contourT C x ∧
        roughDelta d x = d * (Real.log (Real.log x)) ^ 3 / Real.log x ∧
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ B →
          1 ≤ heightLog q C x ∧
          roughDelta d x ≤ c0 / (heightLog q C x) ^ 9 ∧
          roughDelta d x ≤ c1 * (Real.log x) ^ (-(14 * B * eta)) /
            (1 + Real.log (Real.log x)) ^ K := by
  have hzero := eventually_roughDelta_le_inverse_heightLog_nine B C d c0 hB hC hd hc0
  have hpower := eventually_roughDelta_le_fourteenB_eta B eta d c1 K hd hc1 hgap hK
  have hll : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hzero.and (hpower.and (hll.and hL)))
  refine ⟨max X 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro x hx
  have hlarge := hX x ((le_max_left _ _).trans hx)
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ((le_max_right _ _).trans hx)
  have hell : 0 < Real.log (Real.log x) := zero_lt_one.trans_le hlarge.2.2.1
  have hz : 1 < roughZ x := Real.one_lt_rpow hx1 (one_div_pos.mpr (pow_pos hell 3))
  refine ⟨hz, div_pos hd (Real.log_pos hz), Real.one_le_rpow hlarge.2.2.2 hC,
    roughDelta_eq d hx1 hell, ?_⟩
  intro q hq hqB
  exact ⟨(heightLog_bound hB hC hlarge.2.2.2 hell.le q hq hqB).1,
    hlarge.1 q hq hqB, hlarge.2.1⟩

end
end ImbalancedChen.Part3.ActualRoughContourParameters20261026b
