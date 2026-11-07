import ImbalancedChen.Part3OriginalS2ShiftedTwelve
import ImbalancedChen.RoughSquareException
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual shifted order-12 estimate supplies the second reciprocal
prime factor. A finite integer telescope pays the actual prime bank,
and the result is inserted in the unchanged otherRoughCorrection.
The final arbitrary-log absorption is deliberately not a hypothesis.
-/

namespace ImbalancedChen.Part3OriginalS2RoughPrimeTail

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2ShiftedTwelve
open ImbalancedChen.Part3OriginalS2OtherRoughSource
open ImbalancedChen.Part3OriginalS2OtherRoughCounting
open ImbalancedChen.Part3OriginalS2OtherRoughMean
open ImbalancedChen.Part3OriginalS2OtherRoughConsumer
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalS2SingleZeroPayment
open ImbalancedChen.Part3OriginalS2NativePhysicalRange
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumActualRestorationPayment20261028
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ImbalancedChen.Part3.ActualMediumVarianceAtomBindingSourceOnly

def mixedLogBudget (hShiu : S2PrimitiveShiu) (x : ℝ) : ℝ :=
  20 * (1 + Real.log (5 * x)) ^ 3 +
    5 * (2 : ℝ) ^ (13 : ℕ) * shiftedLogBudget hShiu x

theorem mixedLogBudget_nonneg (hShiu : S2PrimitiveShiu) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ mixedLogBudget hShiu x := by
  have hl : 0 ≤ Real.log (5 * x) := Real.log_nonneg (by linarith)
  have hF := shiftedLogBudget_nonneg hShiu hx
  unfold mixedLogBudget
  positivity

/-- Finite Cauchy is closed with fixed logarithmic costs; no pointwise
divisor subpower factor is introduced into the original logarithmic error. -/
theorem actual_mixed_moment_le
    (hShiu : S2PrimitiveShiu)
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (hc0 : 0 < c0) (hkappa : kappa ≤ 1) (z : ℝ) (k : Key)
    (hk : k ∈ keyBank d (strictReceiverCutoff z) (roughY d.scale))
    (hx : shiuThreshold hShiu ≤ d.scale)
    (p : ℕ) (hp : p ∈ commonPrimes d z k) :
    (∑ v ∈ productMultiples d p, tau v * tau (shiftAbs d.residue v) ^ 6) ≤
      (d.scale / p) * mixedLogBudget hShiu d.scale := by
  have hprime := (Finset.mem_filter.mp hp).2.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
  have hxone := TransposedPrimitiveUPayment.one_le_scale hd
  have hxpos : 0 < d.scale := by linarith
  have hlarge := shiuThreshold_large hShiu hx
  have hcap := occupied_common_prime_le_four_fifths hd hsigma hc0 z k hk hlarge p hp
  have hpx : (p : ℝ) ≤ 5 * d.scale :=
    (hcap.trans (Real.rpow_le_self_of_one_le hxone (by norm_num))).trans (by linarith)
  have hquot1 : 1 ≤ 5 * d.scale / p :=
    (le_div_iff₀ hpR).mpr (by simpa using hpx)
  have hlog : 1 + Real.log (5 * d.scale / p) ≤ 1 + Real.log (5 * d.scale) :=
    add_le_add_left (Real.log_le_log (by positivity)
      (div_le_self (by positivity) hp1)) _
  have hpow := pow_le_pow_left₀
    (show 0 ≤ 1 + Real.log (5 * d.scale / p) by
      linarith [Real.log_nonneg hquot1]) hlog 3
  let S := ∑ v ∈ productMultiples d p, tau v * tau (shiftAbs d.residue v) ^ 6
  let t : ℝ := d.scale / p
  let a : ℝ := 20 * (1 + Real.log (5 * d.scale)) ^ 3
  let b : ℝ := 5 * (2 : ℝ) ^ (13 : ℕ) * shiftedLogBudget hShiu d.scale
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ha : 0 ≤ a := by
    have hl := Real.log_nonneg (show 1 ≤ 5 * d.scale by linarith)
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    have hF := shiftedLogBudget_nonneg hShiu hxone
    dsimp [b]
    positivity
  have hS : 0 ≤ S := by dsimp [S]; unfold tau; positivity
  have hcs := actual_product_mixed_moment_sq_le_shifted_twelve
    hd hsigma hc0 z k hk hlarge p hp
  have hshift := actual_shifted_twelve_le hShiu hd hsigma hc0 hkappa z k hk hx p hp
  have hfirst : (20 * d.scale / p) * (1 + Real.log (5 * d.scale / p)) ^ 3 ≤ t * a := by
    calc
      _ ≤ (20 * d.scale / p) * (1 + Real.log (5 * d.scale)) ^ 3 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by dsimp [t, a]; ring
  have hsecond :
      (∑ v ∈ productMultiples d p, tau (shiftAbs d.residue v) ^ 12) ≤ t * b := by
    convert hshift using 1 <;> dsimp [t, b] <;> ring
  have hsq : S ^ 2 ≤ (t * a) * (t * b) :=
    hcs.trans (mul_le_mul hfirst hsecond
      (Finset.sum_nonneg (fun _ _ => by unfold tau; positivity)) (mul_nonneg ht ha))
  have hab : a * b ≤ (a + b) ^ 2 := by
    nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg ha hb]
  have hsq' : S ^ 2 ≤ (t * (a + b)) ^ 2 := by
    calc
      _ ≤ (t * a) * (t * b) := hsq
      _ = t ^ 2 * (a * b) := by ring
      _ ≤ t ^ 2 * (a + b) ^ 2 := mul_le_mul_of_nonneg_left hab (sq_nonneg _)
      _ = _ := by ring
  have hmajor : 0 ≤ t * (a + b) := mul_nonneg ht (add_nonneg ha hb)
  have hresult : S ≤ t * (a + b) := by nlinarith
  exact hresult

/-- The actual rough-prime bank is a subset of an integer tail. This
uses its strict p>z gate and finite cap; no prime number theorem enters. -/
theorem commonPrimes_reciprocal_square_le (d : MediumAtom) (z : ℝ)
    (hz : 2 ≤ z) (k : Key) :
    (∑ p ∈ commonPrimes d z k, 1 / (p : ℝ) ^ 2) ≤ 2 / z := by
  have hceil : 2 ≤ Nat.ceil z :=
    Nat.add_one_le_ceil_iff.mpr (by simpa using (show 1 < z by linarith))
  have hsub : commonPrimes d z k ⊆ Finset.Icc (Nat.ceil z) (2 ^ (k.w + 1)) := by
    intro p hp
    obtain ⟨hpN, hpprime, hzp, hcop⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hzp.le, (Finset.mem_range.mp hpN).le⟩
  have hrec : 1 / (z - 1) ≤ 2 / z := by
    apply (div_le_div_iff₀ (by linarith : 0 < z - 1) (by linarith : 0 < z)).mpr
    linarith
  calc
    _ ≤ ∑ p ∈ Finset.Icc (Nat.ceil z) (2 ^ (k.w + 1)), 1 / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 / ((Nat.ceil z : ℝ) - 1) := reciprocalSquare_Icc_tail_le _ hceil
    _ ≤ 1 / (z - 1) := div_le_div_of_nonneg_left (by norm_num)
      (by linarith) (sub_le_sub_right (Nat.le_ceil z) 1)
    _ ≤ 2 / z := hrec

theorem shiftedRoughMoment_le_prime_tail
    (hShiu : S2PrimitiveShiu)
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (hc0 : 0 < c0) (hkappa : kappa ≤ 1) (z : ℝ) (hz : 2 ≤ z) (k : Key)
    (hk : k ∈ keyBank d (strictReceiverCutoff z) (roughY d.scale))
    (hx : shiuThreshold hShiu ≤ d.scale) :
    shiftedRoughMoment d z k ≤ (2 * d.scale / z) * mixedLogBudget hShiu d.scale := by
  have hxone := TransposedPrimitiveUPayment.one_le_scale hd
  have hF := mixedLogBudget_nonneg hShiu hxone
  calc
    _ ≤ ∑ p ∈ commonPrimes d z k,
        (1 / (p : ℝ)) * ((d.scale / p) * mixedLogBudget hShiu d.scale) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (actual_mixed_moment_le hShiu hd hsigma hc0 hkappa z k hk hx p hp) (by positivity)
    _ = (d.scale * mixedLogBudget hShiu d.scale) *
        ∑ p ∈ commonPrimes d z k, 1 / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (d.scale * mixedLogBudget hShiu d.scale) * (2 / z) :=
      mul_le_mul_of_nonneg_left (commonPrimes_reciprocal_square_le d z hz k)
        (mul_nonneg (by linarith) hF)
    _ = _ := by ring

theorem occupied_rough_window_le_eight_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (hc0 : 0 < c0) (z y : ℝ) (k : Key) (hk : k ∈ keyBank d z y) :
    2 * singleZeroR k ≤ 8 * d.scale := by
  have hxone := TransposedPrimitiveUPayment.one_le_scale hd
  have hphys := occupied_keyDR_le_physical
    (show 0 ≤ d.Q2 by linarith [hd.2.2.2.1])
    (show 0 ≤ d.Q3 by linarith [hd.2.2.2.2.1]) hk
  have hphys' : (2 : ℝ) ^ k.d * singleZeroR k ≤ 4 * d.Q2 * d.Q3 := by
    simpa only [keyD, keyR, singleZeroR, Nat.cast_pow, Nat.cast_ofNat] using hphys
  have hD : (1 : ℝ) ≤ 2 ^ k.d := one_le_pow₀ (by norm_num)
  have hR : 0 ≤ singleZeroR k := by unfold singleZeroR; positivity
  have hprod := Q1Q2Q3_lt_scale_seven_tenths hd hsigma
    (residue_ne_zero_of_original_c0 hd hc0)
  have h23pos : 0 ≤ d.Q2 * d.Q3 := by
    have h2 := hd.2.2.2.1
    have h3 := hd.2.2.2.2.1
    positivity
  have hpower : d.scale ^ ((7 : ℝ) / 10) ≤ d.scale :=
    Real.rpow_le_self_of_one_le hxone (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hD hR,
    mul_le_mul_of_nonneg_right hd.2.2.1 h23pos]

def roughLogNumerator (hShiu : S2PrimitiveShiu) (x : ℝ) : ℝ :=
  96 * (1 + Real.log (8 * x)) ^ 3 * mixedLogBudget hShiu x

/-- Actual S2 residual with both prime factors and the tail paid.
The remaining scalar is an explicit fixed polynomial in logarithms
divided by z. This theorem does not assume its arbitrary-log decay. -/
theorem actual_otherRough_le_log_over_z
    (hShiu : S2PrimitiveShiu)
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (hc0 : 0 < c0) (hkappa : kappa ≤ 1) (z : ℝ) (hz : 2 ≤ z) (k : Key)
    (hk : k ∈ keyBank d (strictReceiverCutoff z) (roughY d.scale))
    (hx : shiuThreshold hShiu ≤ d.scale) :
    ‖otherRoughCorrection d (strictReceiverCutoff z) (roughY d.scale) k‖ ≤
      fixedDScale d ((2 : ℝ) ^ k.d) * roughLogNumerator hShiu d.scale / z := by
  have hxone := TransposedPrimitiveUPayment.one_le_scale hd
  have hY : 0 < singleZeroY d k := by
    unfold singleZeroY
    have hQ := hd.2.2.1
    positivity
  have hR1 : 1 ≤ singleZeroR k := by
    unfold singleZeroR
    exact one_le_pow₀ (by norm_num)
  have hlog := Real.log_le_log (show 0 < 2 * singleZeroR k by linarith)
    (occupied_rough_window_le_eight_scale hd hsigma hc0 _ _ k hk)
  have hpow := pow_le_pow_left₀
    (show 0 ≤ 1 + Real.log (2 * singleZeroR k) by
      linarith [Real.log_nonneg (show 1 ≤ 2 * singleZeroR k by linarith)])
    (add_le_add_left hlog 1) 3
  have hU : 0 ≤ d.U := by linarith [hd.1]
  have hF := mixedLogBudget_nonneg hShiu hxone
  calc
    _ ≤ (48 * d.U / singleZeroY d k) * (1 + Real.log (2 * singleZeroR k)) ^ 3 *
        shiftedRoughMoment d z k := actual_otherRough_le_shifted_moment hd z (by linarith) k
    _ ≤ (48 * d.U / singleZeroY d k) * (1 + Real.log (2 * singleZeroR k)) ^ 3 *
        ((2 * d.scale / z) * mixedLogBudget hShiu d.scale) := by
      apply mul_le_mul_of_nonneg_left
        (shiftedRoughMoment_le_prime_tail hShiu hd hsigma hc0 hkappa z hz k hk hx)
      have hl := Real.log_nonneg (show 1 ≤ 2 * singleZeroR k by linarith)
      positivity
    _ ≤ (48 * d.U / singleZeroY d k) * (1 + Real.log (8 * d.scale)) ^ 3 *
        ((2 * d.scale / z) * mixedLogBudget hShiu d.scale) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity))
      positivity
    _ = _ := by
      unfold fixedDScale singleZeroY roughLogNumerator MediumAtom.scale
      ring

end
end ImbalancedChen.Part3OriginalS2RoughPrimeTail
