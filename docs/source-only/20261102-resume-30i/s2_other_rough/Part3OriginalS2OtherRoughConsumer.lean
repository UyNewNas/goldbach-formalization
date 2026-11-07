import ImbalancedChen.Part3OriginalS2OtherRoughMean
import ImbalancedChen.Part3OriginalS2SingleZeroPayment
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Insert the source-derived rough moment bound into the ORIGINAL S2 ledger.
H pays the actual single zero and F pays zero-Gram. The remaining shifted
mixed moment is displayed literally, not assumed small or renamed external.
-/
namespace ImbalancedChen.Part3OriginalS2OtherRoughConsumer

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2OtherRoughSource
open ImbalancedChen.Part3OriginalS2OtherRoughCounting
open ImbalancedChen.Part3OriginalS2OtherRoughMean
open ImbalancedChen.Part3OriginalS2SingleZeroPayment
open ImbalancedChen.Part3OriginalS2NativePhysicalRange
open ImbalancedChen.Part3.MediumActualRestorationPayment20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ImbalancedChen.Part3.ActualMediumVarianceAtomBindingSourceOnly
open Classical Finset
open scoped BigOperators

noncomputable section

/-- Actual primitive S2-MT-complete nonzero Poisson source. The only
remaining rough arithmetic is an independently defined finite shifted
moment. Constants and threshold precede the moving original data. -/
theorem exists_original_S2_centered_with_shifted_rough_moment
    (kappa A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 →
        k ∈ originalNumericKeys d (roughZ d.scale) → X ≤ d.scale →
        |primitiveS2 d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k -
            (nativeMT d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re -
            (actualS2NonzeroModes d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re| ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) +
            (48 * d.U / singleZeroY d k) * (1 + Real.log (2 * singleZeroR k)) ^ 3 *
              shiftedRoughMoment d (roughZ d.scale) k := by
  obtain ⟨C, X, hC, hX, hpaid⟩ :=
    exists_original_S2_centered_except_rough_and_nonzero kappa A hA
  refine ⟨C, X, hC, hX, ?_⟩
  intro B sigma c0 d k hd hsigma hc0 hk hx
  have hz : 0 ≤ roughZ d.scale := Real.rpow_nonneg
    (zero_le_one.trans (TransposedPrimitiveUPayment.one_le_scale hd)) _
  have h₁ := hpaid B sigma c0 d k hd hsigma hc0 hk hx
  have h₂ := (Complex.abs_re_le_norm
    (otherRoughCorrection d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k)).trans
      (actual_otherRough_le_shifted_moment hd (roughZ d.scale) hz k)
  have hab (a b : ℝ) : |a| ≤ |a + b| + |b| := by
    calc
      |a| = |(a + b) - b| := by ring_nf
      _ ≤ _ := abs_sub _ _
  exact (hab _ _).trans (add_le_add h₁ h₂)

/-- Direct primitive-versus-full reinstatement, with every unchanged
source term visible. This does not identify smooth-tail payment with
rough-gate removal and does not alter the exact-product ordering. -/
theorem actual_primitive_full_reinstatement_with_shifted_moment
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (hz : 0 ≤ z) (k : Key) :
    |(keyFullRestoredSum d d.scale z k).re -
        primitiveS2 d (strictReceiverCutoff z) (roughY d.scale) k| ≤
      (48 * d.U / singleZeroY d k) * (1 + Real.log (2 * singleZeroR k)) ^ 3 *
        shiftedRoughMoment d z k +
      ‖singleZeroCorrection d (strictReceiverCutoff z) (roughY d.scale) k‖ +
      ‖keyMixedTailSum d d.scale z k‖ := by
  rw [actual_preliminary_S2_receiver_full_identity hd d.scale z hz k]
  have he (s r e t : ℝ) : s + r + e + t - s = (r + e) + t := by ring
  rw [he]
  calc
    _ ≤ |(otherRoughCorrection d (strictReceiverCutoff z) (roughY d.scale) k).re| +
        |(singleZeroCorrection d (strictReceiverCutoff z) (roughY d.scale) k).re| +
        |(keyMixedTailSum d d.scale z k).re| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ ‖otherRoughCorrection d (strictReceiverCutoff z) (roughY d.scale) k‖ +
        ‖singleZeroCorrection d (strictReceiverCutoff z) (roughY d.scale) k‖ +
        ‖keyMixedTailSum d d.scale z k‖ :=
      add_le_add (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _))
        (Complex.abs_re_le_norm _)
    _ ≤ _ := add_le_add_right
      (add_le_add_right (actual_otherRough_le_shifted_moment hd z hz k) _) _

/-- The actual extracted primes lie in the polynomial Shiu range on
occupied original keys. The original y-trim is retained, with no new
restriction on y, sigma or the key family. -/
theorem occupied_common_prime_le_four_fifths
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (hc0 : 0 < c0) (z : ℝ) (k : Key)
    (hk : k ∈ keyBank d (strictReceiverCutoff z) (roughY d.scale))
    (hx : (10 : ℝ) ^ (10 : ℕ) ≤ d.scale)
    (p : ℕ) (hp : p ∈ commonPrimes d z k) :
    (p : ℝ) ≤ d.scale ^ ((4 : ℝ) / 5) := by
  have hxone := TransposedPrimitiveUPayment.one_le_scale hd
  have hxpos := zero_lt_one.trans_le hxone
  have hphys := occupied_keyDR_le_physical
    (show 0 ≤ d.Q2 by linarith [hd.2.2.2.1])
    (show 0 ≤ d.Q3 by linarith [hd.2.2.2.2.1]) hk
  have hphys' : (2 : ℝ) ^ k.d * singleZeroR k ≤ 4 * d.Q2 * d.Q3 := by
    simpa only [keyD, keyR, singleZeroR, Nat.cast_pow, Nat.cast_ofNat] using hphys
  have hD : (1 : ℝ) ≤ 2 ^ k.d := one_le_pow₀ (by norm_num)
  have hR : 0 ≤ singleZeroR k := by unfold singleZeroR; positivity
  have hRle : singleZeroR k ≤ 4 * d.Q2 * d.Q3 := by
    nlinarith [mul_le_mul_of_nonneg_right hD hR]
  have hprod := Q1Q2Q3_lt_scale_seven_tenths hd hsigma
    (residue_ne_zero_of_original_c0 hd hc0)
  have h23 : d.Q2 * d.Q3 < d.scale ^ ((7 : ℝ) / 10) := by
    have hQ1 := hd.2.2.1
    have h23pos : 0 ≤ d.Q2 * d.Q3 := by
      have h2 := hd.2.2.2.1
      have h3 := hd.2.2.2.2.1
      positivity
    nlinarith [mul_le_mul_of_nonneg_right hQ1 h23pos]
  have hpR : (p : ℝ) < 2 * singleZeroR k := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have hhR : (p : ℝ) < (2 : ℝ) ^ (k.w + 1) := by exact_mod_cast hh
    simpa only [singleZeroR, pow_succ, mul_comm] using hhR
  have hten : (10 : ℝ) ≤ d.scale ^ ((1 : ℝ) / 10) := by
    calc
      10 = ((10 : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hx (by norm_num)
  calc
    _ ≤ 8 * d.scale ^ ((7 : ℝ) / 10) := by nlinarith
    _ ≤ d.scale ^ ((1 : ℝ) / 10) * d.scale ^ ((7 : ℝ) / 10) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hxpos.le _)
    _ = _ := by rw [← Real.rpow_add hxpos]; norm_num

/-- Cauchy at the ACTUAL product carrier fixes the remaining shifted
order to 12. The unshifted order-two moment and all its range conditions
are supplied here, not requested from the eventual shifted-Shiu caller. -/
theorem actual_product_mixed_moment_sq_le_shifted_twelve
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (hc0 : 0 < c0) (z : ℝ) (k : Key)
    (hk : k ∈ keyBank d (strictReceiverCutoff z) (roughY d.scale))
    (hx : (10 : ℝ) ^ (10 : ℕ) ≤ d.scale)
    (p : ℕ) (hp : p ∈ commonPrimes d z k) :
    (∑ v ∈ productMultiples d p, tau v * tau (shiftAbs d.residue v) ^ 6) ^ 2 ≤
      (20 * d.scale / p) * (1 + Real.log (5 * d.scale / p)) ^ 3 *
        (∑ v ∈ productMultiples d p, tau (shiftAbs d.residue v) ^ 12) := by
  have hpprime := (Finset.mem_filter.mp hp).2.1
  have hxone := TransposedPrimitiveUPayment.one_le_scale hd
  have hpcap := occupied_common_prime_le_four_fifths hd hsigma hc0 z k hk hx p hp
  have hpP : (p : ℝ) ≤ 5 * d.scale :=
    (hpcap.trans (Real.rpow_le_self_of_one_le hxone (by norm_num))).trans
      (by linarith)
  have hS : ∀ v ∈ productMultiples d p, 0 < v ∧ (v : ℝ) ≤ 5 * d.scale ∧ p ∣ v := by
    intro v hv
    obtain ⟨hv, hdiv, hne⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvlo, hvhi⟩ := Finset.mem_Icc.mp hv
    exact ⟨hvlo, (show (v : ℝ) ≤ Nat.floor (5 * d.scale) by exact_mod_cast hvhi).trans
      (Nat.floor_le (by linarith)), hdiv⟩
  have hmean := multiples_tau_square_mean (productMultiples d p) p hpprime.pos
    (5 * d.scale) hpP hS
  rw [tau_prime hpprime] at hmean
  have hmean' : (∑ v ∈ productMultiples d p, tau v ^ 2) ≤
      (20 * d.scale / p) * (1 + Real.log (5 * d.scale / p)) ^ 3 := by
    convert hmean using 1 <;> ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (productMultiples d p)
    (fun v => tau v) (fun v => tau (shiftAbs d.residue v) ^ 6)
  have hcs' :
      (∑ v ∈ productMultiples d p, tau v * tau (shiftAbs d.residue v) ^ 6) ^ 2 ≤
        (∑ v ∈ productMultiples d p, tau v ^ 2) *
          (∑ v ∈ productMultiples d p, tau (shiftAbs d.residue v) ^ 12) := by
    simpa only [← pow_mul] using hcs
  exact hcs'.trans (mul_le_mul_of_nonneg_right hmean'
    (Finset.sum_nonneg (fun _ _ => by unfold tau; positivity)))

end
end ImbalancedChen.Part3OriginalS2OtherRoughConsumer


