import ImbalancedChen.Part3OriginalS2SingleZeroCounting
import ImbalancedChen.Part3MediumActualRestorationPayment
import ImbalancedChen.Part3TransposedPrimitiveUPayment
import ImbalancedChen.Part3ActualMediumVarianceAtomBinding
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Payment of the actual S2 single-zero correction at its original
fixedDScale = M*N^2/(Q1*D), followed by insertion in the existing S2
centering ledger. The other-rough correction and nonzero Poisson source
stay explicit. No estimate for either is smuggled into a premise.
-/
namespace ImbalancedChen.Part3OriginalS2SingleZeroPayment

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2SingleZeroCounting
open ImbalancedChen.Part3OriginalSingleZeroPolynomialTau
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
open ImbalancedChen.Part3OriginalS2ActualTailTransfer
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3OriginalS2NativePhysicalRange
open ImbalancedChen.Part3OriginalS2ActualCenteringLedger
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2NativeZeroGramBudget
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3.MediumPrimitivePsiSource20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumActualRestorationPayment20261028
open ImbalancedChen.Part3.MediumNativePrincipalSource20261028
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.ActualMediumVarianceAtomBindingSourceOnly
open Classical Finset Filter
open scoped BigOperators

noncomputable section

/-- The coefficient envelope, exact-product count, and reciprocal
totient cost are all discharged, on the unchanged actual S2 source.
The constant depends only on the fixed residue exponent and precision. -/
theorem exists_actual_S2_singleZero_subpower (kappa epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom) (k : Key) (z : ℝ),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 → 0 ≤ z →
        (10 : ℝ) ^ (10 : ℕ) ≤ d.scale →
        ‖singleZeroCorrection d (strictReceiverCutoff z) (roughY d.scale) k‖ ≤
          C * (singleZeroR k * d.U * d.scale ^ epsilon) := by
  let eta := epsilon / 4
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨C0, hC0, hbound⟩ := exists_uniform_polynomial_tau kappa eta heta
  have hC0pos : 0 < C0 := zero_lt_one.trans_le hC0
  refine ⟨24 * C0 ^ (4 : ℕ), by positivity, ?_⟩
  intro B sigma c0 d k z hd hsigma hc0 hz hlarge
  have hx : 1 ≤ d.scale := TransposedPrimitiveUPayment.one_le_scale hd
  have hxpos : 0 < d.scale := zero_lt_one.trans_le hx
  have hxK : d.scale ≤ d.scale ^ (max 1 (1 + kappa)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (le_max_left 1 (1 + kappa))
  let H := Nat.floor (C0 * d.scale ^ eta)
  have hH : (H : ℝ) ≤ C0 * d.scale ^ eta := Nat.floor_le (by positivity)
  have ha := Nat.pos_of_ne_zero
    (Int.natAbs_ne_zero.mpr (residue_ne_zero_of_original_c0 hd hc0))
  have haK : (d.residue.natAbs : ℝ) ≤ d.scale ^ (max 1 (1 + kappa)) :=
    hd.2.2.2.2.2.2.2.1.trans
      (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + kappa)))
  have hA : d.residue.natAbs.divisors.card ≤ H := Nat.le_floor
    (hbound d.scale d.residue.natAbs hx ha (by
      nlinarith [Real.rpow_nonneg hxpos.le (max 1 (1 + kappa))]))
  have hλ : ∀ small ∈ dyadicWindow k.d, ∀ r ∈ dyadicWindow k.w,
      ‖lambdaTrim d (strictReceiverCutoff z) (roughY d.scale) k small r‖ ≤ (H : ℝ) := by
    intro small hsmall r hr
    by_cases hzero : lambdaTrim d (strictReceiverCutoff z) (roughY d.scale) k small r = 0
    · simp [hzero]
    have hK : keyKept d d.scale z k small r ≠ 0 := by
      rw [keyKept_eq_actual_lambdaTrim hd d.scale z hz k small r hsmall]
      exact hzero
    have hsupp := nonzero_labelSubset_support d z small r
      (fun v => keyPredicate z k v ∧
        ImbalancedChen.Part3OriginalS2SmoothYRankinStart.individualSmoothWithinY d.scale z v) hK
    have hp := Nat.mul_pos (dCarrier_pos d z small hsupp.1)
      (roughFiber_pos d z small r hsupp.2)
    have hprod := small_mul_rough_le_four hd z small r hsupp.2
    have h23 := Q2_mul_Q3_lt_scale hd hsigma
    have hpoly : ((small * r : ℕ) : ℝ) ≤ 8 * d.scale ^ (max 1 (1 + kappa)) := by
      nlinarith
    have hτ : (small * r).divisors.card ≤ H := Nat.le_floor
      (hbound d.scale (small * r) hx hp hpoly)
    exact (lambdaTrim_norm_le_tau d (strictReceiverCutoff z) (roughY d.scale)
      k small r hd).trans (by exact_mod_cast hτ)
  have hphysical := nativePhysicalCap_le_original_range hd hsigma
    (residue_ne_zero_of_original_c0 hd hc0) hlarge
  have hcap : (nativePhysicalCap d : ℝ) ≤ d.scale := by
    calc
      _ ≤ (Nat.floor (d.scale ^ ((4 : ℝ) / 5)) : ℝ) := by exact_mod_cast hphysical
      _ ≤ d.scale ^ ((4 : ℝ) / 5) := Nat.floor_le (Real.rpow_nonneg hxpos.le _)
      _ ≤ d.scale := Real.rpow_le_self_of_one_le hx (by norm_num)
  have hτ : ∀ t ∈ s2ZeroActive d (strictReceiverCutoff z) (roughY d.scale) k,
      (t.1.1 * t.1.2.1 * t.2.2.1).divisors.card ≤ H := by
    intro t ht
    obtain ⟨ht, he, hne⟩ := Finset.mem_filter.mp ht
    have hsmall := paired_small_in_key d k t ht
    have hright : lambdaTrim d (strictReceiverCutoff z) (roughY d.scale)
        k t.1.2.1 t.2.2.1 ≠ 0 := by
      intro hzero
      exact hne (by simp [restoredTerm, samePsiTerm, s2TermWithM, canonicalIndex, hzero])
    have hK : keyKept d d.scale z k t.1.2.1 t.2.2.1 ≠ 0 := by
      rw [keyKept_eq_actual_lambdaTrim hd d.scale z hz k t.1.2.1 t.2.2.1 hsmall]
      exact hright
    have hsupp := nonzero_labelSubset_support d z t.1.2.1 t.2.2.1
      (fun v => keyPredicate z k v ∧
        ImbalancedChen.Part3OriginalS2SmoothYRankinStart.individualSmoothWithinY d.scale z v) hK
    have ho := Finset.mem_filter.mp (Finset.mem_product.mp ht).1
    have hq : t.1.1 ∈ nativeQCarrier d :=
      Finset.mem_filter.mpr ⟨(Finset.mem_product.mp ho.1).1, ho.2⟩
    have hc : ⟨(t.1.1, t.1.2.1), (t.2.2.1, t.2.2.1)⟩ ∈ nativeCoefficientCarrier d z :=
      Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr ⟨hq, hsupp.1⟩,
        Finset.mem_product.mpr ⟨hsupp.2, hsupp.2⟩⟩
    have hmod := (native_supported_modulus_le hd z _ hc).1
    have hpoly : ((t.1.1 * t.1.2.1 * t.2.2.1 : ℕ) : ℝ) ≤
        8 * d.scale ^ (max 1 (1 + kappa)) := by
      have hmodR : ((t.1.1 * t.1.2.1 * t.2.2.1 : ℕ) : ℝ) ≤ nativePhysicalCap d := by
        exact_mod_cast hmod
      nlinarith
    exact Nat.le_floor (hbound d.scale _ hx (paired_second_modulus_lower hd k t ht).1 hpoly)
  have hbase := actual_S2_singleZero_integer_budget hd (strictReceiverCutoff z)
    (roughY d.scale) k H ha hA hλ hτ
  have hpow : (d.scale ^ eta) ^ (4 : ℕ) = d.scale ^ epsilon := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    congr 1
    dsimp [eta]
    ring
  calc
    _ ≤ 24 * singleZeroR k * d.U * (H : ℝ) ^ 4 := hbase
    _ ≤ 24 * singleZeroR k * d.U * (C0 * d.scale ^ eta) ^ 4 := by
      have hN : 0 ≤ d.U := by linarith [hd.1]
      have hR : 0 ≤ singleZeroR k := by unfold singleZeroR; positivity
      gcongr
    _ = _ := by rw [mul_pow, hpow]; ring

/-- The original physical product bound pays the S2 scale. Only the
occupied-key product is used: no upper bound on an arbitrary free key
is postulated. The factor four from the physical windows is retained. -/
theorem occupied_S2_singleZero_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (hc0 : 0 < c0) (z y : ℝ) (k : Key) (hk : k ∈ keyBank d z y) :
    (singleZeroR k * d.U) * d.scale ^ ((3 : ℝ) / 10) ≤
      4 * fixedDScale d ((2 : ℝ) ^ k.d) := by
  have hxpos : 0 < d.scale := zero_lt_one.trans_le (TransposedPrimitiveUPayment.one_le_scale hd)
  have hY : 0 < d.Q1 * (2 : ℝ) ^ k.d := by
    have hQ := zero_lt_one.trans_le hd.2.2.1
    positivity
  have hphysical := occupied_keyDR_le_physical
    (show 0 ≤ d.Q2 by linarith [hd.2.2.2.1])
    (show 0 ≤ d.Q3 by linarith [hd.2.2.2.2.1]) hk
  have hprod := Q1Q2Q3_lt_scale_seven_tenths hd hsigma
    (residue_ne_zero_of_original_c0 hd hc0)
  have hYR : singleZeroY d k * singleZeroR k ≤ 4 * d.scale ^ ((7 : ℝ) / 10) := by
    have hphysical' : (2 : ℝ) ^ k.d * (2 : ℝ) ^ k.w ≤ 4 * d.Q2 * d.Q3 := by
      simpa only [keyD, keyR, Nat.cast_pow, Nat.cast_ofNat] using hphysical
    have h := mul_le_mul_of_nonneg_left hphysical' (show 0 ≤ d.Q1 by linarith [hd.2.2.1])
    unfold singleZeroY singleZeroR
    nlinarith
  unfold fixedDScale
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hY).mpr
  calc
    _ = d.U * ((singleZeroY d k * singleZeroR k) * d.scale ^ ((3 : ℝ) / 10)) := by
      unfold singleZeroY
      ring
    _ ≤ d.U * ((4 * d.scale ^ ((7 : ℝ) / 10)) * d.scale ^ ((3 : ℝ) / 10)) := by
      have hN : 0 ≤ d.U := by linarith [hd.1]
      gcongr
    _ = 4 * (d.V * d.U ^ 2) := by
      rw [mul_assoc 4, ← Real.rpow_add hxpos]
      norm_num
      unfold MediumAtom.scale
      ring

/-- One constant and threshold precede every original atom, residue,
key and receiver. The source is the actual S2 correction; coefficient
subpower loss is absorbed using a genuine positive physical-scale gap. -/
theorem exists_actual_S2_singleZero_arbitrary_log (kappa A : ℝ) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom) (k : Key) (z : ℝ),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 → 0 ≤ z →
        k ∈ keyBank d (strictReceiverCutoff z) (roughY d.scale) → X ≤ d.scale →
        ‖singleZeroCorrection d (strictReceiverCutoff z) (roughY d.scale) k‖ ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨C0, hC0, hsource⟩ := exists_actual_S2_singleZero_subpower kappa
    ((1 : ℝ) / 10) (by norm_num)
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow 1 A (by norm_num)
      (show 0 < (1 : ℝ) / 5 by norm_num))
  let X := max X0 (max ((10 : ℝ) ^ (10 : ℕ))
    (Real.exp (Real.exp 1) + Real.exp 1 + 1))
  refine ⟨4 * C0, X, by positivity, ?_, ?_⟩
  · have hpos := Real.exp_pos 1
    exact (by linarith : Real.exp (Real.exp 1) < Real.exp (Real.exp 1) + Real.exp 1 + 1).trans_le
      ((le_max_right _ _).trans (le_max_right _ _))
  intro B sigma c0 d k z hd hsigma hc0 hz hk hx
  have hxright := (le_max_right X0 _).trans hx
  have hxlarge := (le_max_left _ _).trans hxright
  have hxpos : 0 < d.scale := zero_lt_one.trans_le (TransposedPrimitiveUPayment.one_le_scale hd)
  have hlog : 0 < Real.log d.scale := Real.log_pos (by
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < (10 : ℝ) ^ (10 : ℕ)) hxlarge)
  have hlogs : Real.log d.scale ^ A ≤ d.scale ^ ((1 : ℝ) / 5) := by
    simpa only [one_mul] using hX0 d.scale ((le_max_left _ _).trans hx)
  have hp := occupied_S2_singleZero_scale hd hsigma hc0
    (strictReceiverCutoff z) (roughY d.scale) k hk
  have hsource' := hsource B sigma c0 d k z hd hsigma hc0 hz hxlarge
  have hpay : (singleZeroR k * d.U * d.scale ^ ((1 : ℝ) / 10)) * Real.log d.scale ^ A ≤
      4 * fixedDScale d ((2 : ℝ) ^ k.d) := by
    calc
      _ ≤ (singleZeroR k * d.U * d.scale ^ ((1 : ℝ) / 10)) * d.scale ^ ((1 : ℝ) / 5) := by
        apply mul_le_mul_of_nonneg_left hlogs
        have hN : 0 ≤ d.U := by linarith [hd.1]
        unfold singleZeroR
        positivity
      _ = (singleZeroR k * d.U) * d.scale ^ ((3 : ℝ) / 10) := by
        rw [mul_assoc, ← Real.rpow_add hxpos]
        norm_num
      _ ≤ _ := hp
  have hlogpow : 0 < Real.log d.scale ^ A := Real.rpow_pos_of_pos hlog _
  have hpay' := (le_div_iff₀ hlogpow).mpr hpay
  calc
    _ ≤ C0 * (singleZeroR k * d.U * d.scale ^ ((1 : ℝ) / 10)) := hsource'
    _ ≤ C0 * (4 * fixedDScale d ((2 : ℝ) ^ k.d) / Real.log d.scale ^ A) :=
      mul_le_mul_of_nonneg_left hpay' hC0.le
    _ = (4 * C0) * (fixedDScale d ((2 : ℝ) ^ k.d) * Real.log d.scale ^ (-A)) := by
      rw [Real.rpow_neg hlog.le]
      ring

/-- Insert the paid single zero in F's independently defined ORIGINAL
primitive S2 minus its same-source MT. The full nonzero Poisson series
and actual other-rough correction remain on the left with exact signs. -/
theorem exists_original_S2_centered_except_rough_and_nonzero
    (kappa A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 →
        k ∈ originalNumericKeys d (roughZ d.scale) →
        X ≤ d.scale →
        |primitiveS2 d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k -
            (nativeMT d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re -
            (actualS2NonzeroModes d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re +
            (otherRoughCorrection d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re| ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨Cz, Xz, hCz, hXz, hz⟩ := exists_actual_S2_singleZero_arbitrary_log kappa A
  obtain ⟨Cg, Xg, hCg, hXg, hg⟩ := exists_actualZeroGramError_arbitrary_log A hA
  refine ⟨Cg + Cz, max Xg Xz, by linarith, hXg.trans_le (le_max_left _ _), ?_⟩
  intro B sigma c0 d k hd hsigma hc0 hk hx
  have hz0 : 0 ≤ roughZ d.scale := Real.rpow_nonneg
    (zero_le_one.trans (TransposedPrimitiveUPayment.one_le_scale hd)) _
  have hk' : k ∈ keyBank d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) := by
    simpa only [originalNumericKeys, originalSmoothTrim, roughY] using hk
  have hzb := hz B sigma c0 d k (roughZ d.scale) hd hsigma hc0 hz0 hk'
    ((le_max_right _ _).trans hx)
  have hgb := hg B sigma kappa c0 d k hd hsigma hc0 ((le_max_left _ _).trans hx)
  rw [actual_primitive_S2_centered_identity hd]
  have heq (a b c e : ℝ) : (a + b - c - e) - a + c = b - e := by ring
  rw [heq]
  calc
    _ ≤ |(actualZeroGramError d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re| +
        |(singleZeroCorrection d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re| :=
      abs_sub _ _
    _ ≤ ‖actualZeroGramError d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k‖ +
        ‖singleZeroCorrection d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k‖ :=
      add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
    _ ≤ _ := by nlinarith [hgb, hzb]

end
end ImbalancedChen.Part3OriginalS2SingleZeroPayment
