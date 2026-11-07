import ImbalancedChen.Part3OriginalS2SingleZeroCounting
import ImbalancedChen.Part3TransposedPrimitiveUMoment
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual S2 other-rough correction: retain the nonzero signed shift,
extract a genuine common prime above the ORIGINAL cutoff, and pay the
actual mean denominator by divisor weights. No correction bound is a premise.
-/
namespace ImbalancedChen.Part3OriginalS2OtherRoughSource

open ImbalancedChen ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2SingleZeroCounting
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalSingleZeroPolynomialTau
open ImbalancedChen.Part3OriginalActualSingleZeroSource
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
open ImbalancedChen.Part3OriginalS2ActualTailTransfer
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3.MediumPrimitivePsiSource20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open Classical Finset
open scoped BigOperators

noncomputable section

def tau (n : ℕ) : ℝ := n.divisors.card

def shiftAbs (a : ℤ) (v : ℕ) : ℕ := ((v : ℤ) - a).natAbs

def product (t : PairIndex) : ℕ := t.1.2.2 * t.2.1.2

def roughActive (d : MediumAtom) (z y : ℝ) (k : Key) : Finset PairIndex :=
  (pairedCarrier d k).filter (fun t =>
    ¬exactFirstProduct d t ∧ ¬otherRoughGate t ∧ restoredTerm d z y k t ≠ 0)

theorem otherRoughCorrection_eq_active (d : MediumAtom) (z y : ℝ) (k : Key) :
    otherRoughCorrection d z y k =
      ∑ t ∈ roughActive d z y k, restoredTerm d z y k t := by
  unfold otherRoughCorrection roughActive
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases he : exactFirstProduct d t <;>
    by_cases hg : otherRoughGate t <;>
      by_cases hn : restoredTerm d z y k t = 0 <;> simp [he, hg, hn]

theorem tau_nonneg (n : ℕ) : 0 ≤ tau n := Nat.cast_nonneg _

theorem tau_mono {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) : tau a ≤ tau b := by
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hb h)

theorem tau_mul_le (a b : ℕ) : tau (a * b) ≤ tau a * tau b := by
  exact_mod_cast TransposedPrimitiveUMoment.card_divisors_mul_le a b

/-- The original rough fibre, including prime powers, gives p>z. -/
theorem roughFiber_prime_gt (d : MediumAtom) (z : ℝ) (hz : 0 ≤ z)
    {small s p : ℕ} (hs : s ∈ roughFiber d z small) (hp : p.Prime) (hps : p ∣ s) :
    z < (p : ℝ) := by
  obtain ⟨dw, hdw, hds⟩ := Finset.mem_image.mp hs
  obtain ⟨hdw, hsmall⟩ := Finset.mem_filter.mp hdw
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hdw
  have hprod : zRoughPart z v.1 * zRoughPart z v.2 = s := by
    change (labelDW z v).2 = s
    rw [he]
    exact hds
  rw [← hprod] at hps
  rcases hp.dvd_mul.mp hps with hp1 | hp2
  · have hR := originalRough_supported_receiver z hz v.1
    exact (original_lt_nat_iff_receiver_le z hz p).mpr
      (hR.2 p (Nat.mem_primeFactors.mpr ⟨hp, hp1, hR.1⟩))
  · have hR := originalRough_supported_receiver z hz v.2
    exact (original_lt_nat_iff_receiver_le z hz p).mpr
      (hR.2 p (Nat.mem_primeFactors.mpr ⟨hp, hp2, hR.1⟩))

/-- Every active term supplies its OWN nonzero shift and modulus divisor.
The residue remains signed; no replacement by |a| occurs. -/
theorem roughActive_shift_data
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (t : PairIndex) (ht : t ∈ roughActive d z y k) :
    t ∈ pairedCarrier d k ∧ 0 < t.1.2.2 ∧ 0 < product t ∧
      (product t : ℤ) ≠ d.residue ∧
      t.1.1 * t.1.2.1 * t.2.1.1 ∣ shiftAbs d.residue (product t) := by
  obtain ⟨hpair, he, hg, hne⟩ := Finset.mem_filter.mp ht
  have hgate : Nat.Coprime t.2.1.2 (t.1.1 * t.1.2.1 * t.2.1.1) ∧
      Nat.Coprime t.2.2.2 (t.1.1 * t.1.2.1 * t.2.2.1) ∧
      Int.ModEq (t.1.1 * t.1.2.1 * t.2.1.1) (product t : ℤ) d.residue := by
    by_contra h
    exact hne (by simp [restoredTerm, canonicalIndex, samePsiTerm, s2TermWithM,
      product, h])
  have hm := paired_m_positive (zero_lt_one.trans_le hd.2.1) hpair
  have hnmem := (Finset.mem_product.mp
    (Finset.mem_product.mp (Finset.mem_product.mp hpair).2).1).2
  have hnlo : d.U ≤ (t.2.1.2 : ℝ) :=
    (Nat.le_ceil d.U).trans (by exact_mod_cast
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hnmem).1).1)
  have hnpos : 0 < t.2.1.2 := by
    have hpos : (0 : ℝ) < t.2.1.2 := (zero_lt_one.trans_le hd.1).trans_le hnlo
    exact_mod_cast hpos
  have he' : (product t : ℤ) ≠ d.residue := by
    simpa only [product, exactFirstProduct, Nat.mul_comm] using he
  refine ⟨hpair, hm, Nat.mul_pos hm hnpos, he', ?_⟩
  have hdiv := Int.modEq_iff_dvd.mp hgate.2.2.symm
  simpa only [shiftAbs, Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv

/-- The common factor really divides m and the MEAN-leg rough modulus s.
It is automatically coprime to the original moving residue. -/
theorem roughActive_common_prime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (hz : 0 ≤ z)
    (k : Key) (t : PairIndex)
    (ht : t ∈ roughActive d (strictReceiverCutoff z) (roughY d.scale) k) :
    ∃ p : ℕ, p.Prime ∧ z < (p : ℝ) ∧
      p ∣ t.1.2.2 ∧ p ∣ t.2.2.1 ∧ Nat.Coprime p d.residue.natAbs := by
  obtain ⟨hpair, he, hg, hne⟩ := Finset.mem_filter.mp ht
  obtain ⟨p, hp, hpm, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
  have hλ : lambdaTrim d (strictReceiverCutoff z) (roughY d.scale)
      k t.1.2.1 t.2.2.1 ≠ 0 := by
    intro hzero
    exact hne (by simp [restoredTerm, samePsiTerm, s2TermWithM, canonicalIndex, hzero])
  have hK : keyKept d d.scale z k t.1.2.1 t.2.2.1 ≠ 0 := by
    rw [keyKept_eq_actual_lambdaTrim hd d.scale z hz k t.1.2.1 t.2.2.1
      (paired_small_in_key d k t hpair)]
    exact hλ
  have hsupp := nonzero_labelSubset_support d z t.1.2.1 t.2.2.1
    (fun v => keyPredicate z k v ∧
      ImbalancedChen.Part3OriginalS2SmoothYRankinStart.individualSmoothWithinY d.scale z v) hK
  have hsCop := (lambdaTrim_support_residue hd (strictReceiverCutoff z)
    (roughY d.scale) k t.1.2.1 t.2.2.1 hλ).2
  exact ⟨p, hp, roughFiber_prime_gt d z hz hsupp.2 hp hps, hpm, hps,
    Nat.Coprime.of_dvd_left hps hsCop⟩

/-- The exact smooth m support and original alpha interval imply v<=5x.
This cap is independent of d, k, and the prime subsequently extracted. -/
theorem roughActive_product_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (t : PairIndex) (ht : t ∈ roughActive d z y k) :
    product t ≤ Nat.floor (5 * d.scale) := by
  have hpair := (Finset.mem_filter.mp ht).1
  have ho := (Finset.mem_filter.mp (Finset.mem_product.mp hpair).1).1
  have hm := (Finset.mem_product.mp (Finset.mem_product.mp ho).2).2
  have hn := (Finset.mem_product.mp
    (Finset.mem_product.mp (Finset.mem_product.mp hpair).2).1).2
  have hmhi := actual_smooth_m_bound (zero_lt_one.trans_le hd.2.1) hm
  have hnhi : (t.2.1.2 : ℝ) ≤ 2 * d.U :=
    (show (t.2.1.2 : ℝ) ≤ Nat.floor (2 * d.U) by exact_mod_cast
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2).trans
      (Nat.floor_le (by linarith [hd.1]))
  apply Nat.le_floor
  have h := mul_le_mul hmhi hnhi (Nat.cast_nonneg _) (by linarith [hd.2.1])
  dsimp [product, MediumAtom.scale]
  push_cast
  nlinarith

/-- Actual reciprocal-totient payment, keeping FIXED divisor weights.
No pointwise x^epsilon replacement is made on a logarithmic error. -/
theorem restoredTerm_norm_le_divisor_mean
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (t : PairIndex) (ht : t ∈ pairedCarrier d k) :
    ‖restoredTerm d z y k t‖ ≤
      (2 / (singleZeroY d k * singleZeroR k)) *
        (tau (t.1.2.1 * t.2.1.1) * tau (t.1.2.1 * t.2.2.1) *
          tau (t.1.1 * t.1.2.1 * t.2.2.1)) := by
  have hmod := paired_second_modulus_lower hd k t ht
  have hYR : 0 < singleZeroY d k * singleZeroR k := by
    unfold singleZeroY singleZeroR
    have hQ := zero_lt_one.trans_le hd.2.2.1
    positivity
  have hφ : (1 : ℝ) / (Nat.totient (t.1.1 * t.1.2.1 * t.2.2.1) : ℝ) ≤
      2 * tau (t.1.1 * t.1.2.1 * t.2.2.1) /
        (singleZeroY d k * singleZeroR k) := by
    calc
      _ ≤ tau (t.1.1 * t.1.2.1 * t.2.2.1) /
          ((t.1.1 * t.1.2.1 * t.2.2.1 : ℕ) : ℝ) :=
        reciprocal_totient_le_divisor_ratio _ hmod.1
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by exact_mod_cast hmod.1) hYR).mpr
        nlinarith [mul_le_mul_of_nonneg_left hmod.2
          (tau_nonneg (t.1.1 * t.1.2.1 * t.2.2.1))]
  have hi := Finset.mem_product.mp (Finset.mem_product.mp ht).2
  have hAlpha := hd.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hq := actualPsiQWeight_norm_le_one d t.1.1
  have hm : ‖(actualPsiMWeight d t.1.2.2 : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (actualPsiMWeight_nonneg d _)] using actualPsiMWeight_le_one d t.1.2.2
  have hr : ‖lambdaTrim d z y k t.1.2.1 t.2.1.1‖ ≤ tau (t.1.2.1 * t.2.1.1) :=
    lambdaTrim_norm_le_tau d z y k t.1.2.1 t.2.1.1 hd
  have hs : ‖lambdaTrim d z y k t.1.2.1 t.2.2.1‖ ≤ tau (t.1.2.1 * t.2.2.1) :=
    lambdaTrim_norm_le_tau d z y k t.1.2.1 t.2.2.1 hd
  unfold restoredTerm samePsiTerm s2TermWithM
  split_ifs
  · simp only [canonicalIndex, norm_div, norm_mul, norm_star, Complex.norm_natCast]
    calc
      _ ≤ (1 * tau (t.1.2.1 * t.2.1.1) * tau (t.1.2.1 * t.2.2.1) * 1 * 1 * 1) /
          (Nat.totient (t.1.1 * t.1.2.1 * t.2.2.1) : ℝ) := by
        gcongr <;> first | exact hq | exact hm | exact hr | exact hs |
          exact hAlpha _ (Finset.mem_product.mp hi.1).2 |
          exact hAlpha _ (Finset.mem_product.mp hi.2).2
      _ = (tau (t.1.2.1 * t.2.1.1) * tau (t.1.2.1 * t.2.2.1)) *
          (1 / (Nat.totient (t.1.1 * t.1.2.1 * t.2.2.1) : ℝ)) := by ring
      _ ≤ (tau (t.1.2.1 * t.2.1.1) * tau (t.1.2.1 * t.2.2.1)) *
          (2 * tau (t.1.1 * t.1.2.1 * t.2.2.1) /
            (singleZeroY d k * singleZeroR k)) :=
        mul_le_mul_of_nonneg_left hφ (mul_nonneg (tau_nonneg _) (tau_nonneg _))
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

/-- After the actual congruence, three divisor weights collapse to the
nonzero shift and the untouched mean modulus s. -/
theorem roughActive_term_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (t : PairIndex) (ht : t ∈ roughActive d z y k) :
    ‖restoredTerm d z y k t‖ ≤
      (2 / (singleZeroY d k * singleZeroR k)) *
        tau (shiftAbs d.residue (product t)) ^ 3 * tau t.2.2.1 ^ 2 := by
  obtain ⟨hp, hm, hv, hne, hdiv⟩ := roughActive_shift_data hd z y k t ht
  have hshift : shiftAbs d.residue (product t) ≠ 0 :=
    Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hqd : t.1.1 * t.1.2.1 ∣ shiftAbs d.residue (product t) :=
    (dvd_mul_right _ _).trans hdiv
  have hdr : t.1.2.1 * t.2.1.1 ∣ shiftAbs d.residue (product t) := by
    apply dvd_trans _ hdiv
    exact ⟨t.1.1, by ring⟩
  have hdv : t.1.2.1 ∣ shiftAbs d.residue (product t) :=
    (dvd_mul_left _ _).trans hqd
  have hds := (tau_mul_le t.1.2.1 t.2.2.1).trans
    (mul_le_mul_of_nonneg_right (tau_mono hshift hdv) (tau_nonneg _))
  have hqds := (tau_mul_le (t.1.1 * t.1.2.1) t.2.2.1).trans
    (mul_le_mul_of_nonneg_right (tau_mono hshift hqd) (tau_nonneg _))
  calc
    _ ≤ (2 / (singleZeroY d k * singleZeroR k)) *
        (tau (t.1.2.1 * t.2.1.1) * tau (t.1.2.1 * t.2.2.1) *
          tau (t.1.1 * t.1.2.1 * t.2.2.1)) :=
      restoredTerm_norm_le_divisor_mean hd z y k t hp
    _ ≤ (2 / (singleZeroY d k * singleZeroR k)) *
        (tau (shiftAbs d.residue (product t)) *
          (tau (shiftAbs d.residue (product t)) * tau t.2.2.1) *
          (tau (shiftAbs d.residue (product t)) * tau t.2.2.1)) := by
      gcongr <;> first | exact tau_mono hshift hdr | exact hds | exact hqds |
        exact tau_nonneg _ | positivity
    _ = _ := by ring

end
end ImbalancedChen.Part3OriginalS2OtherRoughSource


