import ImbalancedChen.Part3OriginalActualSingleZeroCounting
import ImbalancedChen.Part3OriginalS2NativePhysicalRange
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The single zero in the original S2 ledger has a coprime MEAN on the
second leg. It is not either of the two S3 single-zero corrections.
We count its exact nm=a fibre and retain the actual phi(q*d*s)
denominator. The following file discharges every integer envelope here.
-/
namespace ImbalancedChen.Part3OriginalS2SingleZeroCounting

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalActualSingleZeroSource
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalSingleZeroPolynomialTau
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3.MediumPrimitivePsiSource20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumSingleZeroFiber20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open Classical Finset
open scoped BigOperators

noncomputable section

/-- Elementary reciprocal-totient payment. This follows from the exact
sum of totients, without a new analytic hypothesis. -/
theorem reciprocal_totient_le_divisor_ratio (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / (Nat.totient n : ℝ) ≤ (n.divisors.card : ℝ) / n := by
  have hφ : 0 < Nat.totient n := Nat.totient_pos.mpr hn
  have hnat : n ≤ n.divisors.card * Nat.totient n := by
    calc
      n = ∑ e ∈ n.divisors, Nat.totient e := (Nat.sum_totient n).symm
      _ ≤ ∑ _e ∈ n.divisors, Nat.totient n := by
        apply Finset.sum_le_sum
        intro e he
        exact Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors he))
      _ = _ := by simp
  have hreal : (n : ℝ) ≤ (n.divisors.card : ℝ) * (Nat.totient n : ℝ) := by
    exact_mod_cast hnat
  exact (div_le_div_iff₀ (by exact_mod_cast hφ) (by exact_mod_cast hn)).mpr
    (by simpa only [one_mul] using hreal)

def s2ZeroActive (d : MediumAtom) (z y : ℝ) (k : Key) : Finset PairIndex :=
  (pairedCarrier d k).filter
    (fun t => exactFirstProduct d t ∧ restoredTerm d z y k t ≠ 0)

theorem singleZeroCorrection_eq_active (d : MediumAtom) (z y : ℝ) (k : Key) :
    singleZeroCorrection d z y k =
      ∑ t ∈ s2ZeroActive d z y k, restoredTerm d z y k t := by
  unfold singleZeroCorrection s2ZeroActive
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases he : exactFirstProduct d t <;>
    by_cases hz : restoredTerm d z y k t = 0 <;> simp [he, hz]

/-- The same injective coordinate code as G is used, but its final
fibre is free (n2,s), because S2 has a mean instead of a congruence. -/
def s2ZeroCodeCarrier (d : MediumAtom) (k : Key) : Finset FirstCode :=
  ((nativeQCarrier d ×ˢ dyadicWindow k.d) ×ˢ dyadicWindow k.w).sigma
    (fun _ =>
      (firstProductPairs (paperPsiNaturalCarrier d.V) d.alphaCarrier
        d.residue.natAbs).sigma (fun _ => d.alphaCarrier ×ˢ dyadicWindow k.w))

theorem s2ZeroActive_card_le_code (d : MediumAtom) (z y : ℝ) (k : Key) :
    (s2ZeroActive d z y k).card ≤ (s2ZeroCodeCarrier d k).card := by
  apply Finset.card_le_card_of_injOn firstCode
  · intro t ht
    obtain ⟨ht, he, hne⟩ := Finset.mem_filter.mp ht
    obtain ⟨ho, hi⟩ := Finset.mem_product.mp ht
    obtain ⟨ho, hqc⟩ := Finset.mem_filter.mp ho
    obtain ⟨hq, hdm⟩ := Finset.mem_product.mp ho
    obtain ⟨hd, hm⟩ := Finset.mem_product.mp hdm
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hi
    obtain ⟨hr, hn₁⟩ := Finset.mem_product.mp hi
    obtain ⟨hs, hn₂⟩ := Finset.mem_product.mp hj
    have hprod : t.1.2.2 * t.2.1.2 = d.residue.natAbs := by
      have habs := congrArg Int.natAbs he
      simpa only [exactFirstProduct, Int.natAbs_natCast, Nat.mul_comm] using habs
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hq, hqc⟩, hd⟩, hr⟩,
        Finset.mem_sigma.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm, hn₁⟩, hprod⟩,
            Finset.mem_product.mpr ⟨hn₂, hs⟩⟩⟩
  · exact fun t ht u hu heq => firstCode_injective heq

theorem alphaCarrier_card_le_three_U
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.alphaCarrier.card : ℝ) ≤ 3 * d.U := by
  have hs : d.alphaCarrier ⊆ Finset.range (Nat.floor (2 * d.U) + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
      omega)
  have hc := Finset.card_le_card hs
  simp only [Finset.card_range] at hc
  have hcR : (d.alphaCarrier.card : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) + 1 := by
    exact_mod_cast hc
  have hf := Nat.floor_le (show 0 ≤ 2 * d.U by linarith [hd.1])
  linarith [hd.1]

theorem s2ZeroActive_card_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (H : ℕ) (ha : 0 < d.residue.natAbs)
    (hA : d.residue.natAbs.divisors.card ≤ H) :
    ((s2ZeroActive d z y k).card : ℝ) ≤
      12 * singleZeroY d k * singleZeroR k ^ 2 * d.U * H := by
  have hP : ((firstProductPairs (paperPsiNaturalCarrier d.V) d.alphaCarrier
      d.residue.natAbs).card : ℝ) ≤ H := by
    exact_mod_cast (firstProductPairs_card_le_divisors _ _ _ ha).trans hA
  have hq := nativeQ_card_le_four_Q hd
  have hn := alphaCarrier_card_le_three_U hd
  calc
    _ ≤ ((s2ZeroCodeCarrier d k).card : ℝ) := by
      exact_mod_cast s2ZeroActive_card_le_code d z y k
    _ = ((nativeQCarrier d).card : ℝ) * (2 : ℝ) ^ k.d *
        (2 : ℝ) ^ k.w *
        ((firstProductPairs (paperPsiNaturalCarrier d.V) d.alphaCarrier
          d.residue.natAbs).card : ℝ) * d.alphaCarrier.card * (2 : ℝ) ^ k.w := by
      simp only [s2ZeroCodeCarrier, Finset.card_sigma, Finset.card_product,
        Finset.sum_const, nsmul_eq_mul, dyadicWindow_card, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      ring
    _ ≤ (4 * d.Q1) * (2 : ℝ) ^ k.d * (2 : ℝ) ^ k.w * H *
        (3 * d.U) * (2 : ℝ) ^ k.w := by
      gcongr <;> first | exact hq | exact hP | exact hn | positivity
    _ = _ := by unfold singleZeroY singleZeroR; ring

theorem paired_second_modulus_lower
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k : Key)
    (t : PairIndex) (ht : t ∈ pairedCarrier d k) :
    0 < t.1.1 * t.1.2.1 * t.2.2.1 ∧
      singleZeroY d k * singleZeroR k / 2 ≤
        ((t.1.1 * t.1.2.1 * t.2.2.1 : ℕ) : ℝ) := by
  obtain ⟨ho, hi⟩ := Finset.mem_product.mp ht
  have hq := primitiveSmoothOuter_q_data (zero_lt_one.trans_le hd.2.2.1) ho
  have hdw := (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp ho).1).2).1
  have hsw := (Finset.mem_product.mp (Finset.mem_product.mp hi).2).1
  have hD : (2 : ℝ) ^ k.d ≤ (t.1.2.1 : ℝ) := by
    exact_mod_cast (Finset.mem_Ico.mp hdw).1
  have hR : (2 : ℝ) ^ k.w ≤ (t.2.2.1 : ℝ) := by
    exact_mod_cast (Finset.mem_Ico.mp hsw).1
  have hp : 0 < t.1.2.1 :=
    (pow_pos (by norm_num : (0 : ℕ) < 2) k.d).trans_le (Finset.mem_Ico.mp hdw).1
  have hs : 0 < t.2.2.1 :=
    (pow_pos (by norm_num : (0 : ℕ) < 2) k.w).trans_le (Finset.mem_Ico.mp hsw).1
  refine ⟨Nat.mul_pos (Nat.mul_pos hq.2.2.2 hp) hs, ?_⟩
  have hh := mul_le_mul
    (mul_le_mul hq.1 hD (by positivity) (Nat.cast_nonneg _)) hR
    (by positivity : (0 : ℝ) ≤ 2 ^ k.w) (by positivity)
  simpa only [singleZeroY, singleZeroR, Nat.cast_mul, div_mul_eq_mul_div,
    mul_div_assoc] using hh

theorem restoredTerm_norm_le_envelope
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (H : ℕ)
    (hλ : ∀ small ∈ dyadicWindow k.d, ∀ r ∈ dyadicWindow k.w,
      ‖lambdaTrim d z y k small r‖ ≤ (H : ℝ))
    (t : PairIndex) (ht : t ∈ pairedCarrier d k)
    (hτ : (t.1.1 * t.1.2.1 * t.2.2.1).divisors.card ≤ H) :
    ‖restoredTerm d z y k t‖ ≤
      2 * (H : ℝ) ^ 3 / (singleZeroY d k * singleZeroR k) := by
  have hdw := paired_small_in_key d k t ht
  have hi := Finset.mem_product.mp (Finset.mem_product.mp ht).2
  have hri := Finset.mem_product.mp hi.1
  have hsj := Finset.mem_product.mp hi.2
  have hAlpha := hd.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hq := actualPsiQWeight_norm_le_one d t.1.1
  have hm : ‖(actualPsiMWeight d t.1.2.2 : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (actualPsiMWeight_nonneg d _)] using actualPsiMWeight_le_one d t.1.2.2
  have hmod := paired_second_modulus_lower hd k t ht
  have hYR : 0 < singleZeroY d k * singleZeroR k := by
    unfold singleZeroY singleZeroR
    have hQ := zero_lt_one.trans_le hd.2.2.1
    positivity
  have hφ : (1 : ℝ) / (Nat.totient (t.1.1 * t.1.2.1 * t.2.2.1) : ℝ) ≤
      2 * H / (singleZeroY d k * singleZeroR k) := by
    calc
      _ ≤ ((t.1.1 * t.1.2.1 * t.2.2.1).divisors.card : ℝ) /
          ((t.1.1 * t.1.2.1 * t.2.2.1 : ℕ) : ℝ) :=
        reciprocal_totient_le_divisor_ratio _ hmod.1
      _ ≤ (H : ℝ) / ((t.1.1 * t.1.2.1 * t.2.2.1 : ℕ) : ℝ) := by
        gcongr
        exact_mod_cast hτ
      _ ≤ 2 * H / (singleZeroY d k * singleZeroR k) := by
        apply (div_le_div_iff₀ (by exact_mod_cast hmod.1) hYR).mpr
        nlinarith [mul_le_mul_of_nonneg_left hmod.2 (Nat.cast_nonneg H)]
  unfold restoredTerm samePsiTerm s2TermWithM
  split_ifs
  · simp only [canonicalIndex, norm_div, norm_mul, norm_star, Complex.norm_natCast]
    calc
      _ ≤ (1 * (H : ℝ) * H * 1 * 1 * 1) /
          (Nat.totient (t.1.1 * t.1.2.1 * t.2.2.1) : ℝ) := by
        gcongr <;> first | exact hq | exact hm | exact hλ _ hdw _ hri.1 |
          exact hλ _ hdw _ hsj.1 | exact hAlpha _ hri.2 | exact hAlpha _ hsj.2
      _ = (H : ℝ) ^ 2 * (1 / (Nat.totient (t.1.1 * t.1.2.1 * t.2.2.1) : ℝ)) := by ring
      _ ≤ (H : ℝ) ^ 2 * (2 * H / (singleZeroY d k * singleZeroR k)) := by
        exact mul_le_mul_of_nonneg_left hφ (sq_nonneg _)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

/-- The original S2 single-zero source, not a generic count envelope.
All d in the original common dyadic family are included once. -/
theorem actual_S2_singleZero_integer_budget
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (H : ℕ) (ha : 0 < d.residue.natAbs)
    (hA : d.residue.natAbs.divisors.card ≤ H)
    (hλ : ∀ small ∈ dyadicWindow k.d, ∀ r ∈ dyadicWindow k.w,
      ‖lambdaTrim d z y k small r‖ ≤ (H : ℝ))
    (hτ : ∀ t ∈ s2ZeroActive d z y k,
      (t.1.1 * t.1.2.1 * t.2.2.1).divisors.card ≤ H) :
    ‖singleZeroCorrection d z y k‖ ≤ 24 * singleZeroR k * d.U * (H : ℝ) ^ 4 := by
  have hY : 0 < singleZeroY d k := by
    unfold singleZeroY
    have hQ := zero_lt_one.trans_le hd.2.2.1
    positivity
  have hR : 0 < singleZeroR k := by unfold singleZeroR; positivity
  rw [singleZeroCorrection_eq_active]
  calc
    _ ≤ ∑ t ∈ s2ZeroActive d z y k, ‖restoredTerm d z y k t‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ s2ZeroActive d z y k,
        2 * (H : ℝ) ^ 3 / (singleZeroY d k * singleZeroR k) := by
      apply Finset.sum_le_sum
      intro t ht
      exact restoredTerm_norm_le_envelope hd z y k H hλ t
        (Finset.mem_filter.mp ht).1 (hτ t ht)
    _ = ((s2ZeroActive d z y k).card : ℝ) *
        (2 * (H : ℝ) ^ 3 / (singleZeroY d k * singleZeroR k)) := by simp
    _ ≤ (12 * singleZeroY d k * singleZeroR k ^ 2 * d.U * H) *
        (2 * (H : ℝ) ^ 3 / (singleZeroY d k * singleZeroR k)) :=
      mul_le_mul_of_nonneg_right (s2ZeroActive_card_le hd z y k H ha hA) (by positivity)
    _ = _ := by field_simp [hY.ne', hR.ne']; ring

end
end ImbalancedChen.Part3OriginalS2SingleZeroCounting
