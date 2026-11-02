import ImbalancedChen.Part3OriginalS2OtherRoughSource
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
An actual arithmetic reduction of otherRoughCorrection. It replaces the
seven original variables by the product v=mn, divisors of the NONZERO
signed shift v-a, and the genuine common-prime multiple sums. All powers
of tau stay inside their finite averages. The analytic estimate of the
resulting fixed-order moment is deliberately not a hypothesis here.
-/
namespace ImbalancedChen.Part3OriginalS2OtherRoughCounting

open ImbalancedChen ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2OtherRoughSource
open ImbalancedChen.Part3OriginalS2SingleZeroCounting
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3OriginalS2SmoothYRankinStart
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open Classical Finset
open scoped BigOperators

noncomputable section

def commonPrimes (d : MediumAtom) (z : ℝ) (k : Key) : Finset ℕ :=
  (Finset.range (2 ^ (k.w + 1))).filter
    (fun p => p.Prime ∧ z < (p : ℝ) ∧ Nat.Coprime p d.residue.natAbs)

def productMultiples (d : MediumAtom) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor (5 * d.scale))).filter
    (fun v => p ∣ v ∧ (v : ℤ) ≠ d.residue)

def meanMultiples (k : Key) (p : ℕ) : Finset ℕ :=
  (dyadicWindow k.w).filter (fun s => p ∣ s)

def primeActive (d : MediumAtom) (z : ℝ) (k : Key) (p : ℕ) : Finset PairIndex :=
  (roughActive d (strictReceiverCutoff z) (roughY d.scale) k).filter
    (fun t => p ∣ t.1.2.2 ∧ p ∣ t.2.2.1)

/-- Independent arithmetic moment. The first factor is the mean-leg
multiple sum, the second the original NONZERO shifted-product moment.
Both are required for the two factors 1/p in manuscript section 4. -/
def roughMoment (d : MediumAtom) (z : ℝ) (k : Key) : ℝ :=
  ∑ p ∈ commonPrimes d z k,
    (∑ s ∈ meanMultiples k p, tau s ^ 2) *
      (∑ v ∈ productMultiples d p, tau v * tau (shiftAbs d.residue v) ^ 6)

abbrev ProductCode := Σ _v : ℕ, (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)

def productCode (t : PairIndex) : ProductCode :=
  ⟨product t, ((t.1.1, t.1.2.1, t.2.1.1, t.1.2.2), (t.2.2.1, t.2.2.2))⟩

def productDecode (c : ProductCode) : PairIndex :=
  ((c.2.1.1, c.2.1.2.1, c.2.1.2.2.2),
    (c.2.1.2.2.1, c.1 / c.2.1.2.2.2), (c.2.2.1, c.2.2.2))

def productCodeCarrier (d : MediumAtom) (k : Key) (p : ℕ) : Finset ProductCode :=
  (productMultiples d p).sigma (fun v =>
    ((shiftAbs d.residue v).divisors ×ˢ (shiftAbs d.residue v).divisors ×ˢ
      (shiftAbs d.residue v).divisors ×ˢ v.divisors) ×ˢ
        (meanMultiples k p ×ˢ d.alphaCarrier))

def codeWeight (d : MediumAtom) (c : ProductCode) : ℝ :=
  tau (shiftAbs d.residue c.1) ^ 3 * tau c.2.2.1 ^ 2

theorem productDecode_code (t : PairIndex) (hm : 0 < t.1.2.2) :
    productDecode (productCode t) = t := by
  rcases t with ⟨⟨q, small, m⟩, ⟨r, n₁⟩, ⟨s, n₂⟩⟩
  simp only [productDecode, productCode, product, Nat.mul_div_cancel_left _ hm]

theorem primeActive_maps_to_code
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (k : Key) (p : ℕ)
    (t : PairIndex) (ht : t ∈ primeActive d z k p) :
    productCode t ∈ productCodeCarrier d k p := by
  obtain ⟨ht, hpm, hps⟩ := Finset.mem_filter.mp ht
  obtain ⟨hpair, hm, hv, hne, hdiv⟩ := roughActive_shift_data hd _ _ k t ht
  have hshift : shiftAbs d.residue (product t) ≠ 0 :=
    Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hqdiv : t.1.1 ∣ shiftAbs d.residue (product t) :=
    (dvd_mul_right t.1.1 t.1.2.1).trans ((dvd_mul_right _ _).trans hdiv)
  have hddiv : t.1.2.1 ∣ shiftAbs d.residue (product t) :=
    (dvd_mul_left t.1.2.1 t.1.1).trans ((dvd_mul_right _ _).trans hdiv)
  have hrdiv : t.2.1.1 ∣ shiftAbs d.residue (product t) :=
    (dvd_mul_left _ _).trans hdiv
  have hi := Finset.mem_product.mp (Finset.mem_product.mp hpair).2
  have hs := (Finset.mem_product.mp hi.2).1
  have hn₂ := (Finset.mem_product.mp hi.2).2
  refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hv, roughActive_product_le hd _ _ k t ht⟩,
        hpm.trans (dvd_mul_right _ _), hne⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hqdiv, hshift⟩,
        Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hddiv, hshift⟩,
          Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hrdiv, hshift⟩,
            Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, hv.ne'⟩⟩⟩⟩,
        Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hs, hps⟩, hn₂⟩⟩

/-- Factor-pair multiplicity tau(v), and three actual modulus-divisor
coordinates tau(|v-a|)^3. No tau(0) can enter this carrier. -/
theorem productCodeCarrier_sum (d : MediumAtom) (k : Key) (p : ℕ) :
    (∑ c ∈ productCodeCarrier d k p, codeWeight d c) =
      (d.alphaCarrier.card : ℝ) * (∑ s ∈ meanMultiples k p, tau s ^ 2) *
        (∑ v ∈ productMultiples d p, tau v * tau (shiftAbs d.residue v) ^ 6) := by
  rw [productCodeCarrier, Finset.sum_sigma]
  simp only [codeWeight, Finset.sum_product]
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  dsimp [tau]
  ring

theorem primeActive_weighted_count
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (k : Key) (p : ℕ) :
    (∑ t ∈ primeActive d z k p,
      tau (shiftAbs d.residue (product t)) ^ 3 * tau t.2.2.1 ^ 2) ≤
      (d.alphaCarrier.card : ℝ) * (∑ s ∈ meanMultiples k p, tau s ^ 2) *
        (∑ v ∈ productMultiples d p, tau v * tau (shiftAbs d.residue v) ^ 6) := by
  have hinj : Set.InjOn productCode (primeActive d z k p) := by
    intro t ht u hu heq
    have htm := (roughActive_shift_data hd _ _ k t (Finset.mem_filter.mp ht).1).2.1
    have hum := (roughActive_shift_data hd _ _ k u (Finset.mem_filter.mp hu).1).2.1
    have h := congrArg productDecode heq
    simpa only [productDecode_code t htm, productDecode_code u hum] using h
  have hsub : (primeActive d z k p).image productCode ⊆ productCodeCarrier d k p := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    exact primeActive_maps_to_code hd z k p t ht
  calc
    _ = ∑ c ∈ (primeActive d z k p).image productCode, codeWeight d c := by
      rw [Finset.sum_image hinj]
      rfl
    _ ≤ ∑ c ∈ productCodeCarrier d k p, codeWeight d c :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by
        unfold codeWeight tau
        positivity)
    _ = _ := productCodeCarrier_sum d k p

/-- Union bound over genuine rough common primes; repeated prime factors
can only increase the right hand side. -/
theorem otherRough_norm_le_prime_sum
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (hz : 0 ≤ z) (k : Key) :
    ‖otherRoughCorrection d (strictReceiverCutoff z) (roughY d.scale) k‖ ≤
      ∑ p ∈ commonPrimes d z k, ∑ t ∈ primeActive d z k p,
        ‖restoredTerm d (strictReceiverCutoff z) (roughY d.scale) k t‖ := by
  rw [otherRoughCorrection_eq_active]
  calc
    _ ≤ ∑ t ∈ roughActive d (strictReceiverCutoff z) (roughY d.scale) k,
        ‖restoredTerm d (strictReceiverCutoff z) (roughY d.scale) k t‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ roughActive d (strictReceiverCutoff z) (roughY d.scale) k,
        ∑ p ∈ commonPrimes d z k,
          if p ∣ t.1.2.2 ∧ p ∣ t.2.2.1 then
            ‖restoredTerm d (strictReceiverCutoff z) (roughY d.scale) k t‖ else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨p, hp, hzp, hpm, hps, hpa⟩ := roughActive_common_prime hd z hz k t ht
      have hpair := (Finset.mem_filter.mp ht).1
      have hs := (Finset.mem_product.mp
        (Finset.mem_product.mp (Finset.mem_product.mp hpair).2).2).1
      have hslo : 0 < t.2.2.1 :=
        (pow_pos (by norm_num : (0 : ℕ) < 2) k.w).trans_le (Finset.mem_Ico.mp hs).1
      have hpbank : p ∈ commonPrimes d z k := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((Nat.le_of_dvd hslo hps).trans_lt
          (by simpa only [pow_succ] using (Finset.mem_Ico.mp hs).2)), hp, hzp, hpa⟩
      have h := Finset.single_le_sum
        (fun p (_hp : p ∈ commonPrimes d z k) =>
          show (0 : ℝ) ≤ (if p ∣ t.1.2.2 ∧ p ∣ t.2.2.1 then
            ‖restoredTerm d (strictReceiverCutoff z) (roughY d.scale) k t‖ else 0) from
              by split_ifs <;> positivity) hpbank
      simpa only [if_pos ⟨hpm, hps⟩] using h
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [primeActive, Finset.sum_filter]

/-- Actual S2 rough correction reduced to independent fixed-order arithmetic
moments. The original common d family is counted by divisors of the shift,
not by summing D separate assumed estimates. -/
theorem actual_otherRough_le_collapsed_moment
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (hz : 0 ≤ z) (k : Key) :
    ‖otherRoughCorrection d (strictReceiverCutoff z) (roughY d.scale) k‖ ≤
      (6 * d.U / (singleZeroY d k * singleZeroR k)) * roughMoment d z k := by
  have hfac : 0 ≤ 2 / (singleZeroY d k * singleZeroR k) := by
    unfold singleZeroY singleZeroR
    have hQ := zero_lt_one.trans_le hd.2.2.1
    positivity
  have hM : 0 ≤ roughMoment d z k := by unfold roughMoment tau; positivity
  calc
    _ ≤ ∑ p ∈ commonPrimes d z k, ∑ t ∈ primeActive d z k p,
        ‖restoredTerm d (strictReceiverCutoff z) (roughY d.scale) k t‖ :=
      otherRough_norm_le_prime_sum hd z hz k
    _ ≤ ∑ p ∈ commonPrimes d z k,
        (2 / (singleZeroY d k * singleZeroR k)) *
          ((d.alphaCarrier.card : ℝ) * (∑ s ∈ meanMultiples k p, tau s ^ 2) *
            (∑ v ∈ productMultiples d p, tau v * tau (shiftAbs d.residue v) ^ 6)) := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        _ ≤ ∑ t ∈ primeActive d z k p,
            (2 / (singleZeroY d k * singleZeroR k)) *
              (tau (shiftAbs d.residue (product t)) ^ 3 * tau t.2.2.1 ^ 2) := by
          apply Finset.sum_le_sum
          intro t ht
          simpa only [mul_assoc] using roughActive_term_bound hd _ _ k t
            (Finset.mem_filter.mp ht).1
        _ = (2 / (singleZeroY d k * singleZeroR k)) *
            (∑ t ∈ primeActive d z k p,
              tau (shiftAbs d.residue (product t)) ^ 3 * tau t.2.2.1 ^ 2) :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (primeActive_weighted_count hd z k p) hfac
    _ = ((2 / (singleZeroY d k * singleZeroR k)) * d.alphaCarrier.card) *
        roughMoment d z k := by
      unfold roughMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ ((2 / (singleZeroY d k * singleZeroR k)) * (3 * d.U)) *
        roughMoment d z k := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (alphaCarrier_card_le_three_U hd) hfac) hM
    _ = _ := by ring

end
end ImbalancedChen.Part3OriginalS2OtherRoughCounting



