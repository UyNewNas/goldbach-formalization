import ImbalancedChen.P5ProperPowerSignedModulusPayment
import ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound
import ImbalancedChen.P5RoughSquareWeightedBudget
import Mathlib.Data.Fintype.BigOperators

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original finite proper-power chart is charged to a reciprocal-product
mass. One marked slot has a genuine A^(-1/2) reciprocal-tail saving, with
explicit logarithmic losses. The other slots retain their original order.
The noncollision signed modulus cost is the literal distance-divisor sup
on the actual complete-product range, plus the SAME rho/phi mean budget.
Exact product=t is kept separate and uses the earlier tau(t)^k integer-word
multiplicity. This is not the prime-square diagonal of the bad receiver.
-/

namespace ImbalancedChen.P5Z.ProperPowerActualReciprocalTail

noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
open ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
open ImbalancedChen.P5Z.LicensedOriginalIntegerProfile
open ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
open ImbalancedChen.Part3.OriginalProperPowerChartCount
open ImbalancedChen.Part3.OriginalProperPowerActualChart
open ImbalancedChen.Part3.AllKLambdaChartCorrection
open ImbalancedChen.Part3.AllKFamilyLambdaCorrectionBound
open ImbalancedChen.P5Z.ProperPowerSignedMeanHBTransport
open ImbalancedChen.P5Z.ProperPowerSignedModulusPayment
open ImbalancedChen.P5Z.RoughSquareWeightedBudget

/-- The actual reciprocal tail of prime-base proper powers, with all
possible representations covered rather than chosen as a unique exponent. -/
def properTail (U : ℕ) (A : ℝ) : Finset ℕ :=
  (properPowers U).filter (fun n => A ≤ (n : ℝ))

def reciprocalTailBudget (U : ℕ) (A : ℝ) : ℝ :=
  ((Nat.log2 U + 1 : ℕ) : ℝ) * logBudget (Nat.sqrt U) / Real.sqrt A

/-- An elementary proper-power reciprocal tail with fixed logarithmic
losses. Each n=p^e>=A satisfies sqrt(A)*p<=n. Summing the base/exponent
cover therefore costs one harmonic base sum and one exponent logarithm. -/
theorem properTail_reciprocal_le {U : ℕ} (hU : 1 ≤ U) {A : ℝ} (hA : 0 < A) :
    (∑ n ∈ properTail U A, 1 / (n : ℝ)) ≤ reciprocalTailBudget U A := by
  let S := properTail U A
  let P := baseExponentPairs U
  have hex (n : S) : ∃ pe : P, pe.val.1 ^ pe.val.2 = n.val := by
    have hn := (Finset.mem_filter.mp n.property).1
    obtain ⟨pe, hpe, heq⟩ := Finset.mem_image.mp (properPowers_subset_pair_image hU hn)
    exact ⟨⟨pe, hpe⟩, heq⟩
  let E : S → P := fun n => Classical.choose (hex n)
  have hpower (n : S) : (E n).val.1 ^ (E n).val.2 = n.val := Classical.choose_spec (hex n)
  have hinj : Function.Injective E := by
    intro n m heq
    apply Subtype.ext
    calc
      n.val = (E n).val.1 ^ (E n).val.2 := (hpower n).symm
      _ = (E m).val.1 ^ (E m).val.2 := congrArg (fun pe : P => pe.val.1 ^ pe.val.2) heq
      _ = m.val := hpower m
  let w : P → ℝ := fun pe => (1 / Real.sqrt A) * (1 / (pe.val.1 : ℝ))
  have hpoint (n : S) : 1 / (n.val : ℝ) ≤ w (E n) := by
    have hpn := Finset.mem_product.mp (E n).property
    have hp : 2 ≤ (E n).val.1 := (Finset.mem_Icc.mp hpn.1).1
    have he : 2 ≤ (E n).val.2 := (Finset.mem_Icc.mp hpn.2).1
    have hnA : A ≤ (n.val : ℝ) := (Finset.mem_filter.mp n.property).2
    have hn0 : 0 ≤ (n.val : ℝ) := Nat.cast_nonneg _
    have hpsq : ((E n).val.1 : ℝ) ^ 2 ≤ (n.val : ℝ) := by
      exact_mod_cast (show (E n).val.1 ^ 2 ≤ n.val from
        (pow_le_pow_right₀ (by omega : 1 ≤ (E n).val.1) he).trans_eq (hpower n))
    have hpRoot : ((E n).val.1 : ℝ) ≤ Real.sqrt (n.val : ℝ) :=
      Real.le_sqrt_of_sq_le hpsq
    have hARoot : Real.sqrt A ≤ Real.sqrt (n.val : ℝ) := Real.sqrt_le_sqrt hnA
    have hprod : Real.sqrt A * ((E n).val.1 : ℝ) ≤ (n.val : ℝ) := by
      calc
        _ ≤ Real.sqrt (n.val : ℝ) * Real.sqrt (n.val : ℝ) :=
          mul_le_mul hARoot hpRoot (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
        _ = _ := by nlinarith [Real.sq_sqrt hn0]
    have hpR : (0 : ℝ) < (E n).val.1 := by exact_mod_cast (show 0 < (E n).val.1 by omega)
    have hrec := one_div_le_one_div_of_le (mul_pos (Real.sqrt_pos.mpr hA) hpR) hprod
    dsimp only [w]
    simpa only [one_div, mul_inv_rev, mul_comm] using hrec
  have hPsub : P ⊆ (Finset.Icc 1 (Nat.sqrt U)).product (Finset.Icc 1 (Nat.log2 U + 1)) := by
    intro pe hpe
    obtain ⟨hp, he⟩ := Finset.mem_product.mp hpe
    obtain ⟨hp0, hpU⟩ := Finset.mem_Icc.mp hp
    obtain ⟨he0, heU⟩ := Finset.mem_Icc.mp he
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hpU⟩,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hsum : (∑ n : S, 1 / (n.val : ℝ)) ≤ ∑ pe : P, w pe := by
    calc
      _ ≤ ∑ n : S, w (E n) := Finset.sum_le_sum (fun n _ => hpoint n)
      _ = ∑ pe ∈ Finset.univ.image E, w pe := by
        rw [Finset.sum_image (fun n _ m _ h => hinj h)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => by dsimp [w]; positivity)
  have hpair : (∑ pe : P, w pe) ≤
      (1 / Real.sqrt A) * ((Nat.log2 U + 1 : ℕ) : ℝ) * logBudget (Nat.sqrt U) := by
    rw [Finset.sum_coe_sort]
    calc
      _ ≤ ∑ pe ∈ (Finset.Icc 1 (Nat.sqrt U)).product (Finset.Icc 1 (Nat.log2 U + 1)),
          (1 / Real.sqrt A) * (1 / (pe.1 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun _ _ _ => by positivity)
      _ = (1 / Real.sqrt A) * ((Nat.log2 U + 1 : ℕ) : ℝ) *
          ∑ p ∈ Finset.Icc 1 (Nat.sqrt U), 1 / (p : ℝ) := by
        simp only [Finset.sum_product, Finset.sum_const, nsmul_eq_mul,
          Nat.card_Icc, Nat.add_sub_cancel]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_Icc_le_logBudget _)
        (by positivity)
  calc
    _ = ∑ n : S, 1 / (n.val : ℝ) := (Finset.sum_coe_sort S _).symm
    _ ≤ _ := hsum.trans hpair
    _ = reciprocalTailBudget U A := by unfold reciprocalTailBudget; ring

/-- Arbitrary finite ordered integer words retain their coordinate labels.
Finite Fubini is applied to the coordinate carrier, never to the product
image, so repeated factors and multiple marked occurrences are preserved. -/
theorem ordered_reciprocal_le_product {k : ℕ} (S : Finset (List ℕ))
    (B : Fin k → Finset ℕ) (hlen : ∀ us ∈ S, us.length = k)
    (hcoord : ∀ us ∈ S, ∀ i : Fin k, wordVector k us i ∈ B i) :
    (∑ us ∈ S, 1 / (us.prod : ℝ)) ≤
      ∏ i : Fin k, ∑ n ∈ B i, 1 / (n : ℝ) := by
  let E : S → (∀ i : Fin k, B i) := fun us i => ⟨wordVector k us.val i, hcoord us.val us.property i⟩
  have hinj : Function.Injective E := by
    intro us vs heq
    apply Subtype.ext
    apply wordVector_injOn_length k (hlen _ us.property) (hlen _ vs.property)
    funext i
    exact congrArg (fun f : ∀ i : Fin k, B i => (f i).val) heq
  let w : (∀ i : Fin k, B i) → ℝ := fun v => ∏ i, 1 / ((v i).val : ℝ)
  have he (us : S) : w (E us) = 1 / (us.val.prod : ℝ) := by
    dsimp only [w, E]
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
    have hcast : (∏ i : Fin k, (wordVector k us.val i : ℝ)) = (us.val.prod : ℝ) := by
      have hp := congrArg (fun xs : List ℕ => (xs.prod : ℝ))
        (ofFn_wordVector (hlen _ us.property))
      simpa only [Nat.cast_list_prod, List.map_ofFn, List.prod_ofFn] using hp
    rw [hcast]
  have hsub : (∑ v ∈ Finset.univ.image E, w v) ≤ ∑ v : (∀ i : Fin k, B i), w v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Finset.prod_nonneg (fun _ _ => by positivity))
  have hleft : (∑ v ∈ Finset.univ.image E, w v) = ∑ us ∈ S, 1 / (us.prod : ℝ) := by
    rw [Finset.sum_image (fun us _ vs _ h => hinj h)]
    simp_rw [he]
    exact Finset.sum_coe_sort S _
  rw [hleft] at hsub
  have hright : (∑ v : (∀ i : Fin k, B i), w v) =
      ∏ i : Fin k, ∑ n ∈ B i, 1 / (n : ℝ) := by
    dsimp only [w]
    rw [← Fintype.prod_sum (fun (i : Fin k) (n : B i) => 1 / (n.val : ℝ))]
    apply Finset.prod_congr rfl
    intro i hi
    exact Finset.sum_coe_sort (B i) _
  exact hsub.trans_eq hright

def reciprocalChartBudget {k : ℕ} (U : Fin k → ℕ) (bad : Fin k) (A : ℝ) : ℝ :=
  ∏ i : Fin k, if i = bad then reciprocalTailBudget (U i) A else logBudget (U i)

/-- Exactly one marked reciprocal-tail factor is paid, with the original
remaining harmonic factors and no permutation or rank factorial. -/
theorem reciprocalChartBudget_eq_marked_tail {k : ℕ}
    (U : Fin k → ℕ) (bad : Fin k) (A : ℝ) :
    reciprocalChartBudget U bad A = reciprocalTailBudget (U bad) A *
      ∏ i ∈ (Finset.univ : Finset (Fin k)).erase bad, logBudget (U i) := by
  let f : Fin k → ℝ := fun i =>
    if i = bad then reciprocalTailBudget (U i) A else logBudget (U i)
  have he : (∏ i ∈ (Finset.univ : Finset (Fin k)).erase bad, f i) =
      ∏ i ∈ (Finset.univ : Finset (Fin k)).erase bad, logBudget (U i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [f, if_neg (Finset.mem_erase.mp hi).1]
  have hh := Finset.prod_erase_mul Finset.univ f (Finset.mem_univ bad)
  rw [he] at hh
  simpa only [reciprocalChartBudget, f, if_pos rfl, mul_comm] using hh.symm

/-- A marked original chart has the advertised reciprocal-tail reserve
before the same-rho signed modulus sum is estimated. -/
theorem actual_bad_chart_reciprocal_le
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (hone : ∀ x, x ≤ 1 → chi x = 1) (hzero : ∀ x, 2 ≤ x → chi x = 0)
    (cap k : ℕ) (T kappa0 : ℝ) {js : List ℕ} (hjs : js ∈ chartBank cap k)
    (bad : Fin k) {A : ℝ} (hA : 0 < A)
    (hfloor : ∀ us ∈ badChartWords chi eta W T kappa0 cap k js bad,
      A ≤ (us.getD bad.val 0 : ℝ)) :
    (∑ us ∈ badChartWords chi eta W T kappa0 cap k js bad, 1 / (us.prod : ℝ)) ≤
      reciprocalChartBudget (chartUpper k js) bad A := by
  let S := badChartWords chi eta W T kappa0 cap k js bad
  let B : Fin k → Finset ℕ := fun i =>
    if i = bad then properTail (chartUpper k js i) A else Finset.Icc 1 (chartUpper k js i)
  have hc (us : List ℕ) (hus : us ∈ S) (i : Fin k) : wordVector k us i ∈ B i := by
    have hb := Fintype.mem_piFinset.mp (active_bad_word_in_chart_box
      chi eta W hone hzero cap k T kappa0 bad hjs hus) i
    by_cases hi : i = bad
    · subst i
      simp only [B, if_pos rfl]
      exact Finset.mem_filter.mpr ⟨by simpa [oneBadSlotBox] using hb, hfloor us hus⟩
    · simpa [B, oneBadSlotBox, hi] using hb
  have hrec := ordered_reciprocal_le_product S B (fun us hus => (badChartWords_spec hus).1) hc
  apply hrec.trans
  unfold reciprocalChartBudget
  apply Finset.prod_le_prod
  · intro i hi
    exact Finset.sum_nonneg (fun n hn => by positivity)
  · intro i hi
    by_cases hib : i = bad
    · simp only [B, if_pos hib]
      exact properTail_reciprocal_le (by unfold chartUpper; positivity) hA
    · simp only [B, if_neg hib]
      exact harmonic_Icc_le_logBudget _

/-- A finite divisor supremum on the ACTUAL complete-product range.
Its subpower estimate is a separate classical divisor-bound application. -/
def distanceDivisorEnvelope (t K : ℕ) : ℕ :=
  (Finset.Icc 1 K).sup (fun n => (ImbalancedChen.P5OriginalPrimeEndpoint.distance t n).divisors.card)

def noncollisionModulusBudget (Q : Finset ℕ) (rho : ℕ → ℂ)
    (R : ℝ) (t K : ℕ) : ℝ :=
  R * (distanceDivisorEnvelope t K : ℝ) + meanBudget Q rho

def noncollisionWords (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (T kappa0 : ℝ) (cap k : ℕ) (js : List ℕ) (bad : Fin k) (t : ℕ) : Finset (List ℕ) :=
  (badChartWords chi eta W T kappa0 cap k js bad).filter (fun us => us.prod ≠ t)

/-- Actual all-rank Family, literal chart, normalized Lambda word and
same signed row. The A^(-1/2) saving remains explicit in reciprocalChartBudget.
No final proper-power power bound, hPP or hUpper is supplied as a premise. -/
theorem family_noncollision_chart_signed_le {kStar : ℕ}
    (F : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (chi eta : ℝ → ℝ)
    (hone : ∀ x, x ≤ 1 → chi x = 1) (hzero : ∀ x, 2 ≤ x → chi x = 0)
    (hchi : ∀ x, 0 ≤ chi x ∧ chi x ≤ 1) (heta : ∀ x, |eta x| ≤ 1)
    (cap : ℕ) (kappa0 : ℝ) {js : List ℕ} (hjs : js ∈ chartBank cap k.val)
    (bad : Fin k.val) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hrho : ∀ q ∈ Q, ‖rho q‖ ≤ R)
    (hamp : ∀ us, us.length = k.val → ‖bankWeight F T k us‖ ≤ M)
    (t : ℕ) (hA : 0 < F.lower * (T : ℝ) ^ F.aStar) :
    ‖∑ us ∈ noncollisionWords chi eta (bankWeight F T k) (T : ℝ) kappa0 cap k.val js bad t,
      lambdaWord us * chartTerm chi eta (bankWeight F T k) (T : ℝ) kappa0 js us *
        signedRow Q rho t us.prod‖ ≤
      (M * (F.upper * (T : ℝ)) *
        noncollisionModulusBudget Q rho R t (Nat.ceil (F.upper * (T : ℝ)))) *
          reciprocalChartBudget (chartUpper k.val js) bad (F.lower * (T : ℝ) ^ F.aStar) := by
  let W := bankWeight F T k
  let S := noncollisionWords chi eta W (T : ℝ) kappa0 cap k.val js bad t
  let K := Nat.ceil (F.upper * (T : ℝ))
  let B := noncollisionModulusBudget Q rho R t K
  have hB : 0 ≤ B := by
    dsimp [B, noncollisionModulusBudget, meanBudget]
    positivity
  have hspec (us : List ℕ) (hus : us ∈ badChartWords chi eta W (T : ℝ) kappa0 cap k.val js bad) :
      us.length = k.val ∧ (∀ n ∈ us, 1 ≤ n) ∧
      (∀ n ∈ us, F.lower * (T : ℝ)^F.aStar ≤ (n : ℝ)) ∧
      (us.prod : ℝ) ≤ F.upper * (T : ℝ) := by
    obtain ⟨hlen, hcoord, hactive, _⟩ := badChartWords_spec hus
    have hW : W us ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hactive).2).2
    obtain ⟨hlow, hup⟩ := bankWeight_support F T k hlen hW
    exact ⟨hlen, fun n hn => (hcoord n hn).1, hlow, hup⟩
  have hfloor (us : List ℕ) (hus : us ∈ badChartWords chi eta W (T : ℝ) kappa0 cap k.val js bad) :
      F.lower * (T : ℝ)^F.aStar ≤ (us.getD bad.val 0 : ℝ) := by
    have hs := hspec us hus
    have hi : bad.val < us.length := by rw [hs.1]; exact bad.isLt
    rw [List.getD_eq_getElem _ _ hi]
    exact hs.2.2.1 _ (List.getElem_mem hi)
  have hpoint (us : List ℕ) (hus : us ∈ S) :
      ‖lambdaWord us * chartTerm chi eta W (T : ℝ) kappa0 js us * signedRow Q rho t us.prod‖ ≤
        (M * (F.upper * (T : ℝ)) * B) * (1 / (us.prod : ℝ)) := by
    obtain ⟨hbad, hne⟩ := Finset.mem_filter.mp hus
    have hs := hspec us hbad
    have hpN : 0 < us.prod := List.prod_pos (fun n hn => by have := hs.2.1 n hn; omega)
    have hp : (0 : ℝ) < us.prod := by exact_mod_cast hpN
    have hpK : us.prod ≤ K := by
      exact_mod_cast (hs.2.2.2.trans (Nat.le_ceil _))
    have hd : ((ImbalancedChen.P5OriginalPrimeEndpoint.distance t us.prod).divisors.card : ℝ) ≤
        (distanceDivisorEnvelope t K : ℝ) := by
      exact_mod_cast (Finset.le_sup (f := fun n =>
        (ImbalancedChen.P5OriginalPrimeEndpoint.distance t n).divisors.card)
        (Finset.mem_Icc.mpr ⟨hpN, hpK⟩))
    have hrow : ‖signedRow Q rho t us.prod‖ ≤ B := by
      apply (norm_signedRow_le Q rho R hR hrho t us.prod).trans
      simp only [rowBudget, if_neg hne]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hd hR) _
    have hweight : ‖lambdaWord us * chartTerm chi eta W (T : ℝ) kappa0 js us‖ ≤ M := by
      rw [norm_mul]
      exact (mul_le_mul (lambdaWord_norm_le_one us)
        (bank_chart_amplitude F T k chi eta hchi heta M hM hamp kappa0 js us hs.1)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul M)
    have hcount : 1 ≤ (F.upper * (T : ℝ)) * (1 / (us.prod : ℝ)) := by
      have hh : 1 ≤ (F.upper * (T : ℝ)) / (us.prod : ℝ) :=
        (le_div_iff₀ hp).mpr (by simpa using hs.2.2.2)
      simpa only [div_eq_mul_inv, one_div] using hh
    calc
      _ ≤ M * B := by rw [norm_mul]; exact mul_le_mul hweight hrow (norm_nonneg _) hM
      _ ≤ (M * B) * ((F.upper * (T : ℝ)) * (1 / (us.prod : ℝ))) :=
        le_mul_of_one_le_right (mul_nonneg hM hB) hcount
      _ = _ := by ring
  have hrec : (∑ us ∈ S, 1 / (us.prod : ℝ)) ≤
      reciprocalChartBudget (chartUpper k.val js) bad (F.lower * (T : ℝ)^F.aStar) := by
    have hsub : S ⊆ badChartWords chi eta W (T : ℝ) kappa0 cap k.val js bad :=
      Finset.filter_subset _ _
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => by positivity)).trans
    exact actual_bad_chart_reciprocal_le chi eta W hone hzero cap k.val (T : ℝ)
      kappa0 hjs bad hA hfloor
  calc
    _ ≤ ∑ us ∈ S, ‖lambdaWord us * chartTerm chi eta W (T : ℝ) kappa0 js us *
        signedRow Q rho t us.prod‖ := norm_sum_le _ _
    _ ≤ ∑ us ∈ S, (M * (F.upper * (T : ℝ)) * B) * (1 / (us.prod : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (M * (F.upper * (T : ℝ)) * B) * ∑ us ∈ S, 1 / (us.prod : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by
      have hup : 0 ≤ F.upper := F.upper_pos.le
      positivity)

/-- The earlier tau(t)^k multiplicity is now consumed for the ACTUAL
normalized Lambda/chart source. This is the exact complete-product=t
collision, with arbitrary rho of amplitude R on Q and no divisors(0). -/
theorem family_collision_chart_signed_le {kStar : ℕ}
    (F : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (chi eta : ℝ → ℝ) (hchi : ∀ x, 0 ≤ chi x ∧ chi x ≤ 1)
    (heta : ∀ x, |eta x| ≤ 1) (cap : ℕ) (kappa0 : ℝ)
    (js : List ℕ) (bad : Fin k.val) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hrho : ∀ q ∈ Q, ‖rho q‖ ≤ R)
    (hamp : ∀ us, us.length = k.val → ‖bankWeight F T k us‖ ≤ M)
    (t : ℕ) (ht : t ≠ 0) :
    ‖∑ us ∈ collisionWords (licence F T k) chi eta (T : ℝ) kappa0 cap js bad t,
      lambdaWord us * chartTerm chi eta (bankWeight F T k) (T : ℝ) kappa0 js us *
        signedRow Q rho t us.prod‖ ≤
      (M * (t.divisors.card ^ k.val : ℕ)) * (R * (Q.card : ℝ) + meanBudget Q rho) := by
  let S := collisionWords (licence F T k) chi eta (T : ℝ) kappa0 cap js bad t
  let B := R * (Q.card : ℝ) + meanBudget Q rho
  have hB : 0 ≤ B := by dsimp [B, meanBudget]; positivity
  have hcard : (S.card : ℝ) ≤ (t.divisors.card ^ k.val : ℕ) := by
    exact_mod_cast collisionWords_card_le_divisor_power
      (licence F T k) chi eta (T : ℝ) kappa0 cap js bad t ht
  have hpoint (us : List ℕ) (hus : us ∈ S) :
      ‖lambdaWord us * chartTerm chi eta (bankWeight F T k) (T : ℝ) kappa0 js us *
        signedRow Q rho t us.prod‖ ≤ M * B := by
    obtain ⟨hbad, hprod⟩ := Finset.mem_filter.mp hus
    have hlen := (badChartWords_spec hbad).1
    have hweight : ‖lambdaWord us *
        chartTerm chi eta (bankWeight F T k) (T : ℝ) kappa0 js us‖ ≤ M := by
      rw [norm_mul]
      exact (mul_le_mul (lambdaWord_norm_le_one us)
        (bank_chart_amplitude F T k chi eta hchi heta M hM hamp kappa0 js us hlen)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul M)
    have hrow : ‖signedRow Q rho t us.prod‖ ≤ B := by
      apply (norm_signedRow_le Q rho R hR hrho t us.prod).trans_eq
      simp only [rowBudget, hprod, if_pos rfl, B]
    rw [norm_mul]
    exact mul_le_mul hweight hrow (norm_nonneg _) hM
  calc
    _ ≤ ∑ us ∈ S, ‖lambdaWord us *
        chartTerm chi eta (bankWeight F T k) (T : ℝ) kappa0 js us *
          signedRow Q rho t us.prod‖ := norm_sum_le _ _
    _ ≤ ∑ _us ∈ S, M * B := Finset.sum_le_sum hpoint
    _ = (M * (S.card : ℝ)) * B := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (M * (t.divisors.card ^ k.val : ℕ)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hM) hB
    _ = _ := rfl

/-- Uniform actual-Family amplitude constants precede T, rank, dyadic
chart labels, rho and the independent target. Hence the noncollision
reciprocal-tail bound does not assume the desired test amplitude itself. -/
theorem family_uniform_noncollision_chart_signed {kStar : ℕ} (F : Family kStar) :
    ∃ C B : ℕ, 0 < C ∧
      ∀ (T : ℕ) (k : Fin (kStar + 1)) (chi eta : ℝ → ℝ),
        (∀ x, x ≤ 1 → chi x = 1) → (∀ x, 2 ≤ x → chi x = 0) →
        (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) → (∀ x, |eta x| ≤ 1) →
        ∀ (cap : ℕ) (kappa0 : ℝ) (js : List ℕ), js ∈ chartBank cap k.val →
        ∀ (bad : Fin k.val) (Q : Finset ℕ) (rho : ℕ → ℂ) (R : ℝ),
          0 ≤ R → (∀ q ∈ Q, ‖rho q‖ ≤ R) → ∀ t : ℕ,
          0 < F.lower * (T : ℝ)^F.aStar →
          ‖∑ us ∈ noncollisionWords chi eta (bankWeight F T k) (T : ℝ) kappa0 cap k.val js bad t,
            lambdaWord us * chartTerm chi eta (bankWeight F T k) (T : ℝ) kappa0 js us *
              signedRow Q rho t us.prod‖ ≤
            (((C : ℝ) * Real.log ((T : ℝ)+2)^B) * (F.upper * (T : ℝ)) *
              noncollisionModulusBudget Q rho R t (Nat.ceil (F.upper * (T : ℝ)))) *
                reciprocalChartBudget (chartUpper k.val js) bad (F.lower * (T : ℝ)^F.aStar) := by
  obtain ⟨C, B, hC, hamp⟩ := all_rank_bank_amplitude F
  refine ⟨C, B, hC, ?_⟩
  intro T k chi eta hone hzero hchi heta cap kappa0 js hjs bad Q rho R hR hrho t hA
  have hlog : 0 ≤ Real.log ((T : ℝ)+2) := Real.log_nonneg (by positivity)
  exact family_noncollision_chart_signed_le F T k chi eta hone hzero hchi heta
    cap kappa0 hjs bad Q rho R _ hR (by positivity) hrho (hamp T k) t hA

end
end ImbalancedChen.P5Z.ProperPowerActualReciprocalTail
