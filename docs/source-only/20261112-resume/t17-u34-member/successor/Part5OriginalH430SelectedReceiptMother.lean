import ImbalancedChen.Part5OriginalH430ReceiptFourBand
import ImbalancedChen.Part5OriginalH430FreshReceiptCounts

/-! The actual bank winner, at its physical Q and actual query. Negative
singletons are the original-receipt subpopulation of the strict children.
The three W2 occurrences keep the printed repeated coefficients. -/
namespace ImbalancedChen.Part5OriginalH430SelectedReceiptMother
noncomputable section
open Finset Real Wu2008DoubleSieve
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2AllW1FrozenReceiverFiniteAction (frozen_selected_three_prime_weight rawTripleCount original_W1_parameters)
open P2OriginalSingleChildWindowDictionary (W2Upper W2Upper_order)
open P2OriginalW2CountTupleReindex P2OriginalBankThetaMassLimits
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430SeedHistoryMass Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430SelectedFreshWindows Part5OriginalH430FreshReceiptCounts
open Part5OriginalH430OriginalReceiptMemberPullback Part5OriginalH430ReceiptFourBand
open scoped Classical BigOperators

variable {N n p : ℕ} {k : Root} {τ : ℝ} {g : Fin 430}

def strictSingle (l : Index N n k τ p g) (a : Lane) : ℝ :=
  let Q := rootQ N n k τ p
  let d := wordProduct l
  ∑ q ∈ singleChildren (rule a) N Q (oldWord l) (ceilingAt l),
    ((inheritedChild N (d*q.val) (tailProduct (levelOccurrence l)*q.val)
      (cutoff Q d (anchor a))).card : ℝ)

private theorem strict_single_sum (hN : 2≤N) (hτ : 0≤τ) (hτ' : τ≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k)
    (l : Index N n k τ p g) (a : Lane) :
    (∑ q ∈ singleChildren (rule a) N (rootQ N n k τ p) (oldWord l) (ceilingAt l),
      count N (wordProduct l*q.val) (rootMask N p)
        (cutoff (rootQ N n k τ p) (wordProduct l) (anchor a))) = strictSingle l a := by
  apply sum_congr rfl
  intro q hq
  exact (single_receipt_split hN hτ hτ' hn hp l a q hq).1

theorem selected_W2_negative (hN : 2≤N) (hτ : 0≤τ) (hτ' : τ≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) (j : Fin 36) (s : Fin 3)
    (l : Index N n k τ p g) (hl : l∈selectedLevel N n k τ p g (.inr j)) :
    let Q := rootQ N n k τ p
    let d := wordProduct l
    maskedSingle N d (rootMask N p) (cutoff Q d (originalW2At j).s0)
      (cutoff Q d (W2Upper j s)) = strictSingle l (.inr (j,s)) := by
  let Q := rootQ N n k τ p
  let d := wordProduct l
  let z := cutoff Q d (originalW2At j).s0
  let u := cutoff Q d (W2Upper j s)
  have h := selected_geometry hN hτ hτ' hn hp (.inr j) l hl
  obtain ⟨hw0,hw⟩ := W2Upper_order j s
  have hfit : u ≤ cutoff Q d (originalW2At j).s := rpow_le_rpow_of_exponent_le
    (parentWindow_logs h.1).2.1.le (one_div_le_one_div_of_le (by linarith) hw)
  have he := restored_zero (N:=N) (z:=z) hfit h.2.2.2
  let F := fun q => count N (d*q) (rootMask N p) z
  have hdiff := primeWindow_modulus_sum_difference N d z u F
  rw [he,sum_empty,sub_eq_zero] at hdiff
  exact (hdiff.symm.trans (singleton_W2 hN hτ hτ' hn hp j s l hl F)).trans
    (strict_single_sum hN hτ hτ' hn hp l (.inr (j,s)))

private theorem query_to_bank (hN : 2≤N) (hτ : 0≤τ) (hτ' : τ≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k)
    (l : Index N n k τ p g) (a : Original106Action) (hl : l∈selectedLevel N n k τ p g a) :
    let Q := rootQ N n k τ p
    let d := wordProduct l
    count N d (rootMask N p) (memberCutoff Q (levelOccurrence l)) ≤
      count N d (rootMask N p) (cutoff Q d (Part5OriginalH430BankSlotTargets.actionTarget a)) := by
  have h := selected_geometry hN hτ hτ' hn hp a l hl
  have hs := rootHistory_support (by omega : 1<N) hτ hτ' hn (original_band_prime hp)
    (original_band_geometry hN hp) (levelOccurrence_source l).1
  apply count_cutoff_antitone
  exact rpow_le_rpow_of_exponent_le (parentWindow_logs h.1).2.1.le
    (one_div_le_one_div_of_le (zero_lt_one.trans_le hs.2.2.2.1.1) h.2.1)

/-- All 36 requested W2 rows start with the actual count at this occurrence.
The four good-pair and longer positive incidences still have their common
literal mother ell in positiveMass. No sign or credit of rejected children
has been silently passed to the previous generation. -/
theorem selected_W2_receipt_mother (hN : 2≤N) (hτ : 0≤τ) (hτ' : τ≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k)
    (j : Fin 36) (l : Index N n k τ p g) (hl : l∈selectedLevel N n k τ p g (.inr j)) :
    let Q := rootQ N n k τ p
    let d := wordProduct l
    let z := fun s => cutoff Q d s
    let b := originalW2At j
    let E := rootMask N p
    5*count N d E (memberCutoff Q (levelOccurrence l)) ≤
      4*count N d E (z b.s0) + count N d E (z b.phi1) -
      strictSingle l (.inr (j,0)) - strictSingle l (.inr (j,1)) - strictSingle l (.inr (j,2)) +
      positiveMass N d E (z b.s0) (z b.phi1) (z b.phi2) (z b.phi3) (z b.s) := by
  dsimp only
  have h := selected_geometry hN hτ hτ' hn hp (.inr j) l hl
  obtain ⟨h01,h12,h23,h3s⟩ := P2AllW2SameQRawCountAction.bank_cutoff_order j
    (parentWindow_logs h.1).2.1.le
  have hw := masked_mother N (wordProduct l) (rootMask N p) h01 h12 h23 h3s
  rw [← selected_W2_negative hN hτ hτ' hn hp j 0 l hl,
    ← selected_W2_negative hN hτ hτ' hn hp j 1 l hl,
    ← selected_W2_negative hN hτ hτ' hn hp j 2 l hl]
  exact (mul_le_mul_of_nonneg_left (query_to_bank hN hτ hτ' hn hp l (.inr j) hl)
    (by norm_num : (0:ℝ)≤5)).trans hw

/-- The 70 actual W1 choices use the same frozen receiver at the target,
anchor, and negative children. The raw positive triple keeps its old
exemption modulus, including the first selected prime. -/
theorem selected_W1_receipt_mother (hN : 2≤N) (hτ : 0≤τ) (hτ' : τ≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k)
    (i : Fin 7) (j : Fin 10) (l : Index N n k τ p g)
    (hl : l∈selectedLevel N n k τ p g (.inl (i,j))) :
    let Q := rootQ N n k τ p
    let d := wordProduct l
    let z := cutoff Q d (W1Anchor j)
    let w := cutoff Q d (W1Target i)
    2*count N d (rootMask N p) (memberCutoff Q (levelOccurrence l)) ≤
      2*count N d (rootMask N p) z - strictSingle l (.inl (i,j)) +
      (rawTripleCount N d (d*N) (rootMask N p) z w : ℝ) := by
  let Q := rootQ N n k τ p
  let d := wordProduct l
  let z := cutoff Q d (W1Anchor j)
  let w := cutoff Q d (W1Target i)
  have h := selected_geometry hN hτ hτ' hn hp (.inl (i,j)) l hl
  obtain ⟨hs,ht,_⟩ := original_W1_parameters i j
  have hzw : z ≤ w := rpow_le_rpow_of_exponent_le (parentWindow_logs h.1).2.1.le
    (one_div_le_one_div_of_le (by linarith) ht)
  have hw : 2*count N d (rootMask N p) w ≤ 2*count N d (rootMask N p) z -
      (∑ q∈primeWindow (d*N) z w, count N (d*q) (rootMask N p) z) +
      (rawTripleCount N d (d*N) (rootMask N p) z w : ℝ) := by
    exact_mod_cast frozen_selected_three_prime_weight N d (rootMask N p) hzw
  have hsum := singleton_W1 hN hτ hτ' hn hp i j l hl (fun q => count N (d*q) (rootMask N p) z)
  change (∑ q∈primeWindow (d*N) z w, count N (d*q) (rootMask N p) z) = _ at hsum
  rw [hsum,strict_single_sum hN hτ hτ' hn hp l (.inl (i,j))] at hw
  exact (mul_le_mul_of_nonneg_left (query_to_bank hN hτ hτ' hn hp l (.inl (i,j)) hl)
    (by norm_num : (0:ℝ)≤2)).trans hw

end
end ImbalancedChen.Part5OriginalH430SelectedReceiptMother
