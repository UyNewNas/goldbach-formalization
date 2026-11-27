import ImbalancedChen.P3OriginalU5JointWarmWalls
import ImbalancedChen.P3OriginalU5JointCellCoefficient
import ImbalancedChen.P3OriginalU5WarmRoundingPayment

/-!
Reciprocal-totient mass of actual original pairs and complete rough
divisors whose physical joint fine cell contains an opposite decision.
The arithmetic tuple keeps both exterior places and every rough prime.
-/

namespace ImbalancedChen.P3OriginalU5JointPrimeWallPayment

noncomputable section
open scoped Classical BigOperators List
open P2LowerCapPlanIntegerRetention (coordinate)
open P2OriginalPairSourceReceiver (PairRange pairPlan ceiling)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2LowerCanonicalRetainedTrace (canonical_subword_of_universe)
open P3OriginalU5CommonPhysicalRoot
open P3OriginalU5JointCellCoefficient (Point carrier roughCarrier cell jointLabel)
open P3OriginalU5JointWarmWalls (markedWord original_U5_joint_policy_disagreement_wall)
open P3OriginalU5WarmWordWalls (wordPoint ofFn_wordPoint)
open P3OriginalU5WarmMixedWallCover (wallForm wallCenter)
open P3OriginalU5WarmRoundingPayment (ProperWall rowConstant rowConstant_pos wall_factor_le_rowConstant)
open P3OriginalU5CoarseRootV (Label)
open P5OriginalU5CausalFinite (attachmentNu smallCutoff cutoff pairSupport attachment_gates)
open Part5OriginalUpsilon5CausalDictionary (a h)

def word (x : Point) : List ℕ := x.1.2 :: x.1.1 :: x.2.primeFactorsList.reverse

def tuple (r : ℕ) (x : Point) : Fin (r + 2) → ℕ :=
  primeHistoryTuple (r + 2) (word x).reverse

theorem tuple_ofFn {r : ℕ} {x : Point} (hr : x.2.primeFactorsList.length = r) :
    List.ofFn (tuple r x) = word x := by
  unfold tuple
  rw [primeHistoryTuple_ofFn (by simp [word, hr]), List.reverse_reverse]

private theorem word_data {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) {x : Point} (hx : x ∈ carrier N epsilon) :
    (word x).Pairwise (· > ·) ∧
      (∀ p ∈ word x, p.Prime ∧ ¬p ∣ N ∧
        smallCutoff N epsilon ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ h) ∧
      (word x).prod = (x.1.1 * x.1.2) * x.2 := by
  obtain ⟨ht, hd⟩ := Finset.mem_product.mp hx
  obtain ⟨hpr, hlo, h12, hhi⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpr
  obtain ⟨_, hp', hpc⟩ := mem_chenAdditivePrimeCarrier.mp hp
  obtain ⟨_, hq', hqc⟩ := mem_chenAdditivePrimeCarrier.mp hq
  obtain ⟨hs, hprod⟩ := canonical_subword_of_universe N (Nat.ceil (cutoff N))
    (smallCutoff N epsilon) (cutoff N) hd
  have hw := (attachment_gates hN he he8).2.2
  have h12r : (x.1.1 : ℝ) < x.1.2 := by exact_mod_cast h12
  have hrough (p : ℕ) (hp : p ∈ x.2.primeFactorsList.reverse) : p < x.1.1 := by
    have hl := (mem_roughPrimeUniverse_upper (hs.subset hp)).trans_le hlo
    exact_mod_cast hl
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_cons.mpr
    refine ⟨?_, List.pairwise_cons.mpr ⟨fun p hp => hrough p hp,
      (roughPrimeUniverse_pairwise_gt _ _ _ _).sublist hs⟩⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h12
    · exact (hrough p hp).trans h12
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hq', hq'.coprime_iff_not_dvd.mp hqc, (hw.trans hlo).trans h12r.le, hhi⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hp', hp'.coprime_iff_not_dvd.mp hpc, hw.trans hlo, h12r.trans hhi⟩
    · have hm := hs.subset hp
      exact ⟨mem_roughPrimeUniverse_prime hm, mem_roughPrimeUniverse_not_dvd hm,
        mem_roughPrimeUniverse_lower hm, (mem_roughPrimeUniverse_upper hm).trans_le
          (hlo.trans (h12r.trans hhi).le)⟩
  · change x.1.2 * (x.1.1 * x.2.primeFactorsList.reverse.prod) = _
    rw [hprod]
    ring

abbrev boxTuples (N : ℕ) (epsilon : ℝ) (r : ℕ) :=
  actualPrimeBoxTuples N (fun _ : Fin (r + 2) => attachmentNu * epsilon ^ 2) (fun _ => h)

theorem tuple_mem_box {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) {r : ℕ} {x : Point}
    (hx : x ∈ carrier N epsilon) (hr : x.2.primeFactorsList.length = r) :
    tuple r x ∈ boxTuples N epsilon r := by
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  apply (word_data hN he he8 hx).2.1
  rw [← tuple_ofFn hr]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem tuple_injOn {N : ℕ} {epsilon : ℝ} {r : ℕ} {x y : Point}
    (hx : x ∈ carrier N epsilon) (hy : y ∈ carrier N epsilon)
    (hr : x.2.primeFactorsList.length = r) (hs : y.2.primeFactorsList.length = r)
    (heq : tuple r x = tuple r y) : x = y := by
  have hh := congrArg List.ofFn heq
  rw [tuple_ofFn hr, tuple_ofFn hs] at hh
  obtain ⟨h₂, hh'⟩ := List.cons.inj hh
  obtain ⟨h₁, hrough⟩ := List.cons.inj hh'
  have hd := congrArg List.prod hrough
  rw [(canonical_subword_of_universe N _ _ _ (Finset.mem_product.mp hx).2).2,
      (canonical_subword_of_universe N _ _ _ (Finset.mem_product.mp hy).2).2] at hd
  exact Prod.ext (Prod.ext h₁ h₂) hd

def rowWeight (x : Point) : ℝ :=
  (1 / (Nat.totient (x.1.1 * x.1.2) : ℝ)) * (1 / (Nat.totient x.2 : ℝ))

theorem rowWeight_eq_full {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) {x : Point} (hx : x ∈ carrier N epsilon) :
    rowWeight x = 1 / (Nat.totient ((x.1.1 * x.1.2) * x.2) : ℝ) := by
  obtain ⟨hsort, hslots, hprod⟩ := word_data hN he he8 hx
  have hs := list_prod_squarefree_of_nodup_primes (word x)
    (hsort.imp (fun hz => ne_of_gt hz)) (fun p hp => (hslots p hp).1)
  rw [hprod] at hs
  simp only [rowWeight, Nat.totient_mul (Nat.coprime_of_squarefree_mul hs),
    Nat.cast_mul, one_div, mul_inv_rev]
  ring

theorem rowWeight_eq_tuple {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) {r : ℕ} {x : Point}
    (hx : x ∈ carrier N epsilon) (hr : x.2.primeFactorsList.length = r) :
    rowWeight x = ∏ i, 1 / ((tuple r x i : ℝ) - 1) := by
  obtain ⟨hsort, _, hprod⟩ := word_data hN he he8 hx
  have hp : (∏ i, tuple r x i) = (x.1.1 * x.1.2) * x.2 := by
    rw [← List.prod_ofFn, tuple_ofFn hr, hprod]
  have hsorted : (List.ofFn (tuple r x)).Pairwise (· > ·) := (tuple_ofFn hr).symm ▸ hsort
  have hinj : Function.Injective (tuple r x) :=
    StrictAnti.injective (show StrictAnti (tuple r x) from List.pairwise_ofFn.mp hsorted)
  rw [← actualPrimeBoxTuple_reciprocalTotient (tuple_mem_box hN he he8 hx hr) hinj, hp]
  exact rowWeight_eq_full hN he he8 hx

/-- Every charged row has an actual opposite word inside its complete
joint cell. The rival rough rank is displayed explicitly. -/
def chargedRows (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m N r : ℕ) (epsilon tau : ℝ) : Finset Point :=
  (carrier N epsilon).filter fun x => x.2.primeFactorsList.length = r ∧
    ∃ y ∈ cell R m N epsilon tau x, y.2.primeFactorsList.length = r ∧
      ¬(policy R bank b m N x.1 x.2.primeFactorsList = true ↔
        policy R bank b m N y.1 y.2.primeFactorsList = true)

def chargedTuples (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m N r : ℕ) (epsilon tau : ℝ) : Finset (Fin (r + 2) → ℕ) :=
  (chargedRows R bank b m N r epsilon tau).image (tuple r)

def chargedTupleMass (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m N r : ℕ) (epsilon tau : ℝ) : ℝ :=
  ∑ p ∈ chargedTuples R bank b m N r epsilon tau, ∏ i, 1 / ((p i : ℝ) - 1)

def chargedRowMass (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m N r : ℕ) (epsilon tau : ℝ) : ℝ :=
  ∑ x ∈ chargedRows R bank b m N r epsilon tau, rowWeight x

theorem chargedRowMass_eq_tupleMass (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m r : ℕ) {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) (tau : ℝ) :
    chargedRowMass R bank b m N r epsilon tau = chargedTupleMass R bank b m N r epsilon tau := by
  unfold chargedTupleMass chargedTuples
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hsrc, hr, _⟩ := Finset.mem_filter.mp hx
    exact rowWeight_eq_tuple hN he he8 hsrc hr
  · intro x hx y hy heq
    obtain ⟨hsrc, hr, _⟩ := Finset.mem_filter.mp hx
    obtain ⟨hsrc', hr', _⟩ := Finset.mem_filter.mp hy
    exact tuple_injOn hsrc hsrc' hr hr' heq

/-- Every joint wall centre is fixed once the finite root owner and the
actual checked bank have been chosen. -/
abbrev Catalogue (R : PairRange) (m mesh r : ℕ) := Label R m × ProperWall mesh (r + 2)

def forms (R : PairRange) (m mesh r : ℕ) (i : Fin (Fintype.card (Catalogue R m mesh r))) :
    (Fin (r + 2) → ℝ) →L[ℝ] ℝ :=
  wallForm ((Fintype.equivFin (Catalogue R m mesh r)).symm i).2.val

def centers (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
    (m r : ℕ) (i : Fin (Fintype.card (Catalogue R m mesh r))) : ℝ :=
  let z := (Fintype.equivFin (Catalogue R m mesh r)).symm i
  let s := physicalSeed R b z.1
  wallCenter (pairPlan R bank (2 * b) s) (R.epsilon : ℝ) (ceiling : ℝ) s 0 z.2.val

private theorem tuple_log {r N : ℕ} {x : Point} (hr : x.2.primeFactorsList.length = r) :
    wordPoint (r + 2) (markedWord N x.1 (x.2.primeFactorsList.reverse.map (coordinate N))) =
      actualPrimeTupleLog N (tuple r x) := by
  apply List.ofFn_injective
  rw [ofFn_wordPoint _ (by simp [markedWord, hr])]
  change markedWord N x.1 (x.2.primeFactorsList.reverse.map (coordinate N)) =
    List.ofFn ((coordinate N) ∘ tuple r x)
  rw [← List.map_ofFn, tuple_ofFn hr]
  rfl

theorem charged_row_mem_wall (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m r : ℕ) {N : ℕ} (hN : 2 ≤ N) (epsilon : ℝ) {tau : ℝ} (htau : 0 < tau)
    {x : Point} (hx : x ∈ chargedRows R bank b m N r epsilon tau) :
    actualPrimeTupleLog N (tuple r x) ∈
      primeAffineWallStrip (forms R m mesh r) (centers R bank b m r) (rowConstant mesh (r + 2) * tau) := by
  obtain ⟨hxsrc, hr, y, hy, hr', hdiff⟩ := Finset.mem_filter.mp hx
  obtain ⟨hysrc, hlabel⟩ := Finset.mem_filter.mp hy
  have ht := (Finset.mem_product.mp hxsrc).1
  have hu := (Finset.mem_product.mp hysrc).1
  have hj := P3OriginalU5JointCellCoefficient.same_owner R m hN ht hu hlabel.symm
  have hfine :
      (markedWord N x.1 (x.2.primeFactorsList.reverse.map (coordinate N))).map
        (fun v => (⌊v / tau⌋ : ℤ)) =
      (markedWord N y.1 (y.2.primeFactorsList.reverse.map (coordinate N))).map
        (fun v => (⌊v / tau⌋ : ℤ)) := by
    have hw := P3OriginalU5JointCellCoefficient.same_fine_word R m N tau hlabel.symm
    have hfun : P2LowerFiniteCellRounding.primeLabel N tau =
        fun p : ℕ => (⌊coordinate N p / tau⌋ : ℤ) := rfl
    rw [hfun] at hw
    simpa only [markedWord, List.map_cons, List.map_map, Function.comp_def] using hw
  obtain ⟨_, w, hw, hdist⟩ := original_U5_joint_policy_disagreement_wall
    R bank b m hN hN ht hu hj x.2.primeFactorsList.reverse y.2.primeFactorsList.reverse
    (by simpa only [List.length_reverse] using hr) (by simpa only [List.length_reverse] using hr')
    htau hfine (by simpa only [List.reverse_reverse] using hdiff)
  rw [tuple_log hr] at hdist
  let pw : ProperWall mesh (r + 2) := ⟨w, hw⟩
  let z : Catalogue R m mesh r := (rowOwner R m hN ht, pw)
  refine ⟨(Fintype.equivFin (Catalogue R m mesh r)) z, ?_⟩
  simpa only [forms, centers, Equiv.symm_apply_apply, z, pw] using
    hdist.trans (mul_le_mul_of_nonneg_right (wall_factor_le_rowConstant pw) htau.le)

theorem chargedTupleMass_le_strip (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m r : ℕ) {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) {tau delta : ℝ} (htau : 0 < tau)
    (hwidth : rowConstant mesh (r + 2) * tau ≤ delta) :
    chargedTupleMass R bank b m N r epsilon tau ≤ actualPrimeAffineWallStripMass N
      (fun _ : Fin (r + 2) => attachmentNu * epsilon ^ 2) (fun _ => h)
      (forms R m mesh r) (centers R bank b m r) delta := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hsrc, hr, _⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, hw⟩ := charged_row_mem_wall R bank b m r hN epsilon htau hx
    exact Finset.mem_filter.mpr ⟨tuple_mem_box hN he he8 hsrc hr, i, hw.trans hwidth⟩
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- A single positive width and a single threshold pay every later
target and every finer rounding. The sum is the original two-prime
reciprocal-totient weight times the complete rough-divisor weight. -/
theorem exists_joint_charged_row_payment (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m r : ℕ) {epsilon : ℝ} (he : 0 < epsilon) (he8 : epsilon < 1 / 8)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ {N : ℕ}, N0 ≤ N → ∀ {tau : ℝ}, 0 < tau → tau ≤ tau0 →
        chargedRowMass R bank b m N r epsilon tau < eta := by
  have homega : 0 < attachmentNu * epsilon ^ 2 := by dsimp only [attachmentNu]; positivity
  have hnu : 0 < attachmentNu := by norm_num [attachmentNu]
  have hab : attachmentNu * epsilon ^ 2 < h := by
    calc
      _ < attachmentNu * (1 / 8 : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_left (pow_lt_pow_left₀ he8 he.le (by norm_num)) hnu
      _ < h := by norm_num [attachmentNu, h]
  have hproper (i : Fin (Fintype.card (Catalogue R m mesh r))) : forms R m mesh r i ≠ 0 :=
    ((Fintype.equivFin (Catalogue R m mesh r)).symm i).2.property
  obtain ⟨delta, hdelta, N0, hN0, hpay⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    homega hab (forms R m mesh r) (centers R bank b m r) hproper eta heta
  have hV := rowConstant_pos mesh (r + 2)
  refine ⟨delta / rowConstant mesh (r + 2), div_pos hdelta hV, N0, hN0, ?_⟩
  intro N hN tau ht ht'
  have hwidth : rowConstant mesh (r + 2) * tau ≤ delta := by
    simpa only [mul_comm] using (le_div_iff₀ hV).mp ht'
  rw [chargedRowMass_eq_tupleMass R bank b m r (hN0.trans hN) he he8 tau]
  exact (chargedTupleMass_le_strip R bank b m r (hN0.trans hN) he he8 ht hwidth).trans_lt
    (hpay N hN)

theorem mem_chargedRows_of_ne_raw (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m r : ℕ) {N : ℕ} (hN : 2 ≤ N) (epsilon tau : ℝ) {x : Point}
    (hx : x ∈ carrier N epsilon) (hr : x.2.primeFactorsList.length = r)
    (hne : P3OriginalU5JointCellCoefficient.coefficient R bank b m N epsilon tau x ≠
      P3OriginalU5JointCellCoefficient.rawCoefficient R bank b m N epsilon x) :
    x ∈ chargedRows R bank b m N r epsilon tau := by
  obtain ⟨y, hy, hneq⟩ := P3OriginalU5JointCellCoefficient.gate_difference_of_coefficient_ne_raw
    R bank b m hN epsilon tau hx hne
  have hlen := P3OriginalU5JointCellCoefficient.same_rough_length R m N tau (Finset.mem_filter.mp hy).2
  exact Finset.mem_filter.mpr ⟨hx, hr, y, hy, hlen.trans hr, hneq⟩

def rankRoundingLoss (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m N r : ℕ) (epsilon tau : ℝ) : ℝ :=
  ∑ x ∈ (carrier N epsilon).filter (fun x => x.2.primeFactorsList.length = r),
    |P3OriginalU5JointCellCoefficient.coefficient R bank b m N epsilon tau x -
      P3OriginalU5JointCellCoefficient.rawCoefficient R bank b m N epsilon x| * rowWeight x

/-- The actual joint signed coefficient gap, in absolute value, is
charged only at mixed words of the displayed rough rank. -/
theorem rankRoundingLoss_le (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m r : ℕ) {N : ℕ} (hN : 2 ≤ N) (epsilon tau : ℝ) :
    rankRoundingLoss R bank b m N r epsilon tau ≤
      2 * chargedRowMass R bank b m N r epsilon tau := by
  let C := chargedRows R bank b m N r epsilon tau
  let A := (carrier N epsilon).filter (fun x => x.2.primeFactorsList.length = r)
  let cf := P3OriginalU5JointCellCoefficient.coefficient R bank b m N epsilon tau
  let raw := P3OriginalU5JointCellCoefficient.rawCoefficient R bank b m N epsilon
  have hs : C ⊆ A := fun _ hx => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩
  change (∑ x ∈ A, |cf x - raw x| * rowWeight x) ≤ 2 * ∑ x ∈ C, rowWeight x
  calc
    _ = ∑ x ∈ C, |cf x - raw x| * rowWeight x := by
      symm
      apply Finset.sum_subset hs
      intro x hx hxc
      obtain ⟨hkey, hr⟩ := Finset.mem_filter.mp hx
      have heq : cf x = raw x := by
        by_contra hn
        exact hxc (mem_chargedRows_of_ne_raw R bank b m r hN epsilon tau hkey hr hn)
      simp only [heq, sub_self, abs_zero, zero_mul]
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      have hcf := P3OriginalU5JointCellCoefficient.coefficient_abs_le_one R bank b m N epsilon tau x
      have hraw : |raw x| ≤ 1 := fixedEvenRoughCoefficient_abs_le_one _ _ _ _ _ _
      have htri := abs_sub_le (cf x) 0 (raw x)
      simp only [sub_zero, zero_sub, abs_neg] at htri
      change |cf x| ≤ 1 at hcf
      apply mul_le_mul_of_nonneg_right (by linarith only [hcf, hraw, htri])
      dsimp only [rowWeight]
      positivity

end
end ImbalancedChen.P3OriginalU5JointPrimeWallPayment
