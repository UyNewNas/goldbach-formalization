import ImbalancedChen.P3OriginalU5AllSourceSquares
import ImbalancedChen.OrdinaryRosserContinuation
import ImbalancedChen.RosserShortPrefixAdmissibility

/-! The ordinary lower Rosser predicate at the incoming cap of each reachable
marked U5 prefix. Histories in this module put the most recently selected
prime first, as in the literal first-exit polynomial. -/

namespace ImbalancedChen.P3OriginalU5WarmRosserAdmission

noncomputable section
open scoped Classical List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer P2OriginalSelectedPairNativeData
open P2OriginalPairSourceReceiver P3OriginalU5AllSourceSquares
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalLowerSelectedCapConstructor (prefixCode)
open P2OriginalPairBufferedRootProvenance
open P5OriginalU5CausalFinite (pairSupport cutoff coordinates coordinates_mem_triangle)
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser (UpperAdmissibleSet)

private theorem checkedCap_ge (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (rank : Fin 6) (parent : ℝ) (code : P2OriginalLowerSelectedCapConstructor.Code mesh) :
    parent ≤ checkedCap R bank delta rank parent code := by
  unfold checkedCap checkedChoice
  cases h : select R bank delta rank (prefixCode rank.val code) with
  | none => simp [h, CapChoice.freeze]
  | some branch =>
    by_cases hc : freshCheck R rank (prefixCode rank.val code) delta parent branch
    · simpa [h, hc, CapChoice.freeze] using hc.1.le
    · simp [h, hc, CapChoice.freeze]

/-- The three caps along any actual length-three rough word can all be read
on its last code: every lookup uses only its own stored prefix. -/
private theorem first_three_caps (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (p q r : ℕ) :
    let T := actualTrace R bank delta seed N t
    (T []).cap ≤ (T [p]).cap ∧ (T [p]).cap ≤ (T [p,q]).cap ∧
      (T [p,q]).cap ≤ (T [p,q,r]).cap := by
  let x := coordinate N
  let c3 := codeAt R mesh 3 [x t.2, x t.1, x p]
  let c4 := codeAt R mesh 4 [x t.2, x t.1, x p, x q]
  let c5 := codeAt R mesh 5 [x t.2, x t.1, x p, x q, x r]
  have h35 : prefixCode 3 c3 = prefixCode 3 c5 := by funext i; fin_cases i <;> rfl
  have h34 : prefixCode 3 c4 = prefixCode 3 c5 := by funext i; fin_cases i <;> rfl
  have h45 : prefixCode 4 c4 = prefixCode 4 c5 := by funext i; fin_cases i <;> rfl
  have same_choice (rank : Fin 6) (parent : ℝ)
      {c d : P2OriginalLowerSelectedCapConstructor.Code mesh}
      (heq : prefixCode rank.val c = prefixCode rank.val d) :
      checkedChoice R bank delta rank parent c = checkedChoice R bank delta rank parent d := by
    dsimp only [checkedChoice]
    rw [heq]
  have h3c : cap3 R bank delta seed c3 = cap3 R bank delta seed c5 := by
    exact congrArg (CapChoice.freeze seed) (same_choice 3 seed h35)
  have h3d : cap3 R bank delta seed c4 = cap3 R bank delta seed c5 := by
    exact congrArg (CapChoice.freeze seed) (same_choice 3 seed h34)
  let T := actualTrace R bank delta seed N t
  have h3 : (T [p]).cap = cap3 R bank delta seed c5 := by
    change cap3 R bank delta seed c3 = _
    exact h3c
  have h4 : (T [p,q]).cap = cap4 R bank delta seed c5 := by
    change (checkedChoice R bank delta 4 (cap3 R bank delta seed c4) c4).freeze
      (T [p]).cap = _
    rw [h3, h3d]
    exact congrArg (CapChoice.freeze (cap3 R bank delta seed c5)) (same_choice 4 _ h45)
  have h5 : (T [p,q,r]).cap = cap5 R bank delta seed c5 :=
    pair_run_three_cap R bank delta seed (x t.2) (x t.1) (x p) (x q) (x r)
  change seed ≤ (T [p]).cap ∧ (T [p]).cap ≤ (T [p,q]).cap ∧
    (T [p,q]).cap ≤ (T [p,q,r]).cap
  rw [h3, h4, h5]
  exact ⟨checkedCap_ge R bank delta 3 seed c5,
    checkedCap_ge R bank delta 4 _ c5, checkedCap_ge R bank delta 5 _ c5⟩

abbrev incoming (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) : Trace :=
  actualTrace R bank (2*b) (rootSeed false b N t) N t H.reverse

def rowLevel (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) : ℝ :=
  (N : ℝ) ^ (incoming R bank b N t H).cap / ((t.1 : ℝ) * t.2)

private theorem incoming_cons (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) (q : ℕ) :
    incoming R bank b N t (q::H) =
      step (pairPlan R bank (2*b) (rootSeed false b N t)) (R.epsilon : ℝ)
        (ceiling : ℝ) (incoming R bank b N t H) (coordinate N q) := by
  simpa only [incoming, List.reverse_cons] using
    actualTrace_snoc R bank (2*b) (rootSeed false b N t) N t H.reverse q

private theorem incoming_cap_le (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) (q : ℕ) :
    (incoming R bank b N t H).cap ≤ (incoming R bank b N t (q::H)).cap := by
  cases H with
  | nil => exact (first_three_caps R bank (2*b) (rootSeed false b N t) N t q 0 0).1
  | cons p H =>
    cases H with
    | nil => exact (first_three_caps R bank (2*b) (rootSeed false b N t) N t p q 0).2.1
    | cons r H =>
      cases H with
      | nil => exact (first_three_caps R bank (2*b) (rootSeed false b N t) N t r p q).2.2
      | cons s tail =>
        rw [incoming_cons R bank b N t (p::r::s::tail) q]
        apply le_of_eq
        symm
        apply no_new_cap_outside_345
        simp only [incoming, actualTrace_word, List.length_append, List.length_cons,
          List.length_nil, List.length_map, List.length_reverse]
        omega

private theorem root_cutoff_lt (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb : b ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    cutoff N < rowLevel R bank b N t [] := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hc, _, _, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hc
  have hp0 := (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
  have hq0 := (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  have hcoords : coordinates N t = pairPoint N t := by funext i; fin_cases i <;> rfl
  have hx := coordinates_mem_triangle hN ht
  rw [hcoords] at hx
  have hroot := (fifth_buffered_root_squares hx b hb).2.2
  change coordinate N t.2 + coordinate N t.1 + 2*(417/5000 : ℝ) <
    rootSeed false b N t at hroot
  have hlt : (417/5000 : ℝ) + coordinate N t.1 + coordinate N t.2 <
      rootSeed false b N t := by linarith
  have hh := Real.rpow_lt_rpow_of_exponent_lt hNr hlt
  rw [Real.rpow_add (zero_lt_one.trans hNr), Real.rpow_add (zero_lt_one.trans hNr),
    coordinate_power hNr hp0, coordinate_power hNr hq0] at hh
  change cutoff N < (N : ℝ) ^ rootSeed false b N t / ((t.1 : ℝ) * t.2)
  apply (lt_div_iff₀ (mul_pos (Nat.cast_pos.mpr hp0) (Nat.cast_pos.mpr hq0))).mpr
  simpa only [cutoff, mul_assoc] using hh

private theorem parity_bit (H : List ℕ) : evenListLength H = decide (Even H.length) := by
  induction H with
  | nil => rfl
  | cons p ps ih => simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

private theorem local_test (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (H : List ℕ) (q : ℕ) (hq : q.Prime)
    (hprime : ∀ p ∈ H, p.Prime) (hsort : (q::H).Pairwise (· < ·))
    (hqQ : (q : ℝ) < rowLevel R bank b N t H)
    (hadm : ordinaryRosserPrefixAdmissible true (rowLevel R bank b N t H) H) :
    admission (incoming R bank b N t H) (coordinate N q) ↔
      ordinaryRosserPrefixAdmissible true (rowLevel R bank b N t H) (q::H) := by
  let T := incoming R bank b N t H
  let Q := rowLevel R bank b N t H
  have hlen : T.word.length = H.length + 2 := by
    simp only [T, incoming, actualTrace_word, List.length_append, List.length_cons,
      List.length_nil, List.length_map, List.length_reverse]
    omega
  have hn : T.word.length ≠ 0 := by omega
  by_cases he : Even H.length
  · have hi : (T.word.length + 1) % 2 ≠ 0 := by rw [Nat.even_iff] at he; omega
    have hg : admission T (coordinate N q) := by simp [admission, hn, hi]
    have hh := ordinaryParityRosserPolicy_eq_full_on_valid_prefix true Q H
      (evenListLength H) q hadm rfl hq (fun _ => hqQ) hsort
    have ho : ordinaryParityRosserPolicy true Q (!(evenListLength H)) (q::H) = true := by
      simp [parity_bit, he]
    rw [hh] at ho
    exact iff_of_true hg (of_decide_eq_true ho)
  · have hi : (T.word.length + 1) % 2 = 0 := by rw [Nat.even_iff] at he; omega
    have hP : (0 : ℝ) < H.prod := by
      exact_mod_cast List.prod_pos (fun p hp => (hprime p hp).pos)
    have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    obtain ⟨hc, _, _, _⟩ := Finset.mem_filter.mp ht
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hc
    have h₁ := (mem_chenAdditivePrimeCarrier.mp hp₁).2.1.pos
    have h₂ := (mem_chenAdditivePrimeCarrier.mp hp₂).2.1.pos
    have hB := mul_pos (Nat.cast_pos.mpr h₁ : (0 : ℝ) < t.1) (Nat.cast_pos.mpr h₂ : (0 : ℝ) < t.2)
    have hsep : ∀ s ∈ [q], ∀ p ∈ H, s < p := by
      intro s hs
      obtain rfl := List.mem_singleton.mp hs
      exact (List.pairwise_cons.mp hsort).1
    have hsplit := ordinaryRosserPrefixAdmissible_append_iff true Q H [q] hadm
      (List.pairwise_cons.mp hsort).2.nodup hP hsep
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
    have hp3 : (q : ℝ) ≤ (q : ℝ)^3 := by
      calc (q : ℝ) = (q : ℝ)^1 := (pow_one _).symm
           _ ≤ _ := pow_le_pow_right₀ hq1 (by norm_num)
    have hr : ordinaryRosserPrefixAdmissible true Q (q::H) ↔
        (q : ℝ)^3 < Q / (H.prod : ℝ) := by
      change ordinaryRosserPrefixAdmissible true Q ([q] ++ H) ↔ _
      rw [hsplit]
      simp only [ordinaryRosserResidualLower, if_neg he, Bool.not_true,
        ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false]
      have hc : UpperAdmissibleSet (Q / (H.prod : ℝ)) [q].toFinset ↔
          (q : ℝ)^3 < Q / (H.prod : ℝ) := by
        simp [UpperAdmissibleSet, Finset.filter_singleton, pow_succ, mul_comm]
      simp only [hc, List.prod_cons, List.prod_nil, mul_one]
      exact ⟨And.right, fun h => ⟨hp3.trans_lt h, h⟩⟩
    have hword : T.word = physicalWord N (H ++ [t.1,t.2]) := by
      simp [T, incoming, actualTrace_word, physicalWord, List.reverse_append]
    have hpos : ∀ p ∈ H ++ [t.1,t.2], 0 < p := by
      intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact (hprime p h).pos
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> assumption
    change admission T (coordinate N q) ↔ ordinaryRosserPrefixAdmissible true Q (q::H)
    rw [hr]
    simp only [admission, if_neg hn, if_pos hi]
    rw [hword, cube_test_integer_iff hNr hq.pos (H ++ [t.1,t.2]) hpos T.cap,
      lt_div_iff₀ hP]
    change _ ↔ (q : ℝ)^3 * (H.prod : ℝ) < (N : ℝ)^T.cap / ((t.1 : ℝ)*t.2)
    rw [lt_div_iff₀ hB]
    simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, Nat.cast_mul]
    ring_nf

private theorem reachable (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb : b ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (H : List ℕ)
    (hp : ∀ p ∈ H, p.Prime ∧ (p : ℝ) < cutoff N) (hs : H.Pairwise (· < ·))
    (ha : (incoming R bank b N t H).accepted = true) :
    cutoff N < rowLevel R bank b N t H ∧
      ordinaryRosserPrefixAdmissible true (rowLevel R bank b N t H) H := by
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  induction H with
  | nil =>
    have hc := root_cutoff_lt R bank b hb hN ht
    have hz : 1 ≤ cutoff N := Real.one_le_rpow hNr (by norm_num)
    exact ⟨hc, ordinaryRosserPrefixAdmissible_nil true (hz.trans_lt hc)⟩
  | cons q H ih =>
    obtain ⟨hq, hqz⟩ := hp q (List.mem_cons_self)
    have htail := fun p (h : p ∈ H) => hp p (List.mem_cons_of_mem q h)
    rw [incoming_cons, step_accepted_iff] at ha
    obtain ⟨hc, hadm⟩ := ih htail (List.pairwise_cons.mp hs).2 ha.1
    have hnext := (local_test R bank b hN ht H q hq
      (fun p h => (htail p h).1) hs (hqz.trans hc) hadm).mp ha.2
    have hlevel : rowLevel R bank b N t H ≤ rowLevel R bank b N t (q::H) := by
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hNr (incoming_cap_le R bank b N t H q))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    exact ⟨hc.trans_le hlevel, ordinaryRosserPrefixAdmissible_mono true (q::H) hlevel hnext⟩

/-- A reachable prefix has all ordinary lower Rosser tests at its current
residual level, including when its remaining prime carrier is empty. -/
theorem original_U5_warm_rosser_prefix_admissible (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (b : ℚ) (hb : b ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (enum : ℕ) (w : ℝ) (H : List ℕ)
    (hsub : H.reverse <+ roughPrimeUniverse N enum w (cutoff N))
    (hacc : (incoming R bank b N t H).accepted = true) :
    cutoff N < rowLevel R bank b N t H ∧
      ordinaryRosserPrefixAdmissible true (rowLevel R bank b N t H) H := by
  apply reachable R bank b hb hN ht H _ _ hacc
  · intro p hp
    have hm := hsub.subset (List.mem_reverse.mpr hp)
    exact ⟨mem_roughPrimeUniverse_prime hm, mem_roughPrimeUniverse_upper hm⟩
  · simpa only [List.pairwise_reverse] using
      (roughPrimeUniverse_pairwise_gt N enum w (cutoff N)).sublist hsub

/-- Both assertions use the same incoming level with the two external marked
primes removed once. The ordinary prefix tests are derived from acceptance.
All labels come from the actual rough-prime enumeration. -/
theorem original_U5_warm_rosser_admission (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (b : ℚ) (hb : b ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (enum : ℕ) (w : ℝ)
    (H : List ℕ) (q : ℕ) (hsub : (q::H).reverse <+ roughPrimeUniverse N enum w (cutoff N))
    (hacc : (incoming R bank b N t H).accepted = true) :
    ordinaryRosserPrefixAdmissible true (rowLevel R bank b N t H) H ∧
      (admission (incoming R bank b N t H) (coordinate N q) ↔
       ordinaryParityRosserPolicy true (rowLevel R bank b N t H)
         (!(evenListLength H)) (q::H) = true) := by
  have hs : (q::H).Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using
      (roughPrimeUniverse_pairwise_gt N enum w (cutoff N)).sublist hsub
  have hdata : ∀ p ∈ q::H, p.Prime ∧ (p : ℝ) < cutoff N := by
    intro p hp
    have hm := hsub.subset (List.mem_reverse.mpr hp)
    exact ⟨mem_roughPrimeUniverse_prime hm, mem_roughPrimeUniverse_upper hm⟩
  have htail := fun p (h : p ∈ H) => hdata p (List.mem_cons_of_mem q h)
  obtain ⟨hz, hA⟩ := reachable R bank b hb hN ht H htail (List.pairwise_cons.mp hs).2 hacc
  obtain ⟨hq, hqz⟩ := hdata q List.mem_cons_self
  have hqQ := hqz.trans hz
  refine ⟨hA, ?_⟩
  rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix true _ H (evenListLength H) q
    hA rfl hq (fun _ => hqQ) hs]
  change _ ↔ decide (ordinaryRosserPrefixAdmissible true (rowLevel R bank b N t H) (q::H)) = true
  rw [decide_eq_true_eq]
  exact local_test R bank b hN ht H q hq (fun p h => (htail p h).1) hs hqQ hA

end
end ImbalancedChen.P3OriginalU5WarmRosserAdmission
