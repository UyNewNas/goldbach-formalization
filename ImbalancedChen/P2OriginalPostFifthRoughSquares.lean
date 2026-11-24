import ImbalancedChen.P2OriginalPairRootRoughProducer
import ImbalancedChen.P2OriginalSelectedNativeSmallExtension

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

After full rank five, the actual CapPlan never changes the frozen cap.
An accepted continuation supplies every even-rank cube. At the next odd
rank the previous cube and decreasing order supply its square; there is
no invented odd cube test. Thus actual accepted rough descendants produce
both full and selected-complement gates, not an hRoughWell premise.
-/
namespace ImbalancedChen.P2OriginalPostFifthRoughSquares
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2LowerIntegerRetainedSupport P2EnhancedLowerPhysicalNode
open P2OriginalSelectedIntegerPrefixSquares P2OriginalSelectedNativeSmallExtension
open P2OriginalLowerWholeBoxBranchSelect P2OriginalLowerCompactStartCapConstructor

private theorem step_cap_after_five {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (H : Trace) (hlen : 5 ≤ H.word.length) (x : ℝ) :
    (step P a b H x).cap = H.cap := by
  apply no_new_cap_outside_345
  simp only [List.length_append, List.length_singleton]
  omega

theorem run_cap_after_five {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (H : Trace) (hlen : 5 ≤ H.word.length) (xs : List ℝ) :
    (run P a b H xs).cap = H.cap := by
  induction xs generalizing H with
  | nil => rfl
  | cons x xs ih =>
      have hlen' : 5 ≤ (step P a b H x).word.length := by
        simp only [step, List.length_append, List.length_singleton]
        omega
      calc
        (run P a b H (x::xs)).cap =
            (run P a b (step P a b H x) xs).cap := rfl
        _ = (step P a b H x).cap := ih _ hlen'
        _ = H.cap := step_cap_after_five P a b H hlen x

/-- An actual raw pair-policy atom provides its computed full-rank-five
    state and its accepted remaining rough continuation. Short atoms are
    left in their separate original finite-rank lane. -/
theorem pair_atom_fifth_split {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b seedCap : ℝ) (N enum : ℕ) (p : ℕ × ℕ) (z0 z : ℝ) {r : ℕ}
    (hr : r ∈ fixedEvenRoughSupport
      (P2OriginalPairRootRoughProducer.pairPolicy P a b seedCap N p) N enum z0 z) :
    ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N enum z0 z ∧ chosen.prod = r ∧
      let H5 := run P a b (P2OriginalPairRootRoughProducer.pairRoot N p seedCap)
        ((chosen.take 3).map (coordinate N))
      3 ≤ chosen.length → H5.word.length = 5 ∧
        (run P a b H5 ((chosen.drop 3).map (coordinate N))).accepted = true ∧
        (run P a b H5 ((chosen.drop 3).map (coordinate N))).cap = H5.cap := by
  obtain ⟨chosen, hsub, haccept, hprod⟩ :=
    (P2OriginalPairRootRoughProducer.pair_policy_support_iff
      P a b seedCap N enum p z0 z r).mp hr
  refine ⟨chosen, hsub, hprod, ?_⟩
  intro hlong
  let H5 := run P a b (P2OriginalPairRootRoughProducer.pairRoot N p seedCap)
    ((chosen.take 3).map (coordinate N))
  have hlen : H5.word.length = 5 := by
    rw [run_word]
    simp [P2OriginalPairRootRoughProducer.pairRoot, List.length_take,
      Nat.min_eq_left hlong]
  have hsplit : chosen.map (coordinate N) =
      (chosen.take 3).map (coordinate N) ++ (chosen.drop 3).map (coordinate N) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hsplit, run_append] at haccept
  exact ⟨hlen, haccept, run_cap_after_five P a b H5 (by omega)
    ((chosen.drop 3).map (coordinate N))⟩

/-- The even-length state carries its actual preceding cube. This is
    precisely the reserve needed at the odd bypass, not a new test. -/
private theorem accepted_suffix_squares {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (xs : List ℝ) :
    ∀ (H : Trace) (ceiling : ℝ), 5 ≤ H.word.length →
      (H.word.length % 2 = 0 → H.word.sum + 2*ceiling < H.cap) →
      (H.word.length % 2 = 0 → ∀ x ∈ xs, x ≤ ceiling) →
      xs.Pairwise (· ≥ ·) → (∀ x ∈ xs, 0 ≤ x) →
      (run P a b H xs).accepted = true →
      SquareGates H.cap H.word.sum xs := by
  induction xs with
  | nil => intros; trivial
  | cons x xs ih =>
      intro H ceiling hlen hcarry hceil hsort hnonneg haccept
      have htailacc : (run P a b (step P a b H x) xs).accepted = true :=
        haccept
      have hstepacc := run_accepted_incoming P a b _ _ htailacc
      have hadm := ((step_accepted_iff P a b H x).mp hstepacc).2
      have hcap := step_cap_after_five P a b H hlen x
      have hx0 := hnonneg x (List.mem_cons_self x xs)
      have hcube (heven : (H.word.length+1)%2 = 0) :
          H.word.sum + 3*x < H.cap := by
        have hne : H.word.length ≠ 0 := by omega
        simpa only [admission, if_neg hne, if_pos heven] using hadm
      have hsquare : H.word.sum + 2*x ≤ H.cap := by
        by_cases heven : (H.word.length+1)%2 = 0
        · linarith [hcube heven]
        · have hprevEven : H.word.length%2 = 0 := by omega
          have hc := hcarry hprevEven
          have hx := hceil hprevEven x (List.mem_cons_self x xs)
          linarith
      have hlen' : 5 ≤ (step P a b H x).word.length := by
        simp only [step, List.length_append, List.length_singleton]
        omega
      have hcarry' : (step P a b H x).word.length%2 = 0 →
          (step P a b H x).word.sum + 2*x < (step P a b H x).cap := by
        intro heven
        have he : (H.word.length+1)%2 = 0 := by
          simpa only [step, List.length_append, List.length_singleton] using heven
        have hc := hcube he
        rw [hcap]
        simpa only [step, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
          using (show H.word.sum + x + 2*x < H.cap by linarith)
      have hsortTail := (List.pairwise_cons.mp hsort).2
      have hceil' : (step P a b H x).word.length%2 = 0 →
          ∀ y ∈ xs, y ≤ x := by
        intro _ y hy
        exact (List.pairwise_cons.mp hsort).1 y hy
      have htail := ih (step P a b H x) x hlen' hcarry' hceil' hsortTail
        (fun y hy => hnonneg y (List.mem_cons_of_mem x hy)) htailacc
      rw [hcap] at htail
      have htail' : SquareGates H.cap (H.word.sum+x) xs := by
        simpa only [step, List.sum_append, List.sum_cons, List.sum_nil, add_zero] using htail
      exact ⟨hsquare, htail'⟩

/-- Full rank five is odd. Its first continuation is actually tested
    at even rank six; the auxiliary preceding-cube invariant is vacuous. -/
theorem actual_postfive_suffix_squares {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (H : Trace) (hlen : H.word.length = 5) (xs : List ℝ)
    (hsort : xs.Pairwise (· ≥ ·)) (hnonneg : ∀ x ∈ xs, 0 ≤ x)
    (haccept : (run P a b H xs).accepted = true) :
    SquareGates H.cap H.word.sum xs := by
  apply accepted_suffix_squares P a b xs H 0 (by omega)
  · intro heven; omega
  · intro heven; omega
  · exact hsort
  · exact hnonneg
  · exact haccept

/-- Same original tags, same frozen cap, and both descendant gate lists
    are consequences of the ACTUAL run's acceptance and decreasing order. -/
theorem actual_postfive_tagged_squares {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (H : Trace) (hlen : H.word.length = 5)
    (slots : List Slot) (hword : slots.map Slot.exponent = H.word)
    (hfull : SquareGates H.cap 0 (slots.map Slot.exponent))
    (hselected : SquareGates H.cap (selectedWord slots).sum (remainingWord slots))
    (xs : List ℝ) (hsort : xs.Pairwise (· ≥ ·)) (hnonneg : ∀ x ∈ xs, 0 ≤ x)
    (haccept : (run P a b H xs).accepted = true) :
    let extended := slots ++ xs.map unselected
    SquareGates H.cap 0 (extended.map Slot.exponent) ∧
      SquareGates H.cap (selectedWord extended).sum (remainingWord extended) ∧
      selectedWord extended = selectedWord slots := by
  have hsuffix := actual_postfive_suffix_squares P a b H hlen xs hsort hnonneg haccept
  have hselTail : (selectedWord (xs.map unselected)) = [] := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [selectedWord, unselected] using ih
  have hremTail : remainingWord (xs.map unselected) = xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [remainingWord, unselected] using congrArg (List.cons x) ih
  have hvalues : (xs.map unselected).map Slot.exponent = xs := by
    simp [unselected, List.map_map, Function.comp_def]
  have hsum : (selectedWord slots).sum + (remainingWord slots).sum = H.word.sum := by
    rw [selected_remaining_sum, hword]
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.map_append, hvalues]
    rw [squareGates_append_iff]
    exact ⟨hfull, by simpa only [hword, zero_add] using hsuffix⟩
  · rw [selectedWord_append, remainingWord_append, hselTail, hremTail,
      List.append_nil, squareGates_append_iff]
    exact ⟨hselected, by simpa only [hsum] using hsuffix⟩
  · rw [selectedWord_append, hselTail, List.append_nil]

private theorem coordinate_nonneg {N p : ℕ} (hN : 1 < (N : ℝ)) (hp : 1 ≤ p) :
    0 ≤ coordinate N p := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp)) (Real.log_pos hN).le

private theorem coordinate_mono {N p q : ℕ} (hN : 1 < (N : ℝ))
    (hp : 0 < p) (hpq : p ≤ q) : coordinate N p ≤ coordinate N q := by
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (Nat.cast_pos.mpr hp) (by exact_mod_cast hpq))
    (Real.log_pos hN).le

/-- Integer rough descendants now have their full/selected gates produced
    by their accepted actual chronological trace, rather than assumed. -/
theorem actual_postfive_integer_gates {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) {N : ℕ} (hN : 1 < (N : ℝ))
    (H : Trace) (hlen : H.word.length = 5) (slots : List (ℕ × Bool))
    (hword : (logSlots N slots).map Slot.exponent = H.word)
    (hpos : ∀ v ∈ slots, 0 < v.1)
    (hfull : SquareGates H.cap 0 ((logSlots N slots).map Slot.exponent))
    (hselected : SquareGates H.cap (selectedWord (logSlots N slots)).sum
      (remainingWord (logSlots N slots)))
    (ds : List ℕ) (hprime : ∀ p ∈ ds, p.Prime) (hsort : ds.Pairwise (· ≥ ·))
    (haccept : (run P a b H (ds.map (coordinate N))).accepted = true) :
    let extended := appendUnselected slots ds
    IntegerSquareGates N H.cap 1 (extended.map Prod.fst) ∧
      IntegerSquareGates N H.cap (selectedPrimes extended).prod (remainingPrimes extended) := by
  have hcoordsSort : (ds.map (coordinate N)).Pairwise (· ≥ ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < ds.length := by simpa only [List.length_map] using hi
    have hj' : j < ds.length := by simpa only [List.length_map] using hj
    have hij' := (List.pairwise_iff_getElem.mp hsort) i j hi' hj' hij
    have hposj := (hprime ds[j] (List.getElem_mem hj')).pos
    simpa only [List.getElem_map] using coordinate_mono hN hposj hij'
  have hcoords0 : ∀ x ∈ ds.map (coordinate N), 0 ≤ x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact coordinate_nonneg hN (hprime p hp).one_lt.le
  have hreal := actual_postfive_tagged_squares P a b H hlen (logSlots N slots)
    hword hfull hselected (ds.map (coordinate N)) hcoordsSort hcoords0 haccept
  have heq : logSlots N (appendUnselected slots ds) =
      logSlots N slots ++ (ds.map (coordinate N)).map unselected := by
    simp [logSlots, appendUnselected, unselected, List.map_map, Function.comp_def]
  have hposExt : ∀ v ∈ appendUnselected slots ds, 0 < v.1 := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hpos v hv
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      exact (hprime p hp).pos
  apply physical_slots_to_integer hN (appendUnselected slots ds) hposExt H.cap
  · rw [heq]; exact hreal.1
  · rw [heq]; exact hreal.2.1

/-- The compiler's SECOND buffer is a genuine exponent reserve. -/
theorem double_buffer_identity (S : CompactStart) {mesh : ℕ} (code : Code mesh)
    (buffer : ℚ) (branch : SelectedBranchData) :
    (bufferedCap S code (2*buffer) branch : ℝ) + (buffer : ℝ) =
      (bufferedCap S code buffer branch : ℝ) := by
  simp only [bufferedCap, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  ring

/-- From actual prefix squares at the contracted cap, the small Rosser
    product budget at the once-buffered physical cap is DERIVED. -/
theorem double_buffer_residual_budget {N : ℕ} (hN : 1 < (N : ℝ))
    (S : CompactStart) {mesh : ℕ} (code : Code mesh)
    (buffer : ℚ) (branch : SelectedBranchData) (word : List ℕ)
    (hprime : ∀ p ∈ word, 1 < p) (hne : word ≠ [])
    (hfull : IntegerSquareGates N
      (bufferedCap S code (2*buffer) branch : ℝ) 1 word)
    {L : ℝ} (hL : L ≤ (N : ℝ)^(buffer : ℝ)) :
    (word.prod : ℝ) * L < (N : ℝ)^(bufferedCap S code buffer branch : ℝ) := by
  have hprod := integerSquareGates_product_lt word (by decide : 0 < (1 : ℕ))
    hprime hne hfull
  simp only [Nat.one_mul] at hprod
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hN
  calc
    (word.prod : ℝ) * L ≤ (word.prod : ℝ) * (N : ℝ)^(buffer : ℝ) :=
      mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg word.prod)
    _ < (N : ℝ)^(bufferedCap S code (2*buffer) branch : ℝ) *
        (N : ℝ)^(buffer : ℝ) :=
      mul_lt_mul_of_pos_right hprod (Real.rpow_pos_of_pos hNpos _)
    _ = (N : ℝ)^(bufferedCap S code buffer branch : ℝ) := by
      rw [← Real.rpow_add hNpos, double_buffer_identity]

end
end ImbalancedChen.P2OriginalPostFifthRoughSquares
