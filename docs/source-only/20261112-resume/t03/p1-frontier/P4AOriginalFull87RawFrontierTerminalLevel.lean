import ImbalancedChen.P4AOriginalFull87InheritedTerminalLevel
import ImbalancedChen.P4AOriginalFull87WholeSixthCeiling
import ImbalancedChen.P4AOriginalFull87UnmatchedPhysicalLeaves
import ImbalancedChen.FirstExitFrontierInvariants

/-! Full rough support for the P1 raw post-eight tree, including raw owners
outside the trim. The rank-eight prefix was admitted at its actual sixth
level. An invalid prefix at a changed eighth level permits no first take. -/
namespace ImbalancedChen.P4AOriginalFull87RawFrontierTerminalLevel
noncomputable section
open scoped Classical BigOperators List
open P4AOriginalFull87RawOwnerPartition (actualRawFrontier)
open P4AOriginalFull87UnmatchedPhysicalLeaves (rawRetainedLeaves)
open P4AOriginalFull87CompleteSixthDispatch (policy policy_outside policy_selected)
open P4AOriginalFull87SourceDispatch
  (ownerAtPrefix ownerAtPrefix_append point8 point8_append selectedExponent selectedExponent_bounds)
open P4AOriginalFull87SourceDictionary (newCap)
open P4AOriginalCompleteSixthChronology (data currentSixthExponent current_policy_after_six)
open P4AOriginalFull87InheritedTerminalLevel
  (retained_leaves_congr_nonempty ordinary_terminal_admissible)

private theorem raw_extension_level (e : ℚ) (q : ℕ) (om N : ℝ)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 ≤ N)
    (pre : List ℕ) (hlen : pre.length = 8) :
    ∃ D : ℝ, D ≤ N^(299/500 : ℝ) ∧ ∀ later : List ℕ, later ≠ [] →
      ∀ b : Bool, policy e q om N b (later ++ pre) =
        ordinaryParityRosserPolicy false D b (later ++ pre) := by
  have h8 : 8 ≤ pre.length := hlen.ge
  have hdeep (later : List ℕ) (hne : later ≠ []) : 8 < (later ++ pre).length := by
    cases later with
    | nil => exact (hne rfl).elim
    | cons p ps => simp only [List.length_append,List.length_cons,hlen]; omega
  cases ho : ownerAtPrefix N pre with
  | none =>
      refine ⟨N^(currentSixthExponent e q om N (rosserAncestor 6 pre)),
        Real.rpow_le_rpow_of_exponent_le hN
          (P4AOriginalFull87WholeSixthCeiling.raw_currentSixth_le_initial_ceiling
            e q om N he _), ?_⟩
      intro later hne b
      have ho' := (ownerAtPrefix_append N later pre h8).trans ho
      have h6 : 6 < (later ++ pre).length := lt_trans (by decide : 6 < 8) (hdeep later hne)
      rw [policy_outside e q om N b _ ho', current_policy_after_six e q om N b _ h6,
        rosserAncestor_append 6 later pre (by omega)]
  | some c =>
      have hcap := selectedExponent_bounds N pre (newCap c (point8 N pre))
        (by simp [selectedExponent,ho])
      refine ⟨N^(newCap c (point8 N pre)),
        Real.rpow_le_rpow_of_exponent_le hN
          (hcap.2.le.trans (by norm_num : (153/256 : ℝ) ≤ 299/500)), ?_⟩
      intro later hne b
      have ho' := (ownerAtPrefix_append N later pre h8).trans ho
      rw [policy_selected e q om N c b _ (hdeep later hne) ho',
        point8_append N later pre h8]

private theorem leaves_of_invalid_even_entry (D : ℝ) (pre : List ℕ)
    (hbad : ¬ordinaryRosserPrefixAdmissible false D pre)
    (weight : ℕ → ℝ) (mass : ℝ) (remaining : List ℕ)
    (hprime : ∀ p ∈ remaining, p.Prime)
    (horder : ∀ p ∈ remaining, (p :: pre).Pairwise (· < ·)) :
    firstExitRetainedLeaves (ordinaryParityRosserPolicy false D)
      weight pre true mass remaining = [⟨pre,true,mass⟩] := by
  induction remaining with
  | nil => rfl
  | cons p ps ih =>
      have hreject : ¬ordinaryParityRosserPolicy false D (!true) (p :: pre) = true := by
        intro hg
        have hadm : ordinaryRosserPrefixAdmissible false D (p :: pre) := by
          simpa only [Bool.not_true,ordinaryParityRosserPolicy,Bool.false_eq_true,if_false,
            oddFirstExitPolicy,Bool.false_or,decide_eq_true_eq] using hg
        exact hbad (ordinaryRosserPrefixAdmissible_tail false D p pre
          (hprime p (by simp)) (horder p (by simp)) hadm)
      rw [firstExitRetainedLeaves,if_neg hreject,List.append_nil]
      exact ih (fun x hx => hprime x (List.mem_cons_of_mem _ hx))
        (fun x hx => horder x (List.mem_cons_of_mem _ hx))

/-- Every actual retained suffix leaf of every original raw frontier occurrence.
There is no trim, winning mask, or comparison between the old and new levels
in the hypotheses. The threshold includes the inherited third/fifth seed. -/
theorem raw_frontier_leaf_product_lt (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ actualRawFrontier e q om N cap w z (fun _ => (1 : ℝ)))
    (leaf : FirstExitLeaf ℕ) (hl : leaf ∈ rawRetainedLeaves e q om N s) :
    (leaf.selected.prod : ℝ) < (N : ℝ)^(299/500 : ℝ) := by
  let R := policy e q om (N : ℝ)
  let carrier := roughPrimeUniverse N cap w z
  have h8 := firstExitDepthFrontier_selected_length 8 R (fun _ => (1 : ℝ))
    [] carrier true 1 (by simp) s hs
  have ht := P4AOriginalFull87CompleteSixthDispatch.actual_eighth_frontier_admissible
    e q om N cap w z (fun _ => (1 : ℝ)) s hs
  have hprefix : (s.selectedPrefix.prod : ℝ) < (N : ℝ)^(299/500 : ℝ) :=
    ht.1.trans_le (Real.rpow_le_rpow_of_exponent_le hN.le
      (P4AOriginalFull87WholeSixthCeiling.raw_currentSixth_le_initial_ceiling
        e q om (N : ℝ) he _))
  obtain ⟨D,hD,hread⟩ := raw_extension_level e q om (N : ℝ) he hN.le s.selectedPrefix h8
  have hleaves := retained_leaves_congr_nonempty R (ordinaryParityRosserPolicy false D)
    (fun _ => (1 : ℝ)) s.selectedPrefix s.remaining s.positive s.mass hread
  change leaf ∈ firstExitRetainedLeaves R (fun _ => (1 : ℝ))
    s.selectedPrefix s.positive s.mass s.remaining at hl
  rw [hleaves] at hl
  have hsign := mem_firstExitDepthFrontier_positive_eq_evenListLength 8 R
    (fun _ => (1 : ℝ)) carrier s hs
  have hsub : s.selectedPrefix.reverse ++ s.remaining <+ carrier := by
    simpa only [List.reverse_nil,List.nil_append] using
      firstExitDepthFrontier_selected_remaining_sublist 8 R (fun _ => (1 : ℝ))
        [] carrier true 1 s hs
  have hord := (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  have hprime (p : ℕ) (hp : p ∈ s.remaining) : p.Prime :=
    mem_roughPrimeUniverse_prime (hsub.subset (List.mem_append_right _ hp))
  by_cases hv : ordinaryRosserPrefixAdmissible false D s.selectedPrefix
  · have hor : (s.remaining.reverse ++ s.selectedPrefix).Pairwise (· < ·) := by
      simpa only [List.reverse_append,List.reverse_reverse,List.pairwise_reverse] using hord
    exact (ordinary_terminal_admissible D (fun _ => (1 : ℝ)) s.selectedPrefix
      s.remaining s.positive s.mass hv hsign hprime hor leaf hl).1.trans_le hD
  · have parity (xs : List ℕ) : evenListLength xs = decide (Even xs.length) := by
      induction xs with
      | nil => simp [evenListLength]
      | cons x xs ih => simp only [evenListLength,ih,List.length_cons,Nat.even_add_one,decide_not]
    have hp : s.positive = true := by rw [hsign,parity,h8] <;> decide
    have hpair := List.pairwise_append.mp hord
    have horder (p : ℕ) (hm : p ∈ s.remaining) : (p :: s.selectedPrefix).Pairwise (· < ·) := by
      exact List.pairwise_cons.mpr ⟨fun x hx => hpair.2.2 x (List.mem_reverse.mpr hx) p hm,
        by simpa only [List.pairwise_reverse] using hpair.1⟩
    rw [hp,leaves_of_invalid_even_entry D _ hv _ _ _ hprime horder,List.mem_singleton] at hl
    subst leaf
    exact hprefix

end
end ImbalancedChen.P4AOriginalFull87RawFrontierTerminalLevel
