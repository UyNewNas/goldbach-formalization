import ImbalancedChen.P1SignedExitCoefficientDifference
import ImbalancedChen.FirstExitValidSelection
import ImbalancedChen.HistoricalPrefixCertificate

/-!
# Boundary-owner support of a historical policy difference

A nonzero fixed modulus difference supplies a selection retained on exactly
one side. Following that actual selection through the common policy locates
its first different test. Every prime in that history is a prime factor of
the original modulus. Local equality of the actual frozen caps away from a
finite joint-owner family therefore confines the modulus difference to a
finite boundary-history carrier, without an average-size assumption.
-/

namespace ImbalancedChen

noncomputable section

/-- Following a one-sided valid selection reaches an actual first
disagreement of the common tree, before continuing on the retained side. -/
private theorem p1_first_disagreement_of_valid_not_valid
    (allowing rejecting : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    {chosen carrier : List ℕ} (hsub : chosen <+ carrier)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (hallow : FirstExitValidSelection allowing pre positive chosen)
    (hreject : ¬FirstExitValidSelection rejecting pre positive chosen) :
    ∃ state ∈ p1SignedExitStates (p1CommonAdmissionPolicy allowing rejecting)
        h pre positive mass carrier,
      allowing state.positive state.selectedPrefix = true ∧
      rejecting state.positive state.selectedPrefix = false ∧
      ∃ later : List ℕ, chosen.reverse ++ pre = later ++ state.selectedPrefix := by
  induction hsub generalizing pre positive mass with
  | slnil => exact False.elim (hreject trivial)
  | cons p hsub ih =>
      obtain ⟨state, hstate, ha, hr, later, heq⟩ := ih pre positive mass hallow hreject
      refine ⟨state, ?_, ha, hr, later, heq⟩
      rw [p1SignedExitStates]
      exact List.mem_append_left _ hstate
  | @cons_cons chosenTail carrierTail p hsub ih =>
      obtain ⟨ha, htail⟩ := hallow
      by_cases hr : rejecting (!positive) (p :: pre) = true
      · have hnotTail : ¬FirstExitValidSelection rejecting (p :: pre) (!positive) chosenTail :=
          fun hv => hreject ⟨hr, hv⟩
        obtain ⟨state, hstate, ha', hr', later, heq⟩ :=
          ih (p :: pre) (!positive) (mass * h p) htail hnotTail
        refine ⟨state, ?_, ha', hr', later, ?_⟩
        · have hc : p1CommonAdmissionPolicy allowing rejecting (!positive) (p :: pre) = true := by
            simp [p1CommonAdmissionPolicy, ha, hr]
          rw [p1SignedExitStates, if_pos hc]
          exact List.mem_append_right _ hstate
        · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq
      · have hrfalse : rejecting (!positive) (p :: pre) = false := by
          cases hb : rejecting (!positive) (p :: pre) <;> simp_all
        let state : FirstExitDepthState ℕ :=
          {selectedPrefix := p :: pre, positive := !positive,
            mass := mass * h p, remaining := carrierTail}
        refine ⟨state, ?_, ha, hrfalse, chosenTail.reverse, ?_⟩
        · have hc : p1CommonAdmissionPolicy allowing rejecting (!positive) (p :: pre) ≠ true := by
            simp [p1CommonAdmissionPolicy, ha, hrfalse]
          rw [p1SignedExitStates, if_neg hc]
          exact List.mem_append_right _ (by simp [state])
        · simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
          rfl

/-- A retained modulus absent on the other side yields a common-tree exit
whose actual ordered history is made entirely of factors of that modulus. -/
private theorem p1_supported_not_supported_first_disagreement
    (allowing rejecting : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (hnodup : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) (d : ℕ)
    (hd : d ∈ firstExitRetainedModuli allowing carrier)
    (hnot : d ∉ firstExitRetainedModuli rejecting carrier) :
    ∃ state ∈ p1SignedExitStates (p1CommonAdmissionPolicy allowing rejecting)
        h [] true 1 carrier,
      allowing state.positive state.selectedPrefix = true ∧
      rejecting state.positive state.selectedPrefix = false ∧
      state.selectedPrefix.reverse <+ carrier ∧
      ∀ p ∈ state.selectedPrefix, p ∈ d.primeFactors := by
  obtain ⟨leaf, hleaf, hprod⟩ := (mem_firstExitRetainedModuli allowing carrier d).mp hd
  obtain ⟨chosen, hsub, hvalid, heq⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves allowing (fun _ => 1)
      [] carrier true 1 leaf hleaf
  have hchosenProd : chosen.prod = d := by
    simpa only [heq, List.append_nil, List.prod_reverse] using hprod
  have hnotValid : ¬FirstExitValidSelection rejecting [] true chosen := by
    intro hv
    exact hnot ((mem_firstExitRetainedModuli_iff_validSelection rejecting carrier d).mpr
      ⟨chosen, hsub, hv, hchosenProd⟩)
  obtain ⟨state, hstate, ha, hr, later, hsuffix⟩ :=
    p1_first_disagreement_of_valid_not_valid allowing rejecting h hsub [] true 1 hvalid hnotValid
  have hleafEq : leaf.selected = later ++ state.selectedPrefix := heq.trans hsuffix
  have hreverse := mem_firstExitRootLeaves_selected_reverse_sublist
    allowing (fun _ => 1) carrier leaf hleaf
  rw [hleafEq, List.reverse_append] at hreverse
  refine ⟨state, hstate, ha, hr,
    (List.sublist_append_left state.selectedPrefix.reverse later.reverse).trans hreverse, ?_⟩
  intro p hp
  rw [← hprod, mem_firstExitRootLeaves_primeFactors_selectedProd allowing (fun _ => 1)
    carrier hnodup hprime leaf hleaf, List.mem_toFinset]
  rw [hleafEq]
  exact List.mem_append_right _ hp

/-- Fixed coefficient disagreement has a witness on the actual common
tree. It is not just an existential cap mismatch on an arbitrary history. -/
theorem p1_coefficientDifference_ne_zero_firstDisagreement
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (hnodup : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) (d : ℕ)
    (hd : p1PolicyCoefficientDifference oldPolicy newPolicy carrier d ≠ 0) :
    ∃ state ∈ p1SignedExitStates (p1CommonAdmissionPolicy oldPolicy newPolicy)
        h [] true 1 carrier,
      oldPolicy state.positive state.selectedPrefix ≠ newPolicy state.positive state.selectedPrefix ∧
      state.selectedPrefix.reverse <+ carrier ∧
      ∀ p ∈ state.selectedPrefix, p ∈ d.primeFactors := by
  have hs := p1_policyCoefficientDifference_ne_zero_mem_symmDifference
    oldPolicy newPolicy carrier d hd
  rcases Finset.mem_union.mp hs with hnew | hold
  · obtain ⟨hnew, hold⟩ := Finset.mem_sdiff.mp hnew
    obtain ⟨state, hstate, hn, ho, hsub, hfactor⟩ :=
      p1_supported_not_supported_first_disagreement newPolicy oldPolicy h carrier hnodup hprime d
        hnew hold
    have hc : p1CommonAdmissionPolicy newPolicy oldPolicy =
        p1CommonAdmissionPolicy oldPolicy newPolicy := by
      funext positive pre
      exact Bool.and_comm _ _
    rw [hc] at hstate
    refine ⟨state, hstate, ?_, hsub, hfactor⟩
    rw [ho, hn]
    decide
  · obtain ⟨hold, hnew⟩ := Finset.mem_sdiff.mp hold
    obtain ⟨state, hstate, ho, hn, hsub, hfactor⟩ :=
      p1_supported_not_supported_first_disagreement oldPolicy newPolicy h carrier hnodup hprime d
        hold hnew
    refine ⟨state, hstate, ?_, hsub, hfactor⟩
    rw [ho, hn]
    decide

/-- Finite actual processing-order histories whose entries are all prime
factors of `d`; reversal is the literal tree storage convention. -/
def p1PrimeFactorHistoryCarrier (carrier : List ℕ) (d : ℕ) : Finset (List ℕ) := by
  classical
  exact ((carrier.sublists.map List.reverse).toFinset).filter
    (fun history => ∀ p ∈ history, p ∈ d.primeFactors)

theorem p1_mem_primeFactorHistoryCarrier
    (carrier history : List ℕ) (d : ℕ) (hsub : history.reverse <+ carrier)
    (hfactor : ∀ p ∈ history, p ∈ d.primeFactors) :
    history ∈ p1PrimeFactorHistoryCarrier carrier d := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨List.mem_toFinset.mpr ?_, hfactor⟩
  exact List.mem_map.mpr ⟨history.reverse, List.mem_sublists.mpr hsub, by simp⟩

/-- Local test agreement outside `bad` puts every nonzero modulus
difference on a real first-disagreement history in the finite factor carrier. -/
theorem p1_coefficientDifference_boundary_history_support
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (bad : List ℕ → Prop)
    (hsame : ∀ positive history, ¬bad history →
      oldPolicy positive history = newPolicy positive history)
    (h : ℕ → ℝ) (carrier : List ℕ) (hnodup : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) (d : ℕ)
    (hd : p1PolicyCoefficientDifference oldPolicy newPolicy carrier d ≠ 0) :
    ∃ state ∈ p1SignedExitStates (p1CommonAdmissionPolicy oldPolicy newPolicy)
        h [] true 1 carrier,
      oldPolicy state.positive state.selectedPrefix ≠ newPolicy state.positive state.selectedPrefix ∧
      bad state.selectedPrefix ∧ state.selectedPrefix ∈ p1PrimeFactorHistoryCarrier carrier d := by
  classical
  obtain ⟨state, hstate, hneq, hsub, hfactor⟩ :=
    p1_coefficientDifference_ne_zero_firstDisagreement oldPolicy newPolicy h carrier hnodup hprime d hd
  refine ⟨state, hstate, hneq, ?_,
    p1_mem_primeFactorHistoryCarrier carrier state.selectedPrefix d hsub hfactor⟩
  by_contra hgood
  exact hneq (hsame state.positive state.selectedPrefix hgood)

/-- If a modulus has no bad owner among its actual factor histories, its
two literal fixed Möbius coefficients agree. No mean bound is assumed. -/
theorem p1_same_fixed_coefficient_of_no_bad_factor_history
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (bad : List ℕ → Prop)
    (hsame : ∀ positive history, ¬bad history →
      oldPolicy positive history = newPolicy positive history)
    (carrier : List ℕ) (hnodup : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) (d : ℕ)
    (hgood : ∀ history ∈ p1PrimeFactorHistoryCarrier carrier d, ¬bad history) :
    firstExitRetainedCoefficient newPolicy carrier d =
      firstExitRetainedCoefficient oldPolicy carrier d := by
  classical
  apply sub_eq_zero.mp
  change p1PolicyCoefficientDifference oldPolicy newPolicy carrier d = 0
  by_contra hnonzero
  obtain ⟨state, _hstate, _hneq, hbad, hfactor⟩ :=
    p1_coefficientDifference_boundary_history_support oldPolicy newPolicy bad hsame
      (fun _ => 1) carrier hnodup hprime d hnonzero
  exact hgood state.selectedPrefix hfactor hbad

/-- The joint owner keeps both literal rank-four and rank-five ancestors. -/
def p1HistoricalJointOwner (history : List ℕ) : List ℕ × List ℕ :=
  (rosserAncestor 4 history, rosserAncestor 5 history)

/-- Equality of actual frozen levels away from the boundary joint owners
implies equality of the actual historical policy tests there. -/
theorem p1_historical_policy_eq_off_boundary_owners
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (B : Finset (List ℕ × List ℕ))
    (hcap : ∀ history, p1HistoricalJointOwner history ∉ B →
      Q4 (rosserAncestor 4 history) = Q5 (rosserAncestor 5 history))
    (positive : Bool) (history : List ℕ) (hgood : p1HistoricalJointOwner history ∉ B) :
    fourthCappedUpperPolicy base Q3 Q4 positive history =
      fifthCappedUpperPolicy base Q3 Q5 positive history := by
  by_cases hlen : history.length ≤ 4
  · exact p1_historical_fourth_fifth_agree_through_four base Q3 Q4 Q5 positive history hlen
  · simp only [fourthCappedUpperPolicy, fifthCappedUpperPolicy, firstExitDepthSplicePolicy,
      if_neg hlen, frozenParityRosserPolicy, ancestorFrozenPolicy]
    rw [hcap history hgood]

/-- The same local-to-policy dictionary for changing only the historical
fourth cap, with the T3 parent fixed. -/
theorem p1_fourth_caps_local_agreement
    (base : Bool → List ℕ → Bool) (Q3 Q4old Q4new : List ℕ → ℝ)
    (B : Finset (List ℕ × List ℕ))
    (hcap : ∀ history, p1HistoricalJointOwner history ∉ B →
      Q4old (rosserAncestor 4 history) = Q4new (rosserAncestor 4 history))
    (positive : Bool) (history : List ℕ) (hgood : p1HistoricalJointOwner history ∉ B) :
    fourthCappedUpperPolicy base Q3 Q4old positive history =
      fourthCappedUpperPolicy base Q3 Q4new positive history := by
  by_cases hlen : history.length ≤ 4
  · simp [fourthCappedUpperPolicy, firstExitDepthSplicePolicy, hlen]
  · simp only [fourthCappedUpperPolicy, firstExitDepthSplicePolicy, if_neg hlen,
      frozenParityRosserPolicy, ancestorFrozenPolicy]
    rw [hcap history hgood]

/-- The corresponding dictionary for a fifth cap change; its own test
and every later use read the actual rank-five ancestor. -/
theorem p1_fifth_caps_local_agreement
    (base : Bool → List ℕ → Bool) (Q3 Q5old Q5new : List ℕ → ℝ)
    (B : Finset (List ℕ × List ℕ))
    (hcap : ∀ history, p1HistoricalJointOwner history ∉ B →
      Q5old (rosserAncestor 5 history) = Q5new (rosserAncestor 5 history))
    (positive : Bool) (history : List ℕ) (hgood : p1HistoricalJointOwner history ∉ B) :
    fifthCappedUpperPolicy base Q3 Q5old positive history =
      fifthCappedUpperPolicy base Q3 Q5new positive history := by
  by_cases hlen : history.length ≤ 4
  · simp [fifthCappedUpperPolicy, firstExitDepthSplicePolicy, hlen]
  · simp only [fifthCappedUpperPolicy, firstExitDepthSplicePolicy, if_neg hlen,
      frozenParityRosserPolicy, ancestorFrozenPolicy]
    rw [hcap history hgood]

/-- Any actual fourth/fifth disagreement occurs after rank four, so its
joint owner consists of full four- and five-entry ancestors. -/
theorem p1_historical_disagreement_joint_owner_lengths
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (positive : Bool) (history : List ℕ)
    (hneq : fourthCappedUpperPolicy base Q3 Q4 positive history ≠
      fifthCappedUpperPolicy base Q3 Q5 positive history) :
    (p1HistoricalJointOwner history).1.length = 4 ∧
      (p1HistoricalJointOwner history).2.length = 5 := by
  have hlen : 4 < history.length := by
    by_contra hnot
    exact hneq (p1_historical_fourth_fifth_agree_through_four
      base Q3 Q4 Q5 positive history (by omega))
  have h4 : 4 ≤ history.length := by omega
  have h5 : 5 ≤ history.length := by omega
  simp [p1HistoricalJointOwner, rosserAncestor_length,
    Nat.min_eq_left h4, Nat.min_eq_left h5]

/-- Actual historical boundary support: a nonzero fixed coefficient
requires an actual common-tree first disagreement owned by `B`, and every
prime in that literal history is a factor of this very modulus. -/
theorem p1_actualHistorical_boundary_difference_witness
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (B : Finset (List ℕ × List ℕ))
    (hcap : ∀ history, p1HistoricalJointOwner history ∉ B →
      Q4 (rosserAncestor 4 history) = Q5 (rosserAncestor 5 history))
    (N cap : ℕ) (z : ℝ) (h : ℕ → ℝ) (d : ℕ)
    (hd : p1HistoricalFourthFifthCoefficientDifference base Q3 Q4 Q5 N cap z d ≠ 0) :
    ∃ state ∈ p1SignedExitStates
        (p1CommonAdmissionPolicy (fourthCappedUpperPolicy base Q3 Q4)
          (fifthCappedUpperPolicy base Q3 Q5)) h [] true 1 (roughPrimeUniverse N cap 0 z),
      fourthCappedUpperPolicy base Q3 Q4 state.positive state.selectedPrefix ≠
        fifthCappedUpperPolicy base Q3 Q5 state.positive state.selectedPrefix ∧
      p1HistoricalJointOwner state.selectedPrefix ∈ B ∧
      state.selectedPrefix ∈ p1PrimeFactorHistoryCarrier (roughPrimeUniverse N cap 0 z) d := by
  apply p1_coefficientDifference_boundary_history_support
    (fourthCappedUpperPolicy base Q3 Q4) (fifthCappedUpperPolicy base Q3 Q5)
    (fun history => p1HistoricalJointOwner history ∈ B) _ h _
    (roughPrimeUniverse_nodup N cap 0 z) (fun _ hp => mem_roughPrimeUniverse_prime hp) d hd
  intro positive history hgood
  exact p1_historical_policy_eq_off_boundary_owners base Q3 Q4 Q5 B hcap positive history hgood

/-- A finite union-modulus subset charged only when one of its actual
prime-factor histories belongs to the boundary joint-owner family. -/
def p1HistoricalBoundaryModuli
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) (B : Finset (List ℕ × List ℕ)) : Finset ℕ := by
  classical
  exact (p1HistoricalFourthFifthUnionModuli base Q3 Q4 Q5 N cap z).filter
    (fun d => ∃ history ∈ p1PrimeFactorHistoryCarrier (roughPrimeUniverse N cap 0 z) d,
      p1HistoricalJointOwner history ∈ B)

theorem p1_actualHistorical_difference_mem_boundaryModuli
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (B : Finset (List ℕ × List ℕ))
    (hcap : ∀ history, p1HistoricalJointOwner history ∉ B →
      Q4 (rosserAncestor 4 history) = Q5 (rosserAncestor 5 history))
    (N cap : ℕ) (z : ℝ) (d : ℕ)
    (hd : p1HistoricalFourthFifthCoefficientDifference base Q3 Q4 Q5 N cap z d ≠ 0) :
    d ∈ p1HistoricalBoundaryModuli base Q3 Q4 Q5 N cap z B := by
  classical
  apply Finset.mem_filter.mpr
  constructor
  · by_contra hnot
    exact hd (p1_policyCoefficientDifference_zero_outside_union _ _ _ d hnot)
  · obtain ⟨state, _hstate, _hneq, hbad, hfactor⟩ :=
      p1_actualHistorical_boundary_difference_witness base Q3 Q4 Q5 B hcap N cap z (fun _ => 1) d hd
    exact ⟨state.selectedPrefix, hfactor, hbad⟩

/-- Literal selected mesh-owner family, evaluated on the actual frozen
rank-r ancestor, with the original half-open logarithmic cell convention. -/
def p1BadSelectedOwner (r : ℕ) (N : ℝ) (a b : ℚ) (m : ℕ)
    (B : Finset (Fin r → Fin (m + 1))) (history : List ℕ) : Prop :=
  ∃ j ∈ B, primeHistoryLogCoordinates N r (rosserAncestor r history) ∈
    logPrimeMeshCell (a : ℝ) (b : ℝ) m j

/-- Actual changed historical cap support in selected mesh owners. Rank
four is the fourth policy and rank five is the fifth policy, by their
existing definitions. The third-capped parent and all its tests are fixed.
The witness belongs to the actual common tree on the target-deleted carrier. -/
theorem p1_actualHistorical_changedCap_selectedOwner_witness
    (r : ℕ) (base : Bool → List ℕ → Bool) (Q3 Qold Qnew : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) (a b : ℚ) (m : ℕ)
    (B : Finset (Fin r → Fin (m + 1)))
    (hcap : ∀ history, ¬p1BadSelectedOwner r (N : ℝ) a b m B history →
      Qold (rosserAncestor r history) = Qnew (rosserAncestor r history))
    (h : ℕ → ℝ) (d : ℕ)
    (hd : p1PolicyCoefficientDifference
      (firstExitDepthSplicePolicy 4 (thirdCappedUpperPolicy base Q3)
        (frozenParityRosserPolicy false r Qold))
      (firstExitDepthSplicePolicy 4 (thirdCappedUpperPolicy base Q3)
        (frozenParityRosserPolicy false r Qnew)) (roughPrimeUniverse N cap 0 z) d ≠ 0) :
    ∃ state ∈ p1SignedExitStates
      (p1CommonAdmissionPolicy
        (firstExitDepthSplicePolicy 4 (thirdCappedUpperPolicy base Q3)
          (frozenParityRosserPolicy false r Qold))
        (firstExitDepthSplicePolicy 4 (thirdCappedUpperPolicy base Q3)
          (frozenParityRosserPolicy false r Qnew)))
      h [] true 1 (roughPrimeUniverse N cap 0 z),
      (firstExitDepthSplicePolicy 4 (thirdCappedUpperPolicy base Q3)
          (frozenParityRosserPolicy false r Qold)) state.positive state.selectedPrefix ≠
        (firstExitDepthSplicePolicy 4 (thirdCappedUpperPolicy base Q3)
          (frozenParityRosserPolicy false r Qnew)) state.positive state.selectedPrefix ∧
      (∃ j ∈ B, primeHistoryLogCoordinates (N : ℝ) r
        (rosserAncestor r state.selectedPrefix) ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) ∧
      state.selectedPrefix ∈ p1PrimeFactorHistoryCarrier (roughPrimeUniverse N cap 0 z) d := by
  apply p1_coefficientDifference_boundary_history_support _ _
    (p1BadSelectedOwner r (N : ℝ) a b m B) _ h _
    (roughPrimeUniverse_nodup N cap 0 z) (fun _ hp => mem_roughPrimeUniverse_prime hp) d hd
  intro positive history hgood
  by_cases hlen : history.length ≤ 4
  · simp [firstExitDepthSplicePolicy, hlen]
  · simp only [firstExitDepthSplicePolicy, if_neg hlen,
      frozenParityRosserPolicy, ancestorFrozenPolicy]
    rw [hcap history hgood]

end

end ImbalancedChen
