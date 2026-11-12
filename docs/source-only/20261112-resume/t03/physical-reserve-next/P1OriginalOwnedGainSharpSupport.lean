import ImbalancedChen.P4AOriginalFull87Fixed599Charges
import ImbalancedChen.P4AOriginalFull87OwnedPrimitiveLedger
import ImbalancedChen.P4AOriginalFull87SignedSharpReceiver

/-! Scope of the original signed sixth-to-eighth gain at the complete
small-times-rough modulus. Both sides use the same owned eighth state
and their own actual terminal list. -/
namespace ImbalancedChen.P1OriginalOwnedGainSharpSupport
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope (mu)
open P1Pair12RetainedSignedSource (signedTest_eq_leaves attachedLeafTest)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalCompleteSixthChronology (data)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap selectedCap_append)
open P4AOriginalFull87LicensedSixthRealization (states FilteredSourceSupply)
open P4AOriginalFull87OwnedEighthSource
  (ownedSource ordinarySaving frontier frontier_length states_eq_owner_filter
   retainedOwner selectedCap_eq_map_owner)
open P4AOriginalFull87OwnedPrimitiveLedger (beforeLeaves afterLeaves)
open P4AOriginalFull87InheritedTerminalLevel
  (inherited_ordinary_leaf_admissible retained_leaves_congr_nonempty)
open P4AOriginalFull87LicensedSixthPolicy (policy eighthContinuation frontier_eq_new_sixth)
open P4AOriginalFull87EighthPrimeMeanLedger (gain gain_eq_owned_sources)
open P4AOriginalFull87SignedSharpReceiver (full87PhysicalRhoChange full87PhysicalSupport
  full87_physical_signed_normal_form)

private theorem both_leaf_bounds (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (H : FilteredSourceSupply s r n e q om)
    (he : 0≤((data e q om).e:ℝ)) (hN : 1<(N:ℝ)) (hw : w≤(N:ℝ)^(53/13824:ℝ))
    (hz : (N:ℝ)^mu≤z) (hc : z≤cap) (c : Cell) (u : FirstExitDepthState ℕ)
    (hu : u∈states (width r) n e q om N cap w z (fun _ => 1) c)
    (l : FirstExitLeaf ℕ) (hl : l∈beforeLeaves n e q om N u ∨ l∈afterLeaves n e q om N c u) :
    (l.selected.prod:ℝ)<(N:ℝ)^(299/500:ℝ) := by
  rw [states_eq_owner_filter] at hu
  obtain ⟨hu,ho⟩ := List.mem_filter.mp hu
  have ho' : retainedOwner (width r) (N:ℝ) u.selectedPrefix=some c := of_decide_eq_true ho
  have hlen := frontier_length n e q om N cap w z u hu
  have hf : u∈firstExitDepthFrontier 8 (policy (width r) n e q om (N:ℝ)) (fun _ => 1)
      [] true 1 (roughPrimeUniverse N cap w z) := by
    rw [frontier_eq_new_sixth]
    exact hu
  rcases hl with hbefore|hafter
  · have hadm := inherited_ordinary_leaf_admissible (width r) n e q om N cap w z
      (fun _ => 1) u hf l hbefore
    exact hadm.1.trans_le (P4AOriginalFull87WholeSixthCeiling.level6_power_le_initial_ceiling
      n e q om (N:ℝ) he hN.le (rosserAncestor 6 u.selectedPrefix))
  · let p := policy (width r) n e q om (N:ℝ)
    let D := (N:ℝ)^(finiteCap n c (point8 (N:ℝ) u.selectedPrefix):ℝ)
    have hsel : selectedCap (width r) n (N:ℝ) u.selectedPrefix=
        some (finiteCap n c (point8 (N:ℝ) u.selectedPrefix)) := by
      rw [selectedCap_eq_map_owner,ho']
      rfl
    have hread (later : List ℕ) (hne : later≠[]) (b : Bool) :
        p b (later++u.selectedPrefix)=ordinaryParityRosserPolicy false D b (later++u.selectedPrefix) := by
      have hpos : 0<later.length := by cases later with
        | nil => exact (hne rfl).elim
        | cons x xs => simp
      have hl : ¬(later++u.selectedPrefix).length≤8 := by rw [List.length_append,hlen]; omega
      simp only [p,policy,firstExitDepthSplicePolicy,if_neg hl,eighthContinuation,
        selectedCap_append (width r) n (N:ℝ) later u.selectedPrefix hlen.ge,hsel,D]
    have hL := retained_leaves_congr_nonempty p (ordinaryParityRosserPolicy false D)
      (fun _ => 1) u.selectedPrefix u.remaining u.positive u.mass hread
    apply P4AOriginalFull87AllEighthFrontierTerminal.actual_all_eighth_frontier_terminal_product_lt_fixed_power
      s r n e q om N cap w z (fun _ => 1) H he hN hw hz hc u hf l
    rw [hL]
    exact hafter

private theorem zero_list {α : Type*} (l : List α) (f : α→ℝ) (h : ∀x∈l,f x=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons,h x (by simp),
        ih (fun y hy => h y (List.mem_cons_of_mem x hy)),zero_add]

/-- Termwise in actual occurrences before summing either sign. At an active
small coefficient the modulus is strictly below the stated real power. -/
theorem gain_zero_on_upper_test (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z ell : ℝ) (H : FilteredSourceSupply s r n e q om)
    (he : 0≤((data e q om).e:ℝ)) (hN : 1<(N:ℝ)) (hw : w≤(N:ℝ)^(53/13824:ℝ))
    (hz : (N:ℝ)^mu≤z) (hc : z≤cap) (hell : ell≤1/1000)
    (T : ℕ→ℝ) (hT : ∀d : ℕ,(d:ℝ)<(N:ℝ)^(599/1000:ℝ) → T d=0) :
    gain (width r) n e q om N cap w z ((N:ℝ)^ell) T=0 := by
  rw [gain_eq_owned_sources]
  apply Finset.sum_eq_zero
  intro c _
  unfold ownedSource
  apply zero_list
  intro u hu
  let f (l : FirstExitLeaf ℕ) := l.value*attachedLeafTest N cap 1 w ((N:ℝ)^ell) T l.positive l.selected
  have hz' (l : FirstExitLeaf ℕ)
      (hl : l∈beforeLeaves n e q om N u ∨ l∈afterLeaves n e q om N c u) : f l=0 := by
    suffices ha : attachedLeafTest N cap 1 w ((N:ℝ)^ell) T l.positive l.selected=0 by simp [f,ha]
    unfold attachedLeafTest
    apply Finset.sum_eq_zero
    intro a _
    by_cases hb : (if l.positive then actualSmallRosserPlus N cap w ((N:ℝ)^ell) a
      else actualSmallRosserMinus N cap w ((N:ℝ)^ell) a)=0
    · simp only [one_mul,hb,zero_mul,mul_zero]
    · have hrough := both_leaf_bounds s r n e q om N cap w z H he hN hw hz hc c u hu l hl
      have hmod := P4AOriginalFull87Fixed599Charges.actual_live_product_lt_599
        N cap w ell hN hell l.positive a l.selected.prod hb hrough
      simp only [one_mul,hT _ hmod,mul_zero]
  simp only [ordinarySaving,signedTest_eq_leaves]
  change ((beforeLeaves n e q om N u).map f).sum-((afterLeaves n e q om N c u).map f).sum=0
  rw [zero_list _ f (fun l hl => hz' l (Or.inl hl)),zero_list _ f (fun l hl => hz' l (Or.inr hl)),sub_self]

/-- The actual old-sixth-minus-eighth coefficient at the exact integer
endpoint. All unaffected pieces have cancelled in the original gain ledger. -/
theorem same_coefficient_above (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z ell : ℝ) (H : FilteredSourceSupply s r n e q om)
    (he : 0≤((data e q om).e:ℝ)) (hN : 1<(N:ℝ)) (hw : w≤(N:ℝ)^(53/13824:ℝ))
    (hz : (N:ℝ)^mu≤z) (hc : z≤cap) (hell : ell≤1/1000)
    (d : ℕ) (hd : (N:ℝ)^(599/1000:ℝ)≤(d:ℝ)) :
    full87PhysicalRhoChange r n e q om N cap w z ((N:ℝ)^ell) d=0 := by
  let S := full87PhysicalSupport r n e q om N cap w z
  by_cases hmem : d∈S
  · let T (j : ℕ) : ℝ := if j=d then 1 else 0
    have h := gain_zero_on_upper_test s r n e q om N cap w z ell H he hN hw hz hc hell T
      (fun j hj => if_neg (fun h => by subst j; exact (not_lt.mpr hd) hj))
    rw [full87_physical_signed_normal_form] at h
    change d∈full87PhysicalSupport r n e q om N cap w z at hmem
    simpa [T,mul_ite,hmem] using h
  · have h6 : d∉actualSmallRoughModuli
        ((P4AOriginalFull87LicensedSixthPolicy.sixthPolicy n e q om (N:ℝ)) false) N cap w z :=
      fun h => hmem (Finset.mem_union_left _ h)
    have h8 : d∉actualSmallRoughModuli ((policy (width r) n e q om (N:ℝ)) false) N cap w z :=
      fun h => hmem (Finset.mem_union_right _ h)
    simp only [full87PhysicalRhoChange,if_neg h6,if_neg h8,sub_self]

end
end ImbalancedChen.P1OriginalOwnedGainSharpSupport
