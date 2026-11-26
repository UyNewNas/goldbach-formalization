import ImbalancedChen.P1OriginalProducerAttainedRowBinding
import ImbalancedChen.P1OriginalVariableFifthContinuation
import ImbalancedChen.P1CorrectedFifthCausalTupleDictionary
import ImbalancedChen.FirstExitValidSelection

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The fifth winner is constructed from the actual finite maximum. A real
retained rank-at-least-five leaf supplies its own original T3 next tuple;
original firstStop/rawQ3 joint geometry is recovered from that membership.
The inherited fourth exponent remains the pointwise producer maximum on
the same fourth ancestor. No winning row or dominance premise is supplied.
-/

namespace ImbalancedChen.P1OriginalFifthAttainedRowBinding
noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open P1CorrectedFifthCausalTupleDictionary
open P1OriginalProducerAttainedRowBinding

/-- Every initial processing segment keeps the tests it actually passed. -/
theorem validSelection_take {α : Type*} (P : Bool → List α → Bool)
    (pre chosen : List α) (positive : Bool)
    (hvalid : FirstExitValidSelection P pre positive chosen) (k : ℕ) :
    FirstExitValidSelection P pre positive (chosen.take k) := by
  induction k generalizing pre chosen positive with
  | zero => trivial
  | succ k ih =>
    cases chosen with
    | nil => trivial
    | cons p ps =>
      exact ⟨hvalid.1, ih (p :: pre) ps (!positive) hvalid.2⟩

/-- Transfer only those already-passed tests whose histories lie below the
specified rank. This lemma never substitutes a new test at a later rank. -/
theorem validSelection_transfer_bounded {α : Type*}
    (P Q : Bool → List α → Bool) (k : ℕ)
    (hPQ : ∀ positive pre, pre.length ≤ k → P positive pre = Q positive pre)
    (pre chosen : List α) (positive : Bool)
    (hlen : pre.length + chosen.length ≤ k)
    (hvalid : FirstExitValidSelection P pre positive chosen) :
    FirstExitValidSelection Q pre positive chosen := by
  induction chosen generalizing pre positive with
  | nil => trivial
  | cons p ps ih =>
    constructor
    · rw [← hPQ (!positive) (p :: pre) (by simp only [List.length_cons] at *; omega)]
      exact hvalid.1
    · exact ih (p :: pre) (!positive) (by simp only [List.length_cons] at *; omega) hvalid.2

def fifthTuple (pre : List ℕ) : Fin 5 → ℕ :=
  primeHistoryTuple 5 (rosserAncestor 5 pre)

/-- A retained descendant constructs an actual next tuple of the original
rank-four T3 frontier. Its fifth own test is not inserted into enumeration. -/
theorem retained_fifth_ancestor_mem_original_candidates
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (weight : ℕ → ℝ)
    (carrier : List ℕ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy5 e chi m omega N rows4 licensed4 J5 rows5)
      weight [] true 1 carrier) (hlen : 5 ≤ leaf.selected.length) :
    fifthTuple leaf.selected ∈ firstExitFrontierTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega N) carrier := by
  obtain ⟨chosen, hsub, hvalid, hselected⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves
      (policy5 e chi m omega N rows4 licensed4 J5 rows5)
      weight [] carrier true 1 leaf hleaf
  have hc : 5 ≤ chosen.length := by simpa only [hselected, List.length_append,
    List.length_reverse, List.length_nil, Nat.add_zero] using hlen
  have h5 : (rosserAncestor 5 leaf.selected).length = 5 := by
    rw [rosserAncestor_length]
    omega
  have hreverse : (rosserAncestor 5 leaf.selected).reverse = chosen.take 5 := by
    rw [hselected, List.append_nil]
    simp only [rosserAncestor, List.reverse_drop, List.length_reverse,
      List.reverse_reverse]
    congr 1
    omega
  have hofn : List.ofFn (fifthTuple leaf.selected) = chosen.take 5 := by
    exact (primeHistoryTuple_ofFn h5).trans hreverse
  have htake5 : (chosen.take 5).length = 5 := by
    rw [List.length_take]
    omega
  have hdrop : (List.ofFn (fifthTuple leaf.selected)).dropLast = chosen.take 4 := by
    rw [hofn, List.dropLast_eq_take, htake5, List.take_take]
  have hfirst4 : FirstExitValidSelection
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega N)
      [] true (chosen.take 4) := by
    apply validSelection_transfer_bounded
      (policy5 e chi m omega N rows4 licensed4 J5 rows5) _ 4
      (fun positive pre hshort =>
        policy5_through_four e chi m omega N rows4 licensed4 J5 rows5 positive pre hshort)
      [] (chosen.take 4) true
    · simp only [List.length_nil, Nat.zero_add, List.length_take]
      omega
    · exact validSelection_take _ [] chosen true hvalid 4
  apply (mem_firstExitFrontierTuples_iff 4 _ carrier _).mpr
  constructor
  · rw [hofn]
    exact (List.take_sublist 5 chosen).trans hsub
  · rw [hdrop]
    exact hfirst4

/-- The fifth cap is the actual inherited fourth maximum, or an attained
eligible FifthRow with its literal buffered M_I and all endpoint gates. -/
theorem level5_seed_or_attained_row (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega N : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (pre : List ℕ) (hlen : pre.length = 5) :
    level5 e chi m omega N rows4 licensed4 J5 rows5 pre =
        producerLevel4 (e : ℝ) chi m omega N rows4 licensed4 (rosserAncestor 4 pre) ∨
    ∃ r ∈ rows5, eligible e chi m omega J5 r (primeHistoryLogCoordinates N 5 pre) ∧
      level5 e chi m omega N rows4 licensed4 J5 rows5 pre =
        N ^ candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre) ∧
      candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre) =
        min ((1 + ∑ i ∈ r.selected, primeHistoryLogCoordinates N 5 pre i) / 2)
          (57 / 64 - (3 / 2 : ℝ) * ∑ i ∈ r.selected,
            primeHistoryLogCoordinates N 5 pre i) - 2 * (e : ℝ) ∧
      (1 / 2 : ℝ) < candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre) ∧
      (∀ k, prefixSquareExpr (primeHistoryLogCoordinates N 5 pre) k <
        candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre)) ∧
      (∀ k ∉ r.selected, selectedSquareExpr r.selected
        (primeHistoryLogCoordinates N 5 pre) k <
          candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre)) := by
  rcases finiteMax_seed_or_winning_row rows5
      (fun r => eligible e chi m omega J5 r (primeHistoryLogCoordinates N 5 pre))
      (fun r => candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre))
      (inherited4 e chi m omega N rows4 licensed4 pre) with hs | hr
  · left
    rw [← inherited4_eq_actual_fourth]
    change N ^ (if pre.length = 5 then _ else _) = _
    rw [if_pos hlen]
    exact congrArg (fun x : ℝ => N ^ x) hs.1
  · obtain ⟨r, hr, he, _hseed, _hrows, hmax⟩ := hr
    have hpow : level5 e chi m omega N rows4 licensed4 J5 rows5 pre =
        N ^ candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre) := by
      change N ^ (if pre.length = 5 then _ else _) = _
      rw [if_pos hlen]
      exact congrArg (fun x : ℝ => N ^ x) hmax
    exact Or.inr ⟨r, hr, he, hpow, candidate_eq_original_cap _ _ _,
      gateCheck_sound e m r _ he.2.1 he.2.2⟩

/-- The retained descendant's strict bound is attached to an attained
FifthRow or to its own inherited fourth ancestor, with no arbitrary row. -/
theorem retained_modulus_seed_or_attained_fifth_row (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (hlen : 5 ≤ leaf.selected.length) :
    (leaf.selected.prod : ℝ) < producerLevel4 (e : ℝ) chi m omega (N : ℝ)
        rows4 licensed4 (rosserAncestor 4 leaf.selected) ∨
    ∃ r ∈ rows5, eligible e chi m omega J5 r
        (primeHistoryLogCoordinates (N : ℝ) 5 (rosserAncestor 5 leaf.selected)) ∧
      (leaf.selected.prod : ℝ) < (N : ℝ) ^ candidate (e : ℝ) r.selected
        (primeHistoryLogCoordinates (N : ℝ) 5 (rosserAncestor 5 leaf.selected)) ∧
      (1 / 2 : ℝ) < candidate (e : ℝ) r.selected
        (primeHistoryLogCoordinates (N : ℝ) 5 (rosserAncestor 5 leaf.selected)) ∧
      (∀ k, prefixSquareExpr
          (primeHistoryLogCoordinates (N : ℝ) 5 (rosserAncestor 5 leaf.selected)) k <
        candidate (e : ℝ) r.selected
          (primeHistoryLogCoordinates (N : ℝ) 5 (rosserAncestor 5 leaf.selected))) ∧
      (∀ k ∉ r.selected, selectedSquareExpr r.selected
          (primeHistoryLogCoordinates (N : ℝ) 5 (rosserAncestor 5 leaf.selected)) k <
        candidate (e : ℝ) r.selected
          (primeHistoryLogCoordinates (N : ℝ) 5 (rosserAncestor 5 leaf.selected))) := by
  have h5 : (rosserAncestor 5 leaf.selected).length = 5 := by
    rw [rosserAncestor_length]
    omega
  have hstrict := P1OriginalHistoricalRetainedModulusLevel.actual_original_fifth_retained_leaf_prod_lt_current
    (e : ℝ) chi m omega N cap w z
    (level5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
    heupper hN (fun _ => 1) leaf hleaf
  rw [P1OriginalHistoricalRetainedModulusLevel.currentLevel_from_five
    (e : ℝ) chi m omega (N : ℝ) _ leaf.selected hlen] at hstrict
  rcases level5_seed_or_attained_row e chi m omega (N : ℝ) rows4 licensed4
      J5 rows5 (rosserAncestor 5 leaf.selected) h5 with hs | hr
  · left
    rw [rosserAncestor_nested 4 5 (by omega)] at hs
    exact hs ▸ hstrict
  · obtain ⟨r, hr, he, hcap, _hliteral, hhalf, hfull, hselected⟩ := hr
    exact Or.inr ⟨r, hr, he, hcap ▸ hstrict, hhalf, hfull, hselected⟩

/-- On the actual fifth owner, its original joint geometry and inherited
fourth profile are obtained from one real retained leaf. The fourth
ancestor used here is exactly the one in the attained-row alternative. -/
theorem retained_original_joint_and_inherited_profile
    (D : HistoricalPrefixCapData) (e : ℚ) (chi omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 D.m))
    (rows5 : Finset (FifthRow D.m)) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy5 e chi D.m omega (N : ℝ) rows4 licensed4 J5 rows5)
      (fun _ => 1) [] true 1
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))))
    (hlen : 5 ≤ leaf.selected.length)
    (j : P1CorrectedFifthDensityDictionary.Label5 D.m)
    (ht : actualPrimeTupleLog N (fifthTuple leaf.selected) ∈
      logPrimeMeshCell 0 (19 / 96) D.m j) :
    actualPrimeTupleLog N (fifthTuple leaf.selected) ∈
      HistoricalThirdCoarse.P1OriginalCoarseFifth.jointRegion
        (e : ℝ) chi D.m omega j ∧
    inherited4 e chi D.m omega (N : ℝ) rows4 licensed4 (rosserAncestor 5 leaf.selected) =
      P1CorrectedFifthDensityDictionary.originalVariableFourthProfile
        e chi omega D.m j rows4 licensed4 (actualPrimeTupleLog N (fifthTuple leaf.selected)) := by
  have hp := retained_fifth_ancestor_mem_original_candidates e chi D.m omega (N : ℝ)
    rows4 licensed4 J5 rows5 (fun _ => 1) _ leaf hleaf hlen
  have hjoint := (HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_candidates_iff_log_on_cell
    (e : ℝ) chi D.m omega N cap hN hcap (fifthTuple leaf.selected) j ht).mp hp
  have hpos : ∀ i, 0 < fifthTuple leaf.selected i := fun i => (hjoint.1 i).1.pos
  have h5 : (rosserAncestor 5 leaf.selected).length = 5 := by
    rw [rosserAncestor_length]
    omega
  have hh : tupleHistory (fifthTuple leaf.selected) = rosserAncestor 5 leaf.selected :=
    tupleHistory_primeHistoryTuple _ h5
  refine ⟨hjoint.2, ?_⟩
  have hprofile := original_fourth_exponent_on_fifth_cell D e chi omega rows4 licensed4
    N hN (fifthTuple leaf.selected) hpos j ht
  simpa only [hh, inherited4] using hprofile

/-- The physical attachment names exactly this original variable-fifth
policy, using its retained support and its own signed Mobius coefficient. -/
theorem fifth_same_physical_rho (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (N cap : ℕ) (w z L : ℝ) :
    actualSmallRoughRho (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 false)
      N cap w z L =
    smallRoughRho (actualSmallRosserSupport N cap w)
      (firstExitRetainedModuli
        (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
        (roughPrimeUniverse N cap w z))
      (fun d => (firstExitRetainedCoefficient
        (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
        (roughPrimeUniverse N cap w z) d : ℝ))
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) := by
  exact UpperPolicyFiniteBridge.actualSmallRoughRho_eq_firstExitAttachment
    (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) (by
      intro pre
      apply fifthCappedUpperPolicy_even_retained
      intro history
      simp [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy]) N cap w z L
/-- d=1 continues to come from the empty history of this exact fifth tree. -/
theorem fifth_empty_history_mem (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (carrier : List ℕ) :
    1 ∈ firstExitRetainedModuli
      (policy5 e chi m omega N rows4 licensed4 J5 rows5) carrier := by
  exact (mem_firstExitRetainedModuli _ _ _).mpr ⟨⟨[], true, 1⟩,
    firstExitRetainedLeaves_skipAll_mem _ _ [] carrier true 1, by simp⟩

end
end ImbalancedChen.P1OriginalFifthAttainedRowBinding