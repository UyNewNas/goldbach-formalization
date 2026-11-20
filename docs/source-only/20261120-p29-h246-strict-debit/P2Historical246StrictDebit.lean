import ImbalancedChen.P2Historical246StrictCeilingChildUpper

/-! SOURCE ONLY / UNEVALUATED. Exact actual strict-ceiling debit, a
correct-direction lower comparison with that debit retained, and a
positive real-domain witness for the actual H246 row-0 profile. This is
not a sieve-count licence, reserve payment, prime-count counterexample
or H247 endpoint. -/
namespace ImbalancedChen.P2Historical246StrictDebit
noncomputable section
open Set Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2Historical246PairCarrierPartition P2Historical246RepeatedCeilingBook
open P2Historical246RepeatedCeilingDecomposition P2Historical246WallPrefixRemoval
open P2Historical246StrictCeilingChildUpper P2OriginalChildPhysicalNormalization
open P2HistoricalLowerBankAncestry P2HistoricalScheduledPointReads
open P2HistoricalNativePointCounts P2Historical248Authentication
open P2HistoricalW2ArchivedPairWindows
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound P5OriginalFeedbackDomains
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

/-- Exact strict-ceiling rejected Theta-profile, retaining original
interior, prefix-coprime and parent gates, per ordered W2 occurrence. -/
def strictLane (N : ℕ) (nu : ℝ) (m : Mark) (choice : SuccessorChoice)
    (t : Fin (advance m choice).rank → Fin (N+1)) (j : Fin 36) (k : Fin 4) : ℝ :=
  let old := oldWord t
  let Q := (N : ℝ)^nu
  let L := residualExponent N (parentProduct old) nu
  let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
  let c := ceilingPrime N m choice t
  ∑ p ∈ (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
    parentWindow N Q old chi ∧ bothCoprime N old p ∧ c < p 1),
    oldPairAtom N Q L (parentProduct old) j k p

def strictBook {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ (advance (marks a) (choices a)).source N nu,
    (advance (marks a) (choices a)).weight *
      ((∑ k : Fin 4, strictLane N nu (marks a) (choices a) t j k)/5)

/-- Finite signed equality, not a claim that the strict debit is small. -/
theorem after_eq_strict_add_child {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) :
    bookAfterWallPrefix A marks choices N nu j = strictBook A marks choices N nu j +
      childBook A marks choices N nu j := by
  unfold bookAfterWallPrefix strictBook childBook
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hk : (∑ k : Fin 4, laneAfterWallPrefix N nu (marks a) (choices a) t j k) =
      (∑ k : Fin 4, strictLane N nu (marks a) (choices a) t j k) +
      (∑ k : Fin 4, childLane N nu (marks a) (choices a) t j k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rfl
  rw [hk]
  ring

/-- Correct lower direction for the actual child Theta-profile, retaining
the full explicit strict-ceiling debit and a separate epsilon Theta. -/
theorem tagged_book_child_lower_with_strict_debit {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
        b.2.pairRows.length = 4 ∧ (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        let next := fun a => advance (marks a) (choices a)
        bookFull A marks choices N nu j - strictBook A marks choices N nu j -
          epsilon * Theta N ((N : ℝ)^nu)
            (sourceSupport A next N nu) (sourceSigma A next N nu) ≤
        childBook A marks choices N nu j := by
  obtain ⟨T,hT,hremove⟩ := tagged_book_remove_wall_and_full_prefix he heps horizon
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu I A marks choices hm b hb
  obtain ⟨j,hparam,hlen,hlanes,hbound⟩ := hremove N hN nu hnu I A marks choices hm b hb
  refine ⟨j,hparam,hlen,hlanes,?_⟩
  have hplus := (abs_le.mp hbound).2
  rw [after_eq_strict_add_child] at hplus
  linarith only [hplus]
/-- The debit has the manuscript's positive sign; it is not silently
absorbed by the wall or prefix allowance. -/
theorem strictBook_nonnegative {N horizon : ℕ} {nu eta : ℝ}
    (hN : 4 ≤ N) (he : 0 < eta)
    (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice)
    (hm : ∀ a ∈ A, (marks a).BoxRows nu eta horizon) (j : Fin 36) :
    0 ≤ strictBook A marks choices N nu j := by
  unfold strictBook
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro t ht
  have hw : 0 ≤ (advance (marks a) (choices a)).weight := by
    exact mul_nonneg (advance_boxRows (marks a) (choices a) (hm a ha)).2.2.2.2
      (advance (marks a) (choices a)).history.scalar_nonneg
  apply mul_nonneg hw
  apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 5)
  apply Finset.sum_nonneg
  intro k hk
  exact successor_strict_ceiling_nonnegative hN he (marks a) (choices a) (hm a ha) ht j k

/-- Retention, without evaluating H246, keeps the explicitly positive
original seed in the historical open grid cell 52. -/
theorem actualH246_cell52_positive : 0 < outputAt 246 true (52 : Fin 200) := by
  have hseed : 0 < originalSeed true (52 : Fin 200) := by
    norm_num [originalSeed, P2TableActionSourceOnly.tableQ]
  have hretain (n : ℕ) : originalSeed true (52 : Fin 200) ≤ outputAt n true (52 : Fin 200) := by
    induction n with
    | zero => simp [outputAt,iterate]
    | succ n ih => exact ih.trans (iterate_retains _ _ n true (52 : Fin 200))
  exact hseed.trans_le (hretain 246)

/-- On a narrower explicit open rectangle the genuine row-0 D5 profile
argument lies strictly inside historical grid cell 52. -/
theorem first_row_profile_in_cell52 {u v : ℝ}
    (hu0 : (2499/10000 : ℝ) < u) (hu1 : u < 2501/10000)
    (hv0 : (2999/10000 : ℝ) < v) (hv1 : v < 3001/10000) :
    (51/25 : ℝ) < pairProfile (originalW2At 0) 0 ![u,v] ∧
      pairProfile (originalW2At 0) 0 ![u,v] < 103/50 := by
  have hs : (originalW2At 0).s0 = (227/50 : ℝ) := by
    norm_num [originalW2At,originalRepairedW2Bank]
  change (51/25 : ℝ) < (originalW2At 0).s0 * (1-u-v) ∧
    (originalW2At 0).s0 * (1-u-v) < 103/50
  rw [hs]
  constructor <;> linarith

/-- The exact old H246 table lookup is strictly positive on this real
cut rectangle. This is a statement about the profile function, not
about the existence or density of actual primes. -/
theorem first_row_cut_old_profile_positive {u v : ℝ}
    (hu0 : (2499/10000 : ℝ) < u) (hu1 : u < 2501/10000)
    (hv0 : (2999/10000 : ℝ) < v) (hv1 : v < 3001/10000) :
    ![u,v] ∈ W2PairDomain (originalW2At 0) 0 ∧ u < 2/7 ∧ 2/7 < v ∧
      0 < tableFunction false (outputAt 246 true) (pairProfile (originalW2At 0) 0 ![u,v]) := by
  have hwide0 : (249/1000 : ℝ) < u := by linarith
  have hwide1 : u < (251/1000 : ℝ) := by linarith
  have hwide2 : (299/1000 : ℝ) < v := by linarith
  have hwide3 : v < (301/1000 : ℝ) := by linarith
  obtain ⟨hdom,hule,hvgt⟩ := first_original_row_ceiling_cuts_open_rectangle hwide0 hwide1 hwide2 hwide3
  refine ⟨hdom,hule,hvgt,?_⟩
  let rho := pairProfile (originalW2At 0) 0 ![u,v]
  let atom : FloorAtom := Sum.inl (52 : Fin 200)
  have hcell := first_row_profile_in_cell52 hu0 hu1 hv0 hv1
  have hmem : rho ∈ upperAtomSet atom := by
    change (((1 : ℝ) ≤ rho ∧ rho ≤ 5) ∧
      (floorGrid 52 < rho ∧ rho < floorGrid 53))
    norm_num [floorGrid]
    constructor <;> constructor <;> linarith [hcell.1,hcell.2]
  have hlookup : tableFunction false (outputAt 246 true) rho =
      floorValue (outputAt 246 true) (52 : Fin 200) := by
    rw [tableFunction_upper]
    unfold upperFloor
    calc
      _ = (upperAtomSet atom).indicator (fun _ => floorAtomValue (outputAt 246 true) atom) rho := by
        apply Finset.sum_eq_single atom
        · intro c _ hca
          exact indicator_of_notMem (fun hc => hca (P5Z.U11H248.upperAtom_unique hc hmem)) _
        · intro h
          exact (h (Finset.mem_univ atom)).elim
      _ = _ := by simp [hmem,atom,floorAtomValue]
  have hpositive : 0 < floorValue (outputAt 246 true) (52 : Fin 200) := by
    unfold floorValue
    exact div_pos (by exact_mod_cast actualH246_cell52_positive) (by positivity)
  rw [hlookup]
  exact hpositive

end
end ImbalancedChen.P2Historical246StrictDebit
