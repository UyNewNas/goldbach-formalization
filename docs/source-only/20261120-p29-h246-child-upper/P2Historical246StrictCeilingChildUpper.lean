import ImbalancedChen.P2Historical246WallPrefixRemoval
import ImbalancedChen.P2HistoricalLowerBankAncestry

/-! SOURCE ONLY / UNEVALUATED. Strict-ceiling rejection is retained as a
nonnegative term in the H246 upper-direction pair profile. This gives a one-sided upper comparison only. The manuscript positive
feedback requires a lower comparison, which is NOT provided here. No
sieve-count licence, reserve payment or H247 endpoint follows. -/
namespace ImbalancedChen.P2Historical246StrictCeilingChildUpper
noncomputable section
open Set Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2Historical246PairCarrierPartition P2Historical246BoundedPairBridge
open P2Historical246PairProductGate P2Historical246SuccessorParentWindow
open P2Historical246RepeatedCeilingBook P2Historical246RepeatedCeilingDecomposition
open P2Historical246WallPrefixRemoval P2OriginalChildPhysicalNormalization
open P2OriginalBankChildPrimeMass P2OriginalPositiveSameQMassLift
open P2HistoricalLowerBankAncestry P2HistoricalScheduledPointReads
open P2HistoricalNativePointCounts P2Historical248Authentication
open P2HistoricalW2ArchivedPairWindows
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

/-- Positivity alone is sufficient; no upper bound by Q80 is assumed. -/
theorem floorValue_nonnegative {nums : Fin 200 → ℤ}
    (hn : ∀ i, 0 ≤ nums i) (i : Fin 200) : 0 ≤ floorValue nums i := by
  have h : (0 : ℝ) ≤ (nums i : ℝ) := by exact_mod_cast hn i
  unfold floorValue
  exact div_nonneg h (by positivity)

theorem floorKnot_nonnegative {nums : Fin 200 → ℤ}
    (hn : ∀ i, 0 ≤ nums i) (j : Fin 201) : 0 ≤ floorKnotValue nums j := by
  unfold floorKnotValue
  split_ifs
  · exact floorValue_nonnegative hn _
  · exact floorValue_nonnegative hn _
  · exact le_min (floorValue_nonnegative hn _) (floorValue_nonnegative hn _)

theorem tableAtom_nonnegative {nums : Fin 200 → ℤ}
    (hn : ∀ i, 0 ≤ nums i) (b : FloorAtom) : 0 ≤ floorAtomValue nums b := by
  cases b with
  | inl i => exact floorValue_nonnegative hn i
  | inr j => exact floorKnot_nonnegative hn j

theorem tableFunction_nonnegative (lower : Bool) {nums : Fin 200 → ℤ}
    (hn : ∀ i, 0 ≤ nums i) (s : ℝ) : 0 ≤ tableFunction lower nums s := by
  unfold tableFunction
  apply Finset.sum_nonneg
  intro b hb
  by_cases hs : s ∈ tableAtomSet lower b
  · rw [Set.indicator_of_mem hs]
    exact tableAtom_nonnegative hn b
  · rw [Set.indicator_of_notMem hs]
    exact le_rfl

/-- All actual old H246 entries are nonnegative by retention of the
original nonnegative seed. No finite H246 table is evaluated here. -/
theorem actualH246_nonnegative (i : Fin 200) : 0 ≤ outputAt 246 true i := by
  exact iterate_nonnegative _ _ 246 true i

/-- Every actual half-carrier atom has nonnegative old H246 profile and
nonnegative true same-Q child Theta. The actual strict product gate is
proved from the original selected-square gate, not postulated. -/
theorem halfCarrier_oldAtom_nonnegative {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 4 ≤ N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (j : Fin 36) (k : Fin 4) {p : Pair} (hp : p ∈ halfCarrier N L j k) :
    0 ≤ oldPairAtom N Q L (parentProduct old) j k p := by
  have hbox := (Finset.mem_filter.mp hp).1
  have hp0 := ((mem_actualPrimeBoxTuples_iff.mp hbox) 0).1
  have hp1 := ((mem_actualPrimeBoxTuples_iff.mp hbox) 1).1
  have hprod : 0 < parentProduct old * p 0 * p 1 := Nat.mul_pos (Nat.mul_pos hd hp0.pos) hp1.pos
  have hgate := halfCarrier_productGate (by omega) hd hL hQ j k hp
  unfold productGate at hgate
  have hswap : parentProduct old * p 0 * p 1 = parentProduct old * p 1 * p 0 := by ac_rfl
  have hlt : ((parentProduct old * p 0 * p 1 : ℕ) : ℝ) < Q := by rw [hswap]; exact hgate
  have hR : 1 < Q/((parentProduct old * p 0 * p 1 : ℕ) : ℝ) :=
    (one_lt_div (Nat.cast_pos.mpr hprod)).mpr hlt
  unfold oldPairAtom
  exact mul_nonneg (thetaAtom_nonneg hN hprod hR)
    (tableFunction_nonnegative false actualH246_nonnegative _)

/-- Keep the entire strict-ceiling bucket as a nonnegative sum. -/
theorem successor_strict_ceiling_nonnegative {N horizon : ℕ} {nu eta : ℝ}
    (hN : 4 ≤ N) (he : 0 < eta) (m : Mark) (choice : SuccessorChoice)
    (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) (j : Fin 36) (k : Fin 4) :
    let old := oldWord t
    let Q := (N : ℝ)^nu
    let L := residualExponent N (parentProduct old) nu
    let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
    let c := ceilingPrime N m choice t
    0 ≤ ∑ p ∈ (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
      parentWindow N Q old chi ∧ bothCoprime N old p ∧ c < p 1),
      oldPairAtom N Q L (parentProduct old) j k p := by
  obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level (by omega) he m choice hm ht
  apply Finset.sum_nonneg
  intro p hp
  exact halfCarrier_oldAtom_nonnegative hN hd hL hQ j k (Finset.mem_filter.mp hp).1

/-- The genuine pairChildren Theta-profile contribution, with each
ordered W2 occurrence and the single original /5 kept. -/
def childLane (N : ℕ) (nu : ℝ) (m : Mark) (choice : SuccessorChoice)
    (t : Fin (advance m choice).rank → Fin (N+1)) (j : Fin 36) (k : Fin 4) : ℝ :=
  let old := oldWord t
  let Q := (N : ℝ)^nu
  let L := residualExponent N (parentProduct old) nu
  let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
  ∑ p ∈ pairChildren j k N Q old chi,
    oldPairAtom N Q L (parentProduct old) j k (pairValues p)

def childBook {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ (advance (marks a) (choices a)).source N nu,
    (advance (marks a) (choices a)).weight *
      ((∑ k : Fin 4, childLane N nu (marks a) (choices a) t j k)/5)

/-- The strict term need not be small: it is nonnegative, so the actual
child sum is below the exact strict-plus-child remainder. -/
theorem childBook_le_after {N horizon : ℕ} {nu eta : ℝ}
    (hN : 4 ≤ N) (he : 0 < eta)
    (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice)
    (hm : ∀ a ∈ A, (marks a).BoxRows nu eta horizon) (j : Fin 36) :
    childBook A marks choices N nu j ≤ bookAfterWallPrefix A marks choices N nu j := by
  unfold childBook bookAfterWallPrefix
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro t ht
  have hw : 0 ≤ (advance (marks a) (choices a)).weight := by
    exact mul_nonneg (advance_boxRows (marks a) (choices a) (hm a ha)).2.2.2.2
      (advance (marks a) (choices a)).history.scalar_nonneg
  apply mul_le_mul_of_nonneg_left _ hw
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 5)
  apply Finset.sum_le_sum
  intro k hk
  have hstrict := successor_strict_ceiling_nonnegative hN he (marks a) (choices a) (hm a ha) ht j k
  dsimp [laneAfterWallPrefix,childLane]
  linarith only [hstrict]

/-- Concrete one-sided upper comparison on the actual H246 tagged row.
The strict ceiling is not discarded from an equality and is not assumed
small. The child object remains a Theta-profile, not a sieve count. -/
theorem tagged_book_child_upper {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
        b.2.pairRows.length = 4 ∧ (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        let next := fun a => advance (marks a) (choices a)
        childBook A marks choices N nu j ≤ bookFull A marks choices N nu j +
          epsilon * Theta N ((N : ℝ)^nu)
            (sourceSupport A next N nu) (sourceSigma A next N nu) := by
  obtain ⟨T,hT,hremove⟩ := tagged_book_remove_wall_and_full_prefix he heps horizon
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu I A marks choices hm b hb
  obtain ⟨j,hparam,hlen,hlanes,hbound⟩ := hremove N hN nu hnu I A marks choices hm b hb
  refine ⟨j,hparam,hlen,hlanes,?_⟩
  have hchild := childBook_le_after (by omega) he I A marks choices hm j
  have hlow := (abs_le.mp hbound).1
  linarith only [hchild,hlow]


/-- The first literal archived row has these exact D5 boundaries. -/
theorem first_original_row_faces :
    a0 (originalW2At 0) = (50/227 : ℝ) ∧ a2 (originalW2At 0) = (10/29 : ℝ) := by
  constructor <;> norm_num [a0,a2,originalW2At,originalRepairedW2Bank]

/-- A genuine open rectangle in original row 0, D5 lies strictly across
an inherited relative ceiling 2/7: u<2/7<v. This is a geometry witness,
not an assertion that any actual N has primes in the rectangle. -/
theorem first_original_row_ceiling_cuts_open_rectangle {u v : ℝ}
    (hu0 : (249/1000 : ℝ) < u) (hu1 : u < 251/1000)
    (hv0 : (299/1000 : ℝ) < v) (hv1 : v < 301/1000) :
    ![u,v] ∈ W2PairDomain (originalW2At 0) 0 ∧ u < 2/7 ∧ 2/7 < v := by
  obtain ⟨ha0,ha2⟩ := first_original_row_faces
  constructor
  · change a0 (originalW2At 0) < u ∧ u < v ∧
      v < a2 (originalW2At 0) ∧ v+2*u < 1
    rw [ha0,ha2]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  · constructor <;> linarith

/-- Exact physical parameters compatible with alpha≥2 and the previous
singleton relative exponent 2/9: chi/L=2/7. This is an exponent-level
calculation, not construction of a marked prime tuple. -/
theorem ceiling_cut_physical_parameters :
    (0 : ℝ) < (4/45) ∧ (4/45 : ℝ) < 2/5 ∧
      (2/5 : ℝ) - 4/45 = 14/45 ∧
      (4/45 : ℝ)/(2/5) = 2/9 ∧
      (4/45 : ℝ)/(14/45) = 2/7 ∧
      2 ≤ (1-(4/45 : ℝ))/(14/45) := by norm_num

/-- The preceding singleton exponent itself lies in the first original
W2 singleton domain. No actual prime-count assertion is used. -/
theorem first_original_singleton_has_example :
    (2/9 : ℝ) ∈ W2SingletonDomain (originalW2At 0) 0 := by
  change a0 (originalW2At 0) < (2/9 : ℝ) ∧ (2/9 : ℝ) < b (originalW2At 0)
  obtain ⟨ha0,_⟩ := first_original_row_faces
  rw [ha0]
  norm_num [b,originalW2At,originalRepairedW2Bank]

end
end ImbalancedChen.P2Historical246StrictCeilingChildUpper
