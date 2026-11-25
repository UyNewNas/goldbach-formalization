import ImbalancedChen.P2OriginalPairBufferedRootProvenance
import ImbalancedChen.P5OriginalU5PhysicalRho

/-!
# Actual U5 fresh-fifth source to complete signed square support

SOURCE ONLY / UNCOMPILED / NO KERNEL ACCEPTANCE.

This leaf uses the literal original U5 selectedPolicy and its double-buffer
pair plan.  The fresh-fifth condition is the actual finite source decision
and its checked action; it is not a full-square, factorization or modulus
assumption.  Existing point-square, exact frozen-cap, accepted post-five,
and signed-small suppliers produce the complete two square lists.

The result is at this SAME affine source's once-buffered support cover,
not at the global carrier exponent 0.599.  No density-level identification
or change is made. Short words and inherited fifth actions
remain outside this explicitly named subfamily.  No adoption, whole-box
three-factor representation or PP estimate is asserted.
-/

namespace ImbalancedChen.P3OriginalU5FreshFifthSquareSupplier

noncomputable section
open scoped Classical List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer P2OriginalSelectedPairNativeData
open P2OriginalPairSourceReceiver
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank SelectedBranchData)
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalSelectedIntegerPrefixSquares
open P2OriginalSelectedNativeSmallExtension
open P2OriginalPostFifthRoughSquares
open P2OriginalSelectedFifthRoughBudget (original_U5_small_head)
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV (fullModulus)

def fivePrimes (t : ℕ × ℕ) (q₀ q₁ q₂ : ℕ) : Fin 5 → ℕ :=
  ![t.2, t.1, q₀, q₁, q₂]

def fiveCode (R : PairRange) (mesh N : ℕ) (t : ℕ × ℕ) (q₀ q₁ q₂ : ℕ) : Code mesh :=
  codeAt R mesh 5
    [coordinate N t.2, coordinate N t.1, coordinate N q₀,
      coordinate N q₁, coordinate N q₂]

def fiveSlots (R : PairRange) (mesh N : ℕ) (t : ℕ × ℕ) (q₀ q₁ q₂ : ℕ)
    (branch : SelectedBranchData) : List (ℕ × Bool) :=
  integerPrefixSlots 5 (fiveCode R mesh N t q₀ q₁ q₂)
    branch.form.supportMask (fivePrimes t q₀ q₁ q₂)

def roughSlots (R : PairRange) (mesh N : ℕ) (t : ℕ × ℕ) (q₀ q₁ q₂ : ℕ)
    (ds : List ℕ) (branch : SelectedBranchData) : List (ℕ × Bool) :=
  appendUnselected (fiveSlots R mesh N t q₀ q₁ q₂ branch) ds

def sourceLevel (R : PairRange) (mesh N : ℕ) (t : ℕ × ℕ) (q₀ q₁ q₂ : ℕ)
    (buffer : ℚ) (branch : SelectedBranchData) : ℝ :=
  (rowCap R (fiveCode R mesh N t q₀ q₁ q₂) buffer branch : ℝ)

def fiveTrace (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (N : ℕ) (t : ℕ × ℕ) (q₀ q₁ q₂ : ℕ) : Trace :=
  run (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
    (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N t (rootSeed false buffer N t))
    [coordinate N q₀, coordinate N q₁, coordinate N q₂]

/-- The actual finite fresh action, on the actual code and actual parent.
No desired square or final-modulus condition is a field. -/
def FreshFifth (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (N : ℕ) (t : ℕ × ℕ) (q₀ q₁ q₂ : ℕ)
    (branch : SelectedBranchData) : Prop :=
  select R bank (2 * buffer) 5 (fiveCode R mesh N t q₀ q₁ q₂) = some branch ∧
    freshCheck R 5 (fiveCode R mesh N t q₀ q₁ q₂) (2 * buffer)
      (cap4 R bank (2 * buffer) (rootSeed false buffer N t)
        (fiveCode R mesh N t q₀ q₁ q₂)) branch

private theorem prefixCode_five {mesh : ℕ} (code : Code mesh) :
    prefixCode 5 code = code := by
  funext i
  exact if_pos i.isLt

private theorem fiveSlots_values (R : PairRange) (mesh N : ℕ) (t : ℕ × ℕ)
    (q₀ q₁ q₂ : ℕ) (branch : SelectedBranchData) :
    (fiveSlots R mesh N t q₀ q₁ q₂ branch).map Prod.fst =
      [t.2, t.1, q₀, q₁, q₂] := rfl

private theorem roughSlots_values (R : PairRange) (mesh N : ℕ) (t : ℕ × ℕ)
    (q₀ q₁ q₂ : ℕ) (ds : List ℕ) (branch : SelectedBranchData) :
    (roughSlots R mesh N t q₀ q₁ q₂ ds branch).map Prod.fst =
      t.2 :: t.1 :: q₀ :: q₁ :: q₂ :: ds := by
  rw [roughSlots, appendUnselected_values, fiveSlots_values]
  rfl

private theorem sourceLevel_buffers (R : PairRange) (mesh N : ℕ) (t : ℕ × ℕ)
    (q₀ q₁ q₂ : ℕ) (buffer : ℚ) (branch : SelectedBranchData) :
    sourceLevel R mesh N t q₀ q₁ q₂ (2 * buffer) branch + (buffer : ℝ) =
      sourceLevel R mesh N t q₀ q₁ q₂ buffer branch := by
  simp only [sourceLevel, rowCap, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  ring

theorem integer_gates_mono {N B : ℕ} {c d : ℝ}
    (hN : 1 < (N : ℝ)) (hcd : c ≤ d) (ps : List ℕ)
    (h : IntegerSquareGates N c B ps) : IntegerSquareGates N d B ps := by
  apply integerSquareGates_of_indexed
  intro i hi
  exact (integerSquareGates_at ps h i hi).trans
    (Real.rpow_le_rpow_of_exponent_le hN.le hcd)

/-- Original carrier facts needed by both existing consumers. The grid
allocation is scalar and chosen before the actual row is inspected. -/
theorem original_word_data
    (R : PairRange) (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    {chosen : List ℕ}
    (hsub : chosen <+ roughPrimeUniverse N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N)) :
    (∀ p ∈ t.2 :: t.1 :: chosen, p.Prime) ∧
      (t.2 :: t.1 :: chosen).Pairwise (· ≥ ·) ∧
      (∀ p ∈ t.2 :: t.1 :: chosen, smallCutoff N epsilon ≤ (p : ℝ)) ∧
      (∀ p ∈ t.2 :: t.1 :: chosen,
        coordinate N p ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ)) := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hc, hA, horder, hH⟩ := Finset.mem_filter.mp ht
  obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp hc
  have hp₁ := (mem_chenAdditivePrimeCarrier.mp ht₁).2.1
  have hp₂ := (mem_chenAdditivePrimeCarrier.mp ht₂).2.1
  have hroughPrime : ∀ p ∈ chosen, p.Prime :=
    fun p hp => mem_roughPrimeUniverse_prime (hsub.subset hp)
  have hprime : ∀ p ∈ t.2 :: t.1 :: chosen, p.Prime := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hp₂
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hp₁
    · exact hroughPrime p hp
  have hroughLt : ∀ p ∈ chosen, p < t.1 := by
    intro p hp
    exact_mod_cast (mem_roughPrimeUniverse_upper (hsub.subset hp)).trans_le hA
  have hroughOrder : chosen.Pairwise (· ≥ ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    exact ((List.pairwise_iff_getElem.mp
      ((roughPrimeUniverse_pairwise_gt N (Nat.ceil (cutoff N))
        (smallCutoff N epsilon) (cutoff N)).sublist hsub)) i j hi hj hij).le
  have hsorted : (t.2 :: t.1 :: chosen).Pairwise (· ≥ ·) := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, List.pairwise_cons.mpr ⟨fun p hp => (hroughLt p hp).le, hroughOrder⟩⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact horder.le
    · exact (hroughLt p hp).le.trans horder.le
  have h12 : (t.1 : ℝ) ≤ t.2 := by exact_mod_cast horder.le
  have hw := (attachment_gates hN hepsilon hepsilon8).2.2
  have hcut : ∀ p ∈ t.2 :: t.1 :: chosen, smallCutoff N epsilon ≤ (p : ℝ) := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (hw.trans hA).trans h12
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hw.trans hA
    · exact mem_roughPrimeUniverse_lower (hsub.subset hp)
  have hR : (R.epsilon : ℝ) ≤ (417 / 5000 : ℝ) := by
    have hcast : (R.epsilon : ℝ) ≤ ((417 / 5000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr R.epsilon_lt_a.le
    norm_num at hcast ⊢
    exact hcast
  have hlow : (N : ℝ) ^ (R.epsilon : ℝ) ≤ cutoff N :=
    Real.rpow_le_rpow_of_exponent_le hNr.le hR
  have haD : cutoff N ≤ (N : ℝ) ^ (ceiling : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num [ceiling])
  have hhD : (N : ℝ) ^ (19 / 125 : ℝ) ≤ (N : ℝ) ^ (ceiling : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num [ceiling])
  have hpow : ∀ p ∈ t.2 :: t.1 :: chosen,
      (N : ℝ) ^ (R.epsilon : ℝ) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ (N : ℝ) ^ (ceiling : ℝ) := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨(hlow.trans hA).trans h12, hH.le.trans hhD⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hlow.trans hA, h12.trans (hH.le.trans hhD)⟩
    · exact ⟨(Real.rpow_le_rpow_of_exponent_le hNr.le hgrid).trans
        (mem_roughPrimeUniverse_lower (hsub.subset hp)),
        (mem_roughPrimeUniverse_upper (hsub.subset hp)).le.trans haD⟩
  refine ⟨hprime, hsorted, hcut, ?_⟩
  intro p hp
  constructor
  · apply (Real.rpow_le_rpow_left_iff hNr).mp
    rw [coordinate_power hNr (hprime p hp).pos]
    exact (hpow p hp).1
  · apply (Real.rpow_le_rpow_left_iff hNr).mp
    rw [coordinate_power hNr (hprime p hp).pos]
    exact (hpow p hp).2

/-- A genuine fifth source supplies all accepted rough suffix squares and
the literal small-level budget at its once-buffered source cover.
No old square list, row-to-trace identity or product budget is an input. -/
theorem actual_U5_fresh_fifth_rough_supply
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hbuffer : 0 ≤ buffer)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    (halloc : attachmentNu * epsilon ≤ (buffer : ℝ))
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (q₀ q₁ q₂ : ℕ) (ds : List ℕ)
    (hsub : q₀ :: q₁ :: q₂ :: ds <+ roughPrimeUniverse N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N))
    (haccept :
      (run (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
        (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N t (rootSeed false buffer N t))
        ((q₀ :: q₁ :: q₂ :: ds).map (coordinate N))).accepted = true)
    (branch : SelectedBranchData) (hfresh : FreshFifth R bank buffer N t q₀ q₁ q₂ branch) :
    let slots := roughSlots R mesh N t q₀ q₁ q₂ ds branch
    let cover := sourceLevel R mesh N t q₀ q₁ q₂ buffer branch
    (fiveTrace R bank buffer N t q₀ q₁ q₂).cap =
        sourceLevel R mesh N t q₀ q₁ q₂ (2 * buffer) branch ∧
      IntegerSquareGates N cover 1 (slots.map Prod.fst) ∧
      IntegerSquareGates N cover (selectedPrimes slots).prod (remainingPrimes slots) ∧
      ((slots.map Prod.fst).prod : ℝ) * smallLevel N epsilon < (N : ℝ) ^ cover := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hd := original_word_data R epsilon hepsilon hepsilon8 hgrid hN ht hsub
  have hx : ∀ i, coordinate N (fivePrimes t q₀ q₁ q₂ i) ∈
      Set.Icc (R.epsilon : ℝ) (ceiling : ℝ) := by
    intro i
    fin_cases i <;> exact hd.2.2.2 _ (by simp [fivePrimes])
  have hcap : (fiveTrace R bank buffer N t q₀ q₁ q₂).cap =
      sourceLevel R mesh N t q₀ q₁ q₂ (2 * buffer) branch := by
    have h := actual_fifth_source_cap R bank (2 * buffer) (rootSeed false buffer N t)
      (coordinate N t.2) (coordinate N t.1) (coordinate N q₀)
      (coordinate N q₁) (coordinate N q₂) branch
      (by simpa only [prefixCode_five] using hfresh.1)
      (by simpa only [prefixCode_five] using hfresh.2)
    simpa only [fiveTrace, pairRoot, sourceLevel, fiveCode, prefixCode_five] using h
  have hpoint := selected_fifth_point_squares R bank (2 * buffer)
    (fun i => coordinate N (fivePrimes t q₀ q₁ q₂ i)) hx branch
    (by simpa [fiveCode, fivePrimes] using hfresh.1)
  have hinit :
      P2EnhancedLowerPhysicalNode.SquareGates
        (sourceLevel R mesh N t q₀ q₁ q₂ (2 * buffer) branch) 0
        ((logSlots N (fiveSlots R mesh N t q₀ q₁ q₂ branch)).map
          P2EnhancedLowerPhysicalNode.Slot.exponent) ∧
      P2EnhancedLowerPhysicalNode.SquareGates
        (sourceLevel R mesh N t q₀ q₁ q₂ (2 * buffer) branch)
        (P2EnhancedLowerPhysicalNode.selectedWord
          (logSlots N (fiveSlots R mesh N t q₀ q₁ q₂ branch))).sum
        (P2EnhancedLowerPhysicalNode.remainingWord
          (logSlots N (fiveSlots R mesh N t q₀ q₁ q₂ branch))) := by
    simpa [prefixCode_five, sourceLevel, fiveCode, fiveSlots, fivePrimes,
      logSlots, integerPrefixSlots, integerPointSlot,
      P2OriginalPairSourceReceiver.pointSlots, P2OriginalPairSourceReceiver.pointSlot]
      using hpoint
  have hlen : (fiveTrace R bank buffer N t q₀ q₁ q₂).word.length = 5 := by
    simp [fiveTrace, run_word, pairRoot]
  have hword :
      (logSlots N (fiveSlots R mesh N t q₀ q₁ q₂ branch)).map
          P2EnhancedLowerPhysicalNode.Slot.exponent =
        (fiveTrace R bank buffer N t q₀ q₁ q₂).word := by
    simp [fiveTrace, run_word, pairRoot, fiveSlots, fivePrimes,
      logSlots, integerPrefixSlots, integerPointSlot]
  have hpos : ∀ v ∈ fiveSlots R mesh N t q₀ q₁ q₂ branch, 0 < v.1 := by
    intro v hv
    have hv' : v.1 ∈ (fiveSlots R mesh N t q₀ q₁ q₂ branch).map Prod.fst :=
      List.mem_map.mpr ⟨v, hv, rfl⟩
    rw [fiveSlots_values] at hv'
    have hwhole : v.1 ∈ [t.2, t.1, q₀, q₁, q₂] ++ ds :=
      List.mem_append.mpr (Or.inl hv')
    exact (hd.1 v.1 (by simpa using hwhole)).pos
  have hdsPrime : ∀ p ∈ ds, p.Prime := by
    intro p hp
    exact hd.1 p (by simp [hp])
  have hs₁ := (List.pairwise_cons.mp hd.2.1).2
  have hs₂ := (List.pairwise_cons.mp hs₁).2
  have hs₃ := (List.pairwise_cons.mp hs₂).2
  have hs₄ := (List.pairwise_cons.mp hs₃).2
  have hdsSort := (List.pairwise_cons.mp hs₄).2
  have hsuffix :
      (run (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
        (R.epsilon : ℝ) (ceiling : ℝ) (fiveTrace R bank buffer N t q₀ q₁ q₂)
        (ds.map (coordinate N))).accepted = true := by
    change (run _ _ _ _
      ([coordinate N q₀, coordinate N q₁, coordinate N q₂] ++ ds.map (coordinate N))).accepted
        = true at haccept
    rw [run_append] at haccept
    exact haccept
  have hrough := actual_postfive_integer_gates
    (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
    (R.epsilon : ℝ) (ceiling : ℝ) hNr
    (fiveTrace R bank buffer N t q₀ q₁ q₂) hlen
    (fiveSlots R mesh N t q₀ q₁ q₂ branch) hword hpos
    (by rw [hcap]; exact hinit.1) (by rw [hcap]; exact hinit.2)
    ds hdsPrime hdsSort hsuffix
  rw [hcap] at hrough
  have hroughPrime : ∀ p ∈ (roughSlots R mesh N t q₀ q₁ q₂ ds branch).map Prod.fst,
      1 < p := by
    intro p hp
    rw [roughSlots_values] at hp
    exact (hd.1 p hp).one_lt
  have hne : (roughSlots R mesh N t q₀ q₁ q₂ ds branch).map Prod.fst ≠ [] := by
    rw [roughSlots_values]
    simp
  have hprod := integerSquareGates_product_lt
    ((roughSlots R mesh N t q₀ q₁ q₂ ds branch).map Prod.fst)
    (by decide : 0 < (1 : ℕ)) hroughPrime hne hrough.1
  simp only [Nat.one_mul] at hprod
  have hL := P2OriginalPairBufferedRootProvenance.fifth_native_small_level_budget
    hNr epsilon buffer halloc
  have hbudget :
      (((roughSlots R mesh N t q₀ q₁ q₂ ds branch).map Prod.fst).prod : ℝ) *
        smallLevel N epsilon <
          (N : ℝ) ^ sourceLevel R mesh N t q₀ q₁ q₂ buffer branch := by
    calc
      _ ≤ (((roughSlots R mesh N t q₀ q₁ q₂ ds branch).map Prod.fst).prod : ℝ) *
          (N : ℝ) ^ (buffer : ℝ) := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
      _ < (N : ℝ) ^ sourceLevel R mesh N t q₀ q₁ q₂ (2 * buffer) branch *
          (N : ℝ) ^ (buffer : ℝ) :=
        mul_lt_mul_of_pos_right hprod (Real.rpow_pos_of_pos (zero_lt_one.trans hNr) _)
      _ = _ := by
        rw [← Real.rpow_add (zero_lt_one.trans hNr), sourceLevel_buffers]
  have hlevels : sourceLevel R mesh N t q₀ q₁ q₂ (2 * buffer) branch ≤
      sourceLevel R mesh N t q₀ q₁ q₂ buffer branch := by
    have hb : 0 ≤ (buffer : ℝ) := by exact_mod_cast hbuffer
    linarith [sourceLevel_buffers R mesh N t q₀ q₁ q₂ buffer branch]
  exact ⟨hcap, integer_gates_mono hNr hlevels _ hrough.1,
    integer_gates_mono hNr hlevels _ hrough.2, hbudget⟩

/-- Outputs tied to the same native coefficient, same factor witness and
same actual fifth SourceForm. No field is a factorization or PP premise. -/
structure SignedFifthSupply
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (buffer : ℚ)
    (epsilon : ℝ) (N : ℕ) (t : ℕ × ℕ) (k s q₀ q₁ q₂ : ℕ)
    (ds : List ℕ) (branch : SelectedBranchData) : Prop where
  frozen_cap : (fiveTrace R bank buffer N t q₀ q₁ q₂).cap =
    sourceLevel R mesh N t q₀ q₁ q₂ (2 * buffer) branch
  full : IntegerSquareGates N (sourceLevel R mesh N t q₀ q₁ q₂ buffer branch) 1
    ((appendUnselected (roughSlots R mesh N t q₀ q₁ q₂ ds branch)
      s.primeFactorsList.reverse).map Prod.fst)
  selected : IntegerSquareGates N (sourceLevel R mesh N t q₀ q₁ q₂ buffer branch)
    (selectedPrimes (appendUnselected (roughSlots R mesh N t q₀ q₁ q₂ ds branch)
      s.primeFactorsList.reverse)).prod
    (remainingPrimes (appendUnselected (roughSlots R mesh N t q₀ q₁ q₂ ds branch)
      s.primeFactorsList.reverse))
  mask_preserved : selectedPrimes
    (appendUnselected (roughSlots R mesh N t q₀ q₁ q₂ ds branch) s.primeFactorsList.reverse) =
      selectedPrimes (fiveSlots R mesh N t q₀ q₁ q₂ branch)
  canonical : (appendUnselected (roughSlots R mesh N t q₀ q₁ q₂ ds branch)
    s.primeFactorsList.reverse).map Prod.fst = (fullModulus t k).primeFactorsList.reverse
  same_rho : rho N epsilon (selectedPolicy R bank buffer false N t) k =
    P5CausalRhoFactorization.coefficient (selectedPolicy R bank buffer false N t)
      N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon)
      (s, (q₀ :: q₁ :: q₂ :: ds).prod)

theorem actual_U5_fresh_fifth_signed_supply
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hbuffer : 0 ≤ buffer)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    (halloc : attachmentNu * epsilon ≤ (buffer : ℝ))
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {k s : ℕ}
    (hk : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0)
    (hs : s ∈ actualSmallRosserSupport N (Nat.ceil (cutoff N)) (smallCutoff N epsilon))
    (q₀ q₁ q₂ : ℕ) (ds : List ℕ)
    (hkprod : k = s * (q₀ :: q₁ :: q₂ :: ds).prod)
    (hsub : q₀ :: q₁ :: q₂ :: ds <+ roughPrimeUniverse N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N))
    (haccept :
      (run (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
        (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N t (rootSeed false buffer N t))
        ((q₀ :: q₁ :: q₂ :: ds).map (coordinate N))).accepted = true)
    (branch : SelectedBranchData) (hfresh : FreshFifth R bank buffer N t q₀ q₁ q₂ branch) :
    SignedFifthSupply R bank buffer epsilon N t k s q₀ q₁ q₂ ds branch := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hr : (q₀ :: q₁ :: q₂ :: ds).prod ∈ fixedEvenRoughSupport
      (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N) := by
    apply (pair_policy_support_iff
      (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
      (R.epsilon : ℝ) (ceiling : ℝ) (rootSeed false buffer N t)
      N (Nat.ceil (cutoff N)) t (smallCutoff N epsilon) (cutoff N) _).mpr
    exact ⟨q₀ :: q₁ :: q₂ :: ds, hsub, haccept, rfl⟩
  have hpairs : (s, (q₀ :: q₁ :: q₂ :: ds).prod) ∈ P5CausalRhoFactorization.pairs
      (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N) := Finset.mem_product.mpr ⟨hs, hr⟩
  have hvalue := P5CausalRhoFactorization.rho_at_pair
    (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
    (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon) hpairs
  have hactive : (s, (q₀ :: q₁ :: q₂ :: ds).prod) ∈ P5CausalRhoFactorization.activePairs
      (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon) := by
    apply Finset.mem_filter.mpr
    refine ⟨hpairs, ?_⟩
    rw [← hvalue, ← hkprod]
    exact hk
  have hrough := actual_U5_fresh_fifth_rough_supply R bank buffer hbuffer
    epsilon hepsilon hepsilon8 hgrid halloc hN ht q₀ q₁ q₂ ds hsub haccept branch hfresh
  have hd := original_word_data R epsilon hepsilon hepsilon8 hgrid hN ht hsub
  have hprod : ((roughSlots R mesh N t q₀ q₁ q₂ ds branch).map Prod.fst).prod =
      (t.1 * t.2) * (q₀ :: q₁ :: q₂ :: ds).prod := by
    rw [roughSlots_values]
    simp only [List.prod_cons]
    ac_rfl
  have hsmall := actual_signed_small_extension
    (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N)) (t.1 * t.2)
    (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon)
    (sourceLevel R mesh N t q₀ q₁ q₂ buffer branch)
    hactive (original_U5_small_head hNr hepsilon.le hepsilon8.le)
    (roughSlots R mesh N t q₀ q₁ q₂ ds branch) hprod
    (by rw [roughSlots_values]; exact hd.1)
    (by rw [roughSlots_values]; exact hd.2.1)
    (by rw [roughSlots_values]; exact hd.2.2.1)
    hrough.2.1 hrough.2.2.1 (by rw [← hprod]; exact hrough.2.2.2.le)
  refine ⟨hrough.1, hsmall.1, hsmall.2.1, ?_, ?_, ?_⟩
  · exact hsmall.2.2.1.trans (appendUnselected_selected _ _)
  · have heq : ((t.1 * t.2) * (q₀ :: q₁ :: q₂ :: ds).prod) * s =
        fullModulus t k := by
      rw [hkprod]
      simp only [fullModulus, P5OriginalU5PlateauPrimeBV.markedProduct]
      ac_rfl
    simpa only [heq] using hsmall.2.2.2.1
  · rw [hkprod]
    exact hsmall.2.2.2.2

/-- The actual nonzero rho supplies the witness. On its genuinely fresh
fifth branch, all complete square conclusions follow without an incoming
support, cap-identity or small-budget licence. The finite action predicate
is visible; short/inherited branches are not declared paid. -/
theorem native_U5_nonzero_fresh_fifth_supply
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hbuffer : 0 ≤ buffer)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    (halloc : attachmentNu * epsilon ≤ (buffer : ℝ))
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {k : ℕ}
    (hk : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0) :
    ∃ s ∈ actualSmallRosserSupport N (Nat.ceil (cutoff N)) (smallCutoff N epsilon),
      ∃ chosen : List ℕ,
        chosen <+ roughPrimeUniverse N (Nat.ceil (cutoff N))
          (smallCutoff N epsilon) (cutoff N) ∧ k = s * chosen.prod ∧
        ∀ (q₀ q₁ q₂ : ℕ) (ds : List ℕ), chosen = q₀ :: q₁ :: q₂ :: ds →
          ∀ branch : SelectedBranchData, FreshFifth R bank buffer N t q₀ q₁ q₂ branch →
            SignedFifthSupply R bank buffer epsilon N t k s q₀ q₁ q₂ ds branch := by
  obtain ⟨s, hs, r, _hr, chosen, hsub, hprod, hkprod, haccept⟩ :=
    native_U5_nonzero_word R bank buffer epsilon N t hk
  have hkword : k = s * chosen.prod := by simpa only [hprod] using hkprod
  refine ⟨s, hs, chosen, hsub, hkword, ?_⟩
  intro q₀ q₁ q₂ ds hchosen branch hfresh
  subst chosen
  exact actual_U5_fresh_fifth_signed_supply R bank buffer hbuffer
    epsilon hepsilon hepsilon8 hgrid halloc hN ht hk hs q₀ q₁ q₂ ds
    hkword hsub haccept branch hfresh

end
end ImbalancedChen.P3OriginalU5FreshFifthSquareSupplier
