import ImbalancedChen.P2OriginalSelectedPairNativeData

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual pair-receiver fifth SourceForm -> actual computed warm fifth cap
-> accepted rough suffix -> both gate systems and the once-buffer native
small-level budget. The previous batch's scalar hcap is eliminated.
The remaining freshCheck consists of pre-arithmetic primitive finite
parent/candidate/arrival inequalities, not a desired rough modulus bound.
-/
namespace ImbalancedChen.P2OriginalPairFifthOnceBufferedSupport
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank SelectedBranchData)
open P2OriginalLowerNestedBufferedStages (prefixCode_nested)
open P2OriginalSelectedIntegerPrefixSquares P2OriginalSelectedNativeSmallExtension
open P2OriginalPostFifthRoughSquares
open P2OriginalPairSourceReceiver

theorem rowCap_double_buffer (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (buffer : ℚ) (branch : SelectedBranchData) :
    (rowCap R code (2*buffer) branch : ℝ) + (buffer : ℝ) =
      (rowCap R code buffer branch : ℝ) := by
  simp only [rowCap, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  ring

/-- One actual fresh selected fifth branch; no assumed row-to-Trace
    equality, descendant support, or final product budget remains. -/
theorem actual_pair_fifth_once_buffered (R : PairRange) {N mesh : ℕ}
    (hN : 1 < (N : ℝ)) (bank : CandidateBank mesh) (buffer : ℚ)
    (hbuffer : 0 ≤ buffer) (seed : ℝ) (primes : Fin 5 → ℕ)
    (hprime : ∀ i, (primes i).Prime)
    (hx : ∀ i, coordinate N (primes i) ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (branch : SelectedBranchData)
    (hsel : select R bank (2*buffer) 5 (prefixCode 5
      (codeAt R mesh 5 [coordinate N (primes 0), coordinate N (primes 1),
        coordinate N (primes 2), coordinate N (primes 3), coordinate N (primes 4)])) = some branch)
    (hcheck : freshCheck R 5 (prefixCode 5
      (codeAt R mesh 5 [coordinate N (primes 0), coordinate N (primes 1),
        coordinate N (primes 2), coordinate N (primes 3), coordinate N (primes 4)]))
      (2*buffer) (cap4 R bank (2*buffer) seed
        (codeAt R mesh 5 [coordinate N (primes 0), coordinate N (primes 1),
          coordinate N (primes 2), coordinate N (primes 3), coordinate N (primes 4)])) branch)
    (ds : List ℕ) (hdsPrime : ∀ p ∈ ds, p.Prime) (hdsSort : ds.Pairwise (· ≥ ·))
    (haccept :
      let P := pairPlan R bank (2*buffer) seed
      let H5 := run P (R.epsilon : ℝ) (ceiling : ℝ)
        (P2OriginalPairRootRoughProducer.pairRoot N (primes 1,primes 0) seed)
        [coordinate N (primes 2), coordinate N (primes 3), coordinate N (primes 4)]
      (run P (R.epsilon : ℝ) (ceiling : ℝ) H5 (ds.map (coordinate N))).accepted = true)
    (L : ℝ) (hL : L ≤ (N : ℝ)^(buffer : ℝ)) :
    let code := prefixCode 5
      (codeAt R mesh 5 [coordinate N (primes 0), coordinate N (primes 1),
        coordinate N (primes 2), coordinate N (primes 3), coordinate N (primes 4)])
    let old := integerPrefixSlots 5 code branch.form.supportMask primes
    let rough := appendUnselected old ds
    let physical := (rowCap R code buffer branch : ℝ)
    sourceCheck R 5 code (2*buffer) branch ∧
      IntegerSquareGates N physical 1 (rough.map Prod.fst) ∧
      IntegerSquareGates N physical (selectedPrimes rough).prod (remainingPrimes rough) ∧
      selectedPrimes rough = selectedPrimes old ∧
      ((rough.map Prod.fst).prod : ℝ) * L < (N : ℝ)^physical := by
  let x := fun i => coordinate N (primes i)
  let fullCode := codeAt R mesh 5 [x 0,x 1,x 2,x 3,x 4]
  let code := prefixCode 5 fullCode
  let P := pairPlan R bank (2*buffer) seed
  let H5 := run P (R.epsilon : ℝ) (ceiling : ℝ)
    (P2OriginalPairRootRoughProducer.pairRoot N (primes 1,primes 0) seed) [x 2,x 3,x 4]
  let old := integerPrefixSlots 5 code branch.form.supportMask primes
  let rough := appendUnselected old ds
  let physical := (rowCap R code buffer branch : ℝ)
  have hselFull : select R bank (2*buffer) 5 fullCode = some branch := by
    simpa only [select, prefixCode_nested 5 5 (le_refl _)] using hsel
  have hsource := (select_some_source R bank (2*buffer) 5 fullCode branch hselFull).2
  have hsourceSquares := selected_fifth_point_squares R bank (2*buffer) x hx branch hselFull
  have hcap : H5.cap = (rowCap R code (2*buffer) branch : ℝ) :=
    actual_fifth_source_cap R bank (2*buffer) seed (x 0) (x 1) (x 2) (x 3) (x 4)
      branch hsel hcheck
  have hword : H5.word = [x 0,x 1,x 2,x 3,x 4] := by
    rw [run_word]
    rfl
  have hlen : H5.word.length = 5 := by rw [hword]; rfl
  have hlog : logSlots N old = pointSlots 5 code branch.form.supportMask x := by
    rfl
  have hword' : (logSlots N old).map Slot.exponent = H5.word := by
    rw [hword]
    rfl
  have hpos : ∀ v ∈ old, 0 < v.1 := by
    have hp : ∀ i, 0 < primes i := fun i => (hprime i).pos
    simp [old,integerPrefixSlots,integerPointSlot,hp]
  have hfull : SquareGates H5.cap 0 ((logSlots N old).map Slot.exponent) := by
    rw [hcap,hlog]
    exact hsourceSquares.1
  have hselected : SquareGates H5.cap (selectedWord (logSlots N old)).sum
      (remainingWord (logSlots N old)) := by
    rw [hcap,hlog]
    exact hsourceSquares.2
  have hrough := actual_postfive_integer_gates P (R.epsilon : ℝ) (ceiling : ℝ)
    hN H5 hlen old hword' hpos hfull hselected ds hdsPrime hdsSort haccept
  have hroughPrime : ∀ p ∈ rough.map Prod.fst, 1 < p := by
    have hp : ∀ i, 1 < primes i := fun i => (hprime i).one_lt
    have hold : ∀ p ∈ old.map Prod.fst, 1 < p := by
      simp [old,integerPrefixSlots,integerPointSlot,hp]
    intro p hp'
    rw [appendUnselected_values] at hp'
    rcases List.mem_append.mp hp' with hp' | hp'
    · exact hold p hp'
    · exact (hdsPrime p hp').one_lt
  have hne : rough.map Prod.fst ≠ [] := by
    simp [rough,appendUnselected_values,old,integerPrefixSlots]
  have hprod := integerSquareGates_product_lt (rough.map Prod.fst)
    (by decide : 0 < (1 : ℕ)) hroughPrime hne hrough.1
  simp only [Nat.one_mul] at hprod
  have hshift : H5.cap + (buffer : ℝ) = physical := by
    rw [hcap]
    exact rowCap_double_buffer R code buffer branch
  have hbudget : ((rough.map Prod.fst).prod : ℝ) * L < (N : ℝ)^physical := by
    have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hN
    calc
      _ ≤ ((rough.map Prod.fst).prod : ℝ) * (N : ℝ)^(buffer : ℝ) :=
        mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
      _ < (N : ℝ)^H5.cap * (N : ℝ)^(buffer : ℝ) :=
        mul_lt_mul_of_pos_right hprod (Real.rpow_pos_of_pos hNpos _)
      _ = (N : ℝ)^physical := by rw [← Real.rpow_add hNpos,hshift]
  have hcapLe : H5.cap ≤ physical := by
    have hbR : 0 ≤ (buffer : ℝ) := by exact_mod_cast hbuffer
    linarith
  have hpower := Real.rpow_le_rpow_of_exponent_le hN.le hcapLe
  have lift {B : ℕ} (word : List ℕ) (h : IntegerSquareGates N H5.cap B word) :
      IntegerSquareGates N physical B word := by
    apply integerSquareGates_of_indexed
    intro i hi
    exact (integerSquareGates_at word h i hi).trans hpower
  exact ⟨hsource,lift _ hrough.1,lift _ hrough.2,
    appendUnselected_selected old ds,hbudget⟩

end
end ImbalancedChen.P2OriginalPairFifthOnceBufferedSupport
