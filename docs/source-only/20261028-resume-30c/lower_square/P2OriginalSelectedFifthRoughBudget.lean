import ImbalancedChen.P2OriginalPostFifthRoughSquares
import ImbalancedChen.CurrentChenP5OriginalU5CausalFinite

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Consume the actual selected SourceForm at the ACTUAL five-prime code.
The once-buffered physical cap and twice-buffered rough trace cap are
computed from the same stored affine row, not supplied modulus bounds.
Actual post-five acceptance produces the rough square gates and then the
small-level budget. The remaining scalar hL only allocates a compiler
buffer before arithmetic; it is not an equivalent rough support licence.
-/
namespace ImbalancedChen.P2OriginalSelectedFifthRoughBudget
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2EnhancedLowerPhysicalNode
open P2OriginalSelectedIntegerPrefixSquares P2OriginalSelectedNativeSmallExtension
open P2OriginalPostFifthRoughSquares
open P2OriginalLowerWholeBoxBranchSelect P2OriginalLowerCompactStartCapConstructor
open P2OriginalSelectedMaskPhysicalSquares P2OriginalCompactPhysicalGateTransfer

/-- Literal scalar row cap as stored in the finite compiler. -/
def scalarCap (S : CompactStart) {mesh : ℕ} (code : Code mesh) (buffer : ℚ)
    (data : P2OriginalLowerBufferedAffineBoxes.BranchData) : ℝ :=
  (P2OriginalLowerBufferedAffineBoxes.wholeBoxInfimum data.1 data.2.1
    (P2OriginalLowerCompactStartCapConstructor.boxOfCode S code) - buffer : ℚ)

theorem scalarCap_branch (S : CompactStart) {mesh : ℕ} (code : Code mesh)
    (buffer : ℚ) (branch : SelectedBranchData) :
    scalarCap S code buffer branch.asBranchData =
      (bufferedCap S code buffer branch : ℝ) := rfl

private theorem integerSquareGates_mono {N B : ℕ} {cap cap' : ℝ}
    (word : List ℕ) (hpower : (N : ℝ)^cap ≤ (N : ℝ)^cap')
    (hgates : IntegerSquareGates N cap B word) :
    IntegerSquareGates N cap' B word := by
  apply integerSquareGates_of_indexed
  intro i hi
  exact (integerSquareGates_at word hgates i hi).trans hpower

/-- The manuscript's existing U5 small level fits a compiler reserve
    by an exponent allocation BEFORE any integer row is inspected. -/
theorem original_U5_small_level_fits_buffer {N : ℕ} (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (buffer : ℚ)
    (hallocate : P5OriginalU5CausalFinite.attachmentNu * epsilon ≤ (buffer : ℝ)) :
    P5OriginalU5CausalFinite.smallLevel N epsilon ≤ (N : ℝ)^(buffer : ℝ) := by
  exact Real.rpow_le_rpow_of_exponent_le hN.le hallocate

/-- The exact native U5 small cutoff also pays the beta-minus head test. -/
theorem original_U5_small_head {N : ℕ} (hN : 1 < (N : ℝ))
    {epsilon : ℝ} (heps : 0 ≤ epsilon) (heps8 : epsilon ≤ 1/8) :
    (P5OriginalU5CausalFinite.smallCutoff N epsilon)^2 ≤
      P5OriginalU5CausalFinite.smallLevel N epsilon := by
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hN
  have hexp : 2 * (P5OriginalU5CausalFinite.attachmentNu * epsilon^2) ≤
      P5OriginalU5CausalFinite.attachmentNu * epsilon := by
    have hquad : 2*epsilon^2 ≤ epsilon := by nlinarith
    have hnu : 0 ≤ P5OriginalU5CausalFinite.attachmentNu := by
      norm_num [P5OriginalU5CausalFinite.attachmentNu]
    nlinarith
  change ((N : ℝ)^(P5OriginalU5CausalFinite.attachmentNu * epsilon^2))^2 ≤
    (N : ℝ)^(P5OriginalU5CausalFinite.attachmentNu * epsilon)
  have heq : ((N : ℝ)^(P5OriginalU5CausalFinite.attachmentNu * epsilon^2))^2 =
      (N : ℝ)^(2 * (P5OriginalU5CausalFinite.attachmentNu * epsilon^2)) := by
    rw [mul_comm (2 : ℝ), Real.rpow_mul hNpos.le]
    norm_num
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le hN.le hexp

/-- Real branch provenance, real frozen trace cap, actual accepted
    descendants: both gate systems and the physical residual budget are
    outputs. The exact row-to-Trace cap identity is still an explicit
    integration input; no final rough modulus bound is assumed. -/
theorem selected_fifth_actual_rough_budget (S : CompactStart)
    {N mesh depth : ℕ} (hN : 1 < (N : ℝ))
    (bank : CandidateBank mesh) (buffer : ℚ) (hbuffer : 0 ≤ buffer)
    (primes : Fin 5 → ℕ) (hprime : ∀ i, (primes i).Prime)
    (hx : ∀ i, coordinate N (primes i) ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ))
    (data : P2OriginalLowerBufferedAffineBoxes.BranchData)
    (hsel : select S bank (2*buffer) 5
      (prefixCode 5 (actualCode S mesh (fun i => coordinate N (primes i)))) = some data)
    (P : CapPlan depth mesh) (a b : ℝ) (H : Trace)
    (hword : H.word = [coordinate N (primes 0), coordinate N (primes 1),
      coordinate N (primes 2), coordinate N (primes 3), coordinate N (primes 4)])
    (hcap : H.cap = scalarCap S
      (prefixCode 5 (actualCode S mesh (fun i => coordinate N (primes i))))
      (2*buffer) data)
    (ds : List ℕ) (hdsPrime : ∀ p ∈ ds, p.Prime) (hdsSort : ds.Pairwise (· ≥ ·))
    (haccept : (run P a b H (ds.map (coordinate N))).accepted = true)
    (L : ℝ) (hL : L ≤ (N : ℝ)^(buffer : ℝ)) :
    ∃ branch ∈ bank.alternatives 5
        (prefixCode 5 (actualCode S mesh (fun i => coordinate N (primes i)))),
      supportCheck S 5
        (prefixCode 5 (actualCode S mesh (fun i => coordinate N (primes i))))
        (2*buffer) branch ∧ data = branch.asBranchData ∧
      let code := prefixCode 5 (actualCode S mesh (fun i => coordinate N (primes i)))
      let old := integerPrefixSlots 5 code branch.form.supportMask primes
      let rough := appendUnselected old ds
      let physical := scalarCap S code buffer data
      IntegerSquareGates N physical 1 (rough.map Prod.fst) ∧
        IntegerSquareGates N physical (selectedPrimes rough).prod (remainingPrimes rough) ∧
        selectedPrimes rough = selectedPrimes old ∧
        ((rough.map Prod.fst).prod : ℝ) * L < (N : ℝ)^physical := by
  obtain ⟨branch, hb, hcheck, hdata, hsquares⟩ :=
    selected_source_actual_square_gates S bank (2*buffer) 5
      (fun i => coordinate N (primes i)) hx data hsel
  refine ⟨branch, hb, hcheck, hdata, ?_⟩
  let code := prefixCode 5 (actualCode S mesh (fun i => coordinate N (primes i)))
  let old := integerPrefixSlots 5 code branch.form.supportMask primes
  let rough := appendUnselected old ds
  let physical := scalarCap S code buffer data
  have hcapBranch : H.cap = (bufferedCap S code (2*buffer) branch : ℝ) := by
    rw [hcap, hdata]
    exact scalarCap_branch S code (2*buffer) branch
  have hphysical : physical = (bufferedCap S code buffer branch : ℝ) := by
    dsimp [physical]
    rw [hdata]
    exact scalarCap_branch S code buffer branch
  have hlog : logSlots N old = pointPrefixSlots S 5 code branch.form.supportMask
      (fun i => coordinate N (primes i)) :=
    log_integerPrefixSlots N S 5 code branch.form.supportMask primes
  have hword' : (logSlots N old).map Slot.exponent = H.word := by
    rw [hword]
    simp [old, logSlots, integerPrefixSlots, integerPointSlot]
  have hlen : H.word.length = 5 := by rw [hword]; rfl
  have hpos : ∀ v ∈ old, 0 < v.1 := by
    have hp : ∀ i, 0 < primes i := fun i => (hprime i).pos
    simp [old, integerPrefixSlots, integerPointSlot, hp]
  have hfull : SquareGates H.cap 0 ((logSlots N old).map Slot.exponent) := by
    rw [hcapBranch, hlog]
    exact hsquares.1
  have hselected : SquareGates H.cap (selectedWord (logSlots N old)).sum
      (remainingWord (logSlots N old)) := by
    rw [hcapBranch, hlog]
    exact hsquares.2
  have hrough := actual_postfive_integer_gates P a b hN H hlen old hword' hpos
    hfull hselected ds hdsPrime hdsSort haccept
  have hroughPrime : ∀ p ∈ rough.map Prod.fst, 1 < p := by
    have hp : ∀ i, 1 < primes i := fun i => (hprime i).one_lt
    have hold : ∀ p ∈ old.map Prod.fst, 1 < p := by
      simp [old, integerPrefixSlots, integerPointSlot, hp]
    intro p hp'
    rw [appendUnselected_values] at hp'
    rcases List.mem_append.mp hp' with hp' | hp'
    · exact hold p hp'
    · exact (hdsPrime p hp').one_lt
  have hroughNe : rough.map Prod.fst ≠ [] := by
    simp [rough, appendUnselected_values, old, integerPrefixSlots]
  have hcontract : IntegerSquareGates N
      (bufferedCap S code (2*buffer) branch : ℝ) 1 (rough.map Prod.fst) := by
    rw [← hcapBranch]
    exact hrough.1
  have hbudget := double_buffer_residual_budget hN S code buffer branch
    (rough.map Prod.fst) hroughPrime hroughNe hcontract hL
  have hcapLe : H.cap ≤ physical := by
    have hbufR : 0 ≤ (buffer : ℝ) := by exact_mod_cast hbuffer
    rw [hcapBranch, hphysical]
    have heq := double_buffer_identity S code buffer branch
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hN.le hcapLe
  exact ⟨integerSquareGates_mono (rough.map Prod.fst) hpow hrough.1,
    integerSquareGates_mono (remainingPrimes rough) hpow hrough.2,
    appendUnselected_selected old ds, by simpa only [hphysical] using hbudget⟩

end
end ImbalancedChen.P2OriginalSelectedFifthRoughBudget
