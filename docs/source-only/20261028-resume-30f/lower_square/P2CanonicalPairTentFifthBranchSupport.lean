import ImbalancedChen.P2OriginalPairBufferedRootProvenance
import ImbalancedChen.P2OriginalPairFifthOnceBufferedSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual canonical TENT-SUBBANK fifth action: computed inherit, or computed
fresh source -> once-buffer full/selected-complement gates and residual
budget. There is no successful source selection/fresh-check hypothesis.
The inherited lane is retained exactly, not relabelled as a fresh source.
Nonzero native coefficients independently supply actual warm carrier words;
short atoms are not forced through a fifth-source theorem.
-/
namespace ImbalancedChen.P2CanonicalPairTentFifthBranchSupport
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerNestedBufferedStages (prefixCode_nested)
open P2OriginalFiniteTentBankSelectorMargins (tentMasks)
open P2OriginalSelectedIntegerPrefixSquares P2OriginalSelectedNativeSmallExtension
open P2CanonicalPairTentWarmHistory P2OriginalSelectedPairNativeData
open P2OriginalPairFifthOnceBufferedSupport P2OriginalPostFifthRoughSquares

/-- The actual fifth decision itself supplies the complete fresh branch
    licence. The other case inherits its actual fourth cap; no final gate
    or arithmetic-licence conclusion is placed among the hypotheses. -/
theorem canonical_fifth_cases_once_buffered (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (hbuffer : 0 ≤ buffer) (seed : ℝ)
    {N : ℕ} (hN : 1 < (N : ℝ)) (primes : Fin 5 → ℕ)
    (hprime : ∀ i, (primes i).Prime)
    (hx : ∀ i, coordinate N (primes i) ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (ds : List ℕ) (hdsPrime : ∀ p ∈ ds, p.Prime) (hdsSort : ds.Pairwise (· ≥ ·))
    (haccept :
      let P := warmPlan R mesh (2*buffer) floor seed
      let H5 := run P R.epsilon ceiling (pairRoot N (primes 1,primes 0) seed)
        [coordinate N (primes 2),coordinate N (primes 3),coordinate N (primes 4)]
      (run P R.epsilon ceiling H5 (ds.map (coordinate N))).accepted = true)
    (L : ℝ) (hL : L ≤ (N : ℝ)^(buffer : ℝ)) :
    let B := P2OriginalCanonicalPairTentBank.bank R mesh (2*buffer) floor
    let P := warmPlan R mesh (2*buffer) floor seed
    let fullCode := codeAt R mesh 5 [coordinate N (primes 0),coordinate N (primes 1),
      coordinate N (primes 2),coordinate N (primes 3),coordinate N (primes 4)]
    let code := prefixCode 5 fullCode
    let H5 := run P R.epsilon ceiling (pairRoot N (primes 1,primes 0) seed)
      [coordinate N (primes 2),coordinate N (primes 3),coordinate N (primes 4)]
    (P.choose 5 fullCode = .inherit 2 ∧ H5.cap = cap4 R B (2*buffer) seed fullCode) ∨
    ∃ b mask, mask ∈ tentMasks 5 ∧ b.form.supportMask = mask ∧
      (b.form = .tentLeft mask ∨ b.form = .tentRight mask) ∧
      P.choose 5 fullCode = .fresh (rowCap R code (2*buffer) b) b.argument ∧
      H5.cap = (rowCap R code (2*buffer) b : ℝ) ∧
      sourceCheck R 5 code (2*buffer) b ∧
      let old := integerPrefixSlots 5 code b.form.supportMask primes
      let rough := appendUnselected old ds
      let physical := (rowCap R code buffer b : ℝ)
      physical = H5.cap+(buffer : ℝ) ∧
      IntegerSquareGates N physical 1 (rough.map Prod.fst) ∧
      IntegerSquareGates N physical (selectedPrimes rough).prod (remainingPrimes rough) ∧
      selectedPrimes rough = selectedPrimes old ∧
      ((rough.map Prod.fst).prod : ℝ)*L < (N : ℝ)^physical := by
  dsimp only
  let B := P2OriginalCanonicalPairTentBank.bank R mesh (2*buffer) floor
  let P := warmPlan R mesh (2*buffer) floor seed
  let x := fun i => coordinate N (primes i)
  let fullCode := codeAt R mesh 5 [x 0,x 1,x 2,x 3,x 4]
  let code := prefixCode 5 fullCode
  let H5 := run P R.epsilon ceiling (pairRoot N (primes 1,primes 0) seed) [x 2,x 3,x 4]
  have hcap : H5.cap = cap5 R B (2*buffer) seed fullCode :=
    pair_run_three_cap R B (2*buffer) seed (x 0) (x 1) (x 2) (x 3) (x 4)
  have hchoice : P.choose 5 fullCode =
      checkedChoice R B (2*buffer) 5 (cap4 R B (2*buffer) seed fullCode) fullCode := rfl
  rcases checked_choice_cases R mesh (2*buffer) floor 5
      (cap4 R B (2*buffer) seed fullCode) fullCode with hi | hf
  · refine Or.inl ⟨hchoice.trans hi.1,?_⟩
    rw [hcap]
    exact hi.2.1
  · obtain ⟨b,mask,hm,hsel,hside,hsource,hmask,hform,hcheck,hfresh,hfreeze⟩ := hf
    have hselPrefix : select R B (2*buffer) 5 code = some b := by
      simpa only [select,prefixCode_nested 5 5 (le_refl _)] using hsel
    have hcapSource : H5.cap = (rowCap R code (2*buffer) b : ℝ) := by
      rw [hcap]
      exact hfreeze
    have hsupport := actual_pair_fifth_once_buffered R hN B buffer hbuffer seed
      primes hprime hx b hselPrefix hcheck ds hdsPrime hdsSort haccept L hL
    refine Or.inr ⟨b,mask,hm,hmask,hform,hchoice.trans hfresh,hcapSource,hsupport.1,?_⟩
    refine ⟨?_,hsupport.2.1,hsupport.2.2.1,hsupport.2.2.2.1,hsupport.2.2.2.2⟩
    rw [hcapSource]
    exact (rowCap_double_buffer R code buffer b).symm

/-- Genuine nonzero native coefficient for this original-root tent
    subfamily recovers its actual word, coefficient value and full causal
    acceptance. Long words reach a real fifth state; short words remain
    explicitly short. No arbitrary original.policy replacement is used. -/
theorem native_tent_word_history (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (sixth : Bool) (N enum : ℕ) (p : ℕ × ℕ) (w z L : ℝ) {k : ℕ}
    (hk : actualLowerSmallRoughRho
      (pairPolicy (warmPlan R mesh (2*buffer) floor (rootSeed sixth buffer N p))
        R.epsilon ceiling (rootSeed sixth buffer N p) N p) N enum w z L k ≠ 0) :
    let seed := rootSeed sixth buffer N p
    let P := warmPlan R mesh (2*buffer) floor seed
    let policy := pairPolicy P R.epsilon ceiling seed N p
    ∃ s ∈ actualSmallRosserSupport N enum w,
      ∃ r ∈ fixedEvenRoughSupport policy N enum w z,
        ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N enum w z ∧
          chosen.prod=r ∧ k=s*r ∧
          (run P R.epsilon ceiling (pairRoot N p seed)
            (chosen.map (coordinate N))).accepted=true ∧
          actualLowerSmallRoughRho policy N enum w z L k =
            P5CausalRhoFactorization.coefficient policy N enum w z L (s,r) ∧
          ((chosen.length<3) ∨
            let H5 := run P R.epsilon ceiling (pairRoot N p seed)
              ((chosen.take 3).map (coordinate N))
            3≤chosen.length ∧ H5.word.length=5 ∧
              (run P R.epsilon ceiling H5 ((chosen.drop 3).map (coordinate N))).accepted=true ∧
              (run P R.epsilon ceiling H5 ((chosen.drop 3).map (coordinate N))).cap=H5.cap) := by
  dsimp only
  let seed := rootSeed sixth buffer N p
  let P := warmPlan R mesh (2*buffer) floor seed
  obtain ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,hvalue⟩ :=
    pair_rho_nonzero_rough_word P R.epsilon ceiling seed N enum p w z L hk
  refine ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,hvalue,?_⟩
  by_cases hshort : chosen.length<3
  · exact Or.inl hshort
  · have hlong : 3≤chosen.length := by omega
    let H5 := run P R.epsilon ceiling (pairRoot N p seed)
      ((chosen.take 3).map (coordinate N))
    have hlen : H5.word.length=5 := by
      rw [run_word]
      simp [pairRoot,List.length_take,Nat.min_eq_left hlong]
    have hsplit : chosen.map (coordinate N) =
        (chosen.take 3).map (coordinate N) ++ (chosen.drop 3).map (coordinate N) := by
      rw [← List.map_append,List.take_append_drop]
    have htail : (run P R.epsilon ceiling H5
        ((chosen.drop 3).map (coordinate N))).accepted=true := by
      simpa only [hsplit,run_append] using haccept
    exact Or.inr ⟨hlong,hlen,htail,
      run_cap_after_five P R.epsilon ceiling H5 (by omega) _⟩

end
end ImbalancedChen.P2CanonicalPairTentFifthBranchSupport
