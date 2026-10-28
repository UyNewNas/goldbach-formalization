import ImbalancedChen.P2OriginalPairNativeWEmptyMaskSupport
import ImbalancedChen.P2OriginalSelectedNativeSmallExtension

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
The SAME actual signed native coefficient supplies its small Rosser word
with the original sign. Actual accepted rough support pays a once-buffer
budget, including short/inherited words. Both EMPTY-W integer gates hold
on the COMPLETE physical modulus (external pair)*k. Neither a final
modulus bound nor a residual-support conclusion is supplied by the caller.
Full W initialization/monomials/adopted bank identity remain separate. -/
namespace ImbalancedChen.P2OriginalPairNativeOnceBufferedWSquares
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2CanonicalPairTentWarmHistory P2OriginalSelectedPairNativeData
open P2OriginalPairBufferedRootProvenance P2OriginalPairNativeWEmptyMaskSupport
open P2OriginalLowerWholeBoxBranchSelect P2OriginalSelectedIntegerPrefixSquares
open P2OriginalSelectedNativeSmallExtension P5CausalRhoFactorization

/-- Full signed native modulus, with both W-empty-mask square systems
    derived for every once-buffer auxiliary envelope above the actual cap.
    Short/inherited words are covered by the preceding all-rank supplier. -/
theorem native_complete_once_buffered_W_squares (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (hbuffer : 0 ≤ buffer) (hb : buffer ≤ 1/1000)
    (sixth : Bool) {eta : ℝ} (heta : 0 ≤ eta) (hcrop : 2*(buffer : ℝ) ≤ eta)
    (N enum : ℕ) (hN : 1 < (N : ℝ)) (p : ℕ × ℕ)
    (hp1 : p.1.Prime) (hp2 : p.2.Prime)
    (hpDomain : pairPoint N p ∈ originalPairDomain sixth eta)
    (w L : ℝ) (hhead : w^2 ≤ L) (hL : L ≤ (N : ℝ)^(buffer : ℝ)) {k : ℕ}
    (hk : actualLowerSmallRoughRho
      (pairPolicy (warmPlan R mesh (2*buffer) floor (rootSeed sixth buffer N p))
        R.epsilon ceiling (rootSeed sixth buffer N p) N p)
      N enum w ((N : ℝ)^(417/5000 : ℝ)) L k ≠ 0) :
    let seed := rootSeed sixth buffer N p
    let P := warmPlan R mesh (2*buffer) floor seed
    let policy := pairPolicy P R.epsilon ceiling seed N p
    ∃ s ∈ actualSmallRosserSupport N enum w,
      ∃ r ∈ fixedEvenRoughSupport policy N enum w ((N : ℝ)^(417/5000 : ℝ)),
        ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N enum w ((N : ℝ)^(417/5000 : ℝ)) ∧
          chosen.prod=r ∧ k=s*r ∧
          let H := run P R.epsilon ceiling (pairRoot N p seed) (chosen.map (coordinate N))
          let rough := wTagged (p.2::p.1::chosen)
          let whole := appendUnselected rough s.primeFactorsList.reverse
          H.accepted=true ∧ selectedPrimes whole=[] ∧
          (whole.map Prod.fst).prod=(p.2*p.1)*k ∧
          ∀ theta : ℝ, H.cap+(buffer : ℝ) ≤ theta → ∀ j : Fin 5,
            (SourceForm.wSlot j).supportMask=∅ ∧
            IntegerSquareGates N theta 1 (whole.map Prod.fst) ∧
            IntegerSquareGates N theta (selectedPrimes whole).prod (remainingPrimes whole) := by
  dsimp only
  let seed := rootSeed sixth buffer N p
  let P := warmPlan R mesh (2*buffer) floor seed
  let policy := pairPolicy P R.epsilon ceiling seed N p
  let z := (N : ℝ)^(417/5000 : ℝ)
  obtain ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,hvalue,hwordprod,hgates⟩ :=
    native_original_pair_W_square_input R mesh buffer floor hb sixth heta hcrop N enum hN p
      hp1 hp2 hpDomain w L hk
  let H := run P R.epsilon ceiling (pairRoot N p seed) (chosen.map (coordinate N))
  let word := p.2::p.1::chosen
  let rough := wTagged word
  let whole := appendUnselected rough s.primeFactorsList.reverse
  have hactive : (s,r) ∈ activePairs policy N enum w z L := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hs,hr⟩,?_⟩
    rw [← hvalue]
    exact hk
  have hsmall := active_pair_small_word_well policy N enum w z L hactive hhead
  have hsf := actualSmallRosserSupport_squarefree N enum w hs
  have hsprod : s.primeFactorsList.reverse.prod=s := by
    rw [List.prod_reverse,Nat.prod_primeFactorsList hsf.ne_zero]
  have hempty := w_empty_mask_words (0 : Fin 5) word
  have hselected : selectedPrimes whole=[] := by
    rw [appendUnselected_selected]
    exact hempty.2.1
  have hprodWhole : (whole.map Prod.fst).prod=(p.2*p.1)*k := by
    rw [appendUnselected_values,List.prod_append,hempty.2.2.2,hsprod]
    rw [hwordprod,hkprod]
    ring
  refine ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,hselected,hprodWhole,?_⟩
  intro theta htheta j
  have hbR : 0 ≤ (buffer : ℝ) := by exact_mod_cast hbuffer
  have hcapTheta : H.cap ≤ theta := by linarith
  have hroughTheta := hgates theta hcapTheta j
  have hroughActual := (hgates H.cap (le_refl _) j).2.1
  have hprime : ∀ q ∈ word, 1 < q := by
    intro q hq
    simp only [word,List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact hp2.one_lt
    · exact hp1.one_lt
    · exact (mem_roughPrimeUniverse_prime (hsub.subset hq)).one_lt
  have hvalues : rough.map Prod.fst=word := hempty.2.2.2
  have hfullActual : IntegerSquareGates N H.cap 1 word := by
    simpa only [hvalues] using hroughActual
  have hprodBound : (word.prod : ℝ) < (N : ℝ)^H.cap := by
    simpa only [Nat.one_mul] using integerSquareGates_product_lt word (by omega : 0<(1:ℕ))
      hprime (by simp [word]) hfullActual
  have hbudget : ((rough.map Prod.fst).prod : ℝ)*L ≤ (N : ℝ)^theta := by
    rw [hvalues]
    calc
      _ ≤ (word.prod : ℝ)*(N : ℝ)^(buffer : ℝ) :=
        mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
      _ < (N : ℝ)^H.cap*(N : ℝ)^(buffer : ℝ) :=
        mul_lt_mul_of_pos_right hprodBound (Real.rpow_pos_of_pos (zero_lt_one.trans hN) _)
      _ = (N : ℝ)^(H.cap+(buffer : ℝ)) := (Real.rpow_add (zero_lt_one.trans hN) _ _).symm
      _ ≤ (N : ℝ)^theta := Real.rpow_le_rpow_of_exponent_le hN.le htheta
  have hwhole := append_unselected_same_cap rough s.primeFactorsList.reverse
    hroughTheta.2.1 hroughTheta.2.2 hsmall hbudget
  exact ⟨hroughTheta.1,hwhole.1,hwhole.2.1⟩

end
end ImbalancedChen.P2OriginalPairNativeOnceBufferedWSquares
