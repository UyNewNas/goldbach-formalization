import ImbalancedChen.P2CanonicalWarmAllRankSquareEnvelope
import ImbalancedChen.P2OriginalPairBufferedRootProvenance

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Actual original-root canonical native words now supply ALL full squares,
including short/inherited lanes. W has the genuine EMPTY SourceForm mask;
its complement squares are the same full squares, not tent selected sums.
An auxiliary W envelope may be above the actual frozen cap WITHOUT changing
the native rho/word. This is the support input for W, not its still-missing
adopted branch identity, full greedy/monomial/PP arithmetic licence. -/
namespace ImbalancedChen.P2OriginalPairNativeWEmptyMaskSupport
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention P2LowerIntegerRetainedSupport
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2CanonicalPairTentWarmHistory P2OriginalSelectedPairNativeData
open P2OriginalPairBufferedRootProvenance P2CanonicalWarmAllRankSquareEnvelope
open P2OriginalLowerWholeBoxBranchSelect P2OriginalSelectedIntegerPrefixSquares
open P2EnhancedLowerPhysicalNode

def wTagged (word : List ℕ) : List (ℕ × Bool) := word.map (fun p => (p,false))

/-- W's empty source mask really selects no prime slots. It is not an
    artificial zero selected product inserted into a tent licence. -/
theorem w_empty_mask_words (j : Fin 5) (word : List ℕ) :
    (SourceForm.wSlot j).supportMask=∅ ∧
      selectedPrimes (wTagged word)=[] ∧ remainingPrimes (wTagged word)=word ∧
      (wTagged word).map Prod.fst=word := by
  have h : selectedPrimes (wTagged word)=[] ∧ remainingPrimes (wTagged word)=word := by
    induction word with
    | nil => exact ⟨rfl,rfl⟩
    | cons p ps ih => simpa [selectedPrimes,remainingPrimes,wTagged] using ih
  exact ⟨rfl,h.1,h.2,by simp [wTagged,List.map_map,Function.comp_def]⟩

private theorem coordinate_nonneg {N q : ℕ} (hN : 1 < (N : ℝ)) (hq : q.Prime) :
    0 ≤ coordinate N q := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hq.one_lt.le)) (Real.log_pos hN).le

private theorem coordinate_mono {N q p : ℕ} (hN : 1 < (N : ℝ))
    (hq : 0 < q) (hqp : q ≤ p) : coordinate N q ≤ coordinate N p := by
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (Nat.cast_pos.mpr hq) (by exact_mod_cast hqp)) (Real.log_pos hN).le

/-- Actual nonzero native atom -> genuine all-rank word and both EMPTY-W
    gate systems at every auxiliary envelope above its ACTUAL final cap.
    No full-word support, accepted word, fresh selection or W licence is
    assumed. The exact old native coefficient remains unchanged. -/
theorem native_original_pair_W_square_input (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (hb : buffer ≤ 1/1000) (sixth : Bool)
    {eta : ℝ} (heta : 0 ≤ eta) (hcrop : 2*(buffer : ℝ) ≤ eta)
    (N enum : ℕ) (hN : 1 < (N : ℝ)) (p : ℕ × ℕ)
    (hp1 : p.1.Prime) (hp2 : p.2.Prime)
    (hpDomain : pairPoint N p ∈ originalPairDomain sixth eta)
    (w L : ℝ) {k : ℕ}
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
          let word := p.2::p.1::chosen
          H.accepted=true ∧
          actualLowerSmallRoughRho policy N enum w ((N : ℝ)^(417/5000 : ℝ)) L k =
            P5CausalRhoFactorization.coefficient policy N enum w ((N : ℝ)^(417/5000 : ℝ)) L (s,r) ∧
          word.prod=(p.2*p.1)*r ∧
          ∀ theta : ℝ, H.cap ≤ theta → ∀ j : Fin 5,
            (SourceForm.wSlot j).supportMask=∅ ∧
            IntegerSquareGates N theta 1 ((wTagged word).map Prod.fst) ∧
            IntegerSquareGates N theta (selectedPrimes (wTagged word)).prod
              (remainingPrimes (wTagged word)) := by
  dsimp only
  let seed := rootSeed sixth buffer N p
  let P := warmPlan R mesh (2*buffer) floor seed
  obtain ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,hvalue⟩ :=
    pair_rho_nonzero_rough_word P R.epsilon ceiling seed N enum p w
      ((N : ℝ)^(417/5000 : ℝ)) L hk
  let H := run P R.epsilon ceiling (pairRoot N p seed) (chosen.map (coordinate N))
  let word := p.2::p.1::chosen
  have hroot := original_buffered_root_squares sixth buffer hb heta hcrop N p hpDomain
  have hrootSquares : SquareGates seed 0 [coordinate N p.2,coordinate N p.1] := by
    simpa [seed,SquareGates] using And.intro hroot.1.le (And.intro hroot.2.1.le True.intro)
  have hprime : ∀ q ∈ chosen, q.Prime := by
    intro q hq
    exact mem_roughPrimeUniverse_prime (hsub.subset hq)
  have hnatSort : chosen.Pairwise (· > ·) :=
    (roughPrimeUniverse_pairwise_gt N enum w ((N : ℝ)^(417/5000 : ℝ))).sublist hsub
  have hcoordSort : (chosen.map (coordinate N)).Pairwise (· ≥ ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i<chosen.length := by simpa using hi
    have hj' : j<chosen.length := by simpa using hj
    have hgt := (List.pairwise_iff_getElem.mp hnatSort) i j hi' hj' hij
    simpa only [List.getElem_map] using
      coordinate_mono hN (hprime _ (List.getElem_mem hj')).pos hgt.le
  have hcoord0 : ∀ x ∈ chosen.map (coordinate N), 0 ≤ x := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact coordinate_nonneg hN (hprime q hq)
  have hcoordHi : ∀ x ∈ chosen.map (coordinate N), x ≤ (417/5000 : ℝ) := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    have hupper := mem_roughPrimeUniverse_upper (hsub.subset hq)
    have hpow : (N : ℝ)^(coordinate N q) < (N : ℝ)^(417/5000 : ℝ) := by
      rw [coordinate_power hN (hprime q hq).pos]
      exact hupper
    exact ((Real.rpow_lt_rpow_left_iff hN).mp hpow).le
  have hfull := accepted_warm_full_squares R mesh (2*buffer) floor seed
    (coordinate N p.2) (coordinate N p.1) (417/5000) hrootSquares hroot.2.2.le
    (chosen.map (coordinate N)) hcoordSort hcoord0 hcoordHi haccept
  have hword : H.word=word.map (coordinate N) := by
    simp [H,word,run_word,pairRoot]
  have hwordPrime : ∀ q ∈ word, q.Prime := by
    intro q hq
    simp only [word,List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact hp2
    · exact hp1
    · exact hprime q hq
  refine ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,hvalue,?_,?_⟩
  · simp [word,hprod,Nat.mul_assoc]
  · intro theta htheta j
    have hcap (xs : List ℝ) {T : ℝ} (hg : SquareGates H.cap T xs) :
        SquareGates theta T xs := by
      induction xs generalizing T with
      | nil => trivial
      | cons x xs ih => exact ⟨hg.1.trans htheta,ih hg.2⟩
    have hreal : SquareGates theta 0 (word.map (coordinate N)) := by
      rw [← hword]
      exact hcap _ hfull
    have hInt := squareGates_to_integer hN word (fun q hq => (hwordPrime q hq).pos)
      (by simp : (N : ℝ)^(0 : ℝ)=(1 : ℝ)) hreal
    obtain ⟨hempty,hselected,hremaining,hvalues⟩ := w_empty_mask_words j word
    exact ⟨hempty,by simpa only [hvalues] using hInt,
      by simpa only [hselected,hremaining,List.prod_nil] using hInt⟩

end
end ImbalancedChen.P2OriginalPairNativeWEmptyMaskSupport
