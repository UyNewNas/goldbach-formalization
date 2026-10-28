import ImbalancedChen.P2OriginalPairSourceReceiver
import ImbalancedChen.P5JointNativeSignedRegroup
import ImbalancedChen.CurrentChenP5CausalPrimeCorrectionPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Explicit native L5/L6 receiver instances. Root levels are the original
piecewise U5/U6 formulas, not the ordinary nu baseline. The L6 native data
retain the original small cutoff/level functions and the same outer E
carrier. Only the now-computed finite pair continuation policy is supplied.
This constructs a candidate native instance; global bank adoption/coverage,
W arithmetic licensing and analytic density/distribution are not inferred.
-/
namespace ImbalancedChen.P2OriginalSelectedPairNativeData
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P5CausalRhoFactorization P5JointNativeSignedRegroup

def rootLevel (sixth : Bool) (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  if sixth then P5U6CausalLevelGeometry.physicalLevel (coordinate N p.1) (coordinate N p.2)
  else Part5OriginalUpsilon5CausalDictionary.level (coordinate N p.1) (coordinate N p.2)

def rootSeed (sixth : Bool) (buffer : ℚ) (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  rootLevel sixth N p - 2*(buffer : ℝ)

theorem original_root_seed_bounded (sixth : Bool) (buffer : ℚ) (hb : 0 ≤ buffer)
    (N : ℕ) (p : ℕ × ℕ) : rootSeed sixth buffer N p ≤ (153/256 : ℝ) := by
  have hbR : 0 ≤ (buffer : ℝ) := by exact_mod_cast hb
  cases sixth with
  | false =>
      have h := P5CausalPrimeCorrectionPayment.original_U5_level_le_cap
        (![coordinate N p.1, coordinate N p.2] : Fin 2 → ℝ)
      dsimp [rootSeed,rootLevel]
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h
      linarith
  | true =>
      have h := P5CausalPrimeCorrectionPayment.original_U6_level_le_cap
        (![coordinate N p.1, coordinate N p.2] : Fin 2 → ℝ)
      dsimp [rootSeed,rootLevel]
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h
      linarith

def selectedPolicy (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (sixth : Bool) (N : ℕ) (p : ℕ × ℕ) : List ℕ → Bool :=
  pairPolicy (pairPlan R bank (2*buffer) (rootSeed sixth buffer N p))
    (R.epsilon : ℝ) (ceiling : ℝ) (rootSeed sixth buffer N p) N p

/-- The native U6 interface is instantiated, rather than assuming its
    arbitrary old policy equal to the new one. Original w/L stay literal. -/
def selectedLowerData (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (N : ℕ) (original : LowerData) : LowerData where
  policy := selectedPolicy R bank buffer true N
  w := original.w
  L := original.L

@[simp] theorem selectedLowerData_w (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (N : ℕ) (original : LowerData)
    (p : ℕ × ℕ) : (selectedLowerData R bank buffer N original).w p = original.w p := rfl

@[simp] theorem selectedLowerData_L (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (N : ℕ) (original : LowerData)
    (p : ℕ × ℕ) : (selectedLowerData R bank buffer N original).L p = original.L p := rfl

/-- Literal production L5 rho now yields actual rough words for this
    original-level finite receiver, without a policy-equality hypothesis. -/
theorem native_U5_nonzero_word (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (epsilon : ℝ) (N : ℕ) (p : ℕ × ℕ) {k : ℕ}
    (hk : P5OriginalU5CausalFinite.rho N epsilon
      (selectedPolicy R bank buffer false N p) k ≠ 0) :
    ∃ s ∈ actualSmallRosserSupport N (Nat.ceil (P5OriginalU5CausalFinite.cutoff N))
        (P5OriginalU5CausalFinite.smallCutoff N epsilon),
      ∃ r ∈ fixedEvenRoughSupport (selectedPolicy R bank buffer false N p)
          N (Nat.ceil (P5OriginalU5CausalFinite.cutoff N))
          (P5OriginalU5CausalFinite.smallCutoff N epsilon) (P5OriginalU5CausalFinite.cutoff N),
        ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N
            (Nat.ceil (P5OriginalU5CausalFinite.cutoff N))
            (P5OriginalU5CausalFinite.smallCutoff N epsilon) (P5OriginalU5CausalFinite.cutoff N) ∧
          chosen.prod = r ∧ k = s*r ∧
          (run (pairPlan R bank (2*buffer) (rootSeed false buffer N p))
            (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N p (rootSeed false buffer N p))
            (chosen.map (coordinate N))).accepted = true := by
  have h := pair_rho_nonzero_rough_word
    (pairPlan R bank (2*buffer) (rootSeed false buffer N p))
    (R.epsilon : ℝ) (ceiling : ℝ) (rootSeed false buffer N p)
    N (Nat.ceil (P5OriginalU5CausalFinite.cutoff N)) p
    (P5OriginalU5CausalFinite.smallCutoff N epsilon) (P5OriginalU5CausalFinite.cutoff N)
    (P5OriginalU5CausalFinite.smallLevel N epsilon) hk
  obtain ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,_⟩ := h
  exact ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept⟩

/-- Literal native L6 marked rows keep the SAME complement of E; the
    nonzero coefficient supplies its actual chosen rough word internally. -/
theorem native_U6_mark_nonzero_word (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (N : ℕ) (original : LowerData)
    (E : ℕ × ℕ → Prop) (m : LowerMark)
    (hm : m ∈ lowerMarks (selectedLowerData R bank buffer N original) N E)
    (hk : lowerRho (selectedLowerData R bank buffer N original) N m.1 m.2 ≠ 0) :
    m.1 ∈ P5SelectedMaskTransport.sixthSupport N ∧ ¬ E m.1 ∧
      ∃ s ∈ actualSmallRosserSupport N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
          (original.w m.1),
        ∃ r ∈ fixedEvenRoughSupport (selectedPolicy R bank buffer true N m.1)
            N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
            (original.w m.1) (P5CausalRhoQuotientBridge.cutoff N),
          ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N
              (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
              (original.w m.1) (P5CausalRhoQuotientBridge.cutoff N) ∧
            chosen.prod = r ∧ m.2 = s*r ∧
            (run (pairPlan R bank (2*buffer) (rootSeed true buffer N m.1))
              (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N m.1 (rootSeed true buffer N m.1))
              (chosen.map (coordinate N))).accepted = true := by
  have hrow := (Finset.mem_sigma.mp hm).1
  have hret : m.1 ∈ P5SelectedMaskTransport.sixthSupport N ∧ ¬ E m.1 :=
    Finset.mem_filter.mp hrow
  have h := pair_rho_nonzero_rough_word
    (pairPlan R bank (2*buffer) (rootSeed true buffer N m.1))
    (R.epsilon : ℝ) (ceiling : ℝ) (rootSeed true buffer N m.1)
    N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) m.1
    (original.w m.1) (P5CausalRhoQuotientBridge.cutoff N) (original.L m.1) hk
  obtain ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,_⟩ := h
  exact ⟨hret.1,hret.2,s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept⟩

end
end ImbalancedChen.P2OriginalSelectedPairNativeData
