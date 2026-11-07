import ImbalancedChen.P2CanonicalPairTentFifthBranchSupport
import ImbalancedChen.P2OriginalTentSquarePerturbation
import ImbalancedChen.P2OriginalCanonicalTentCriticalLicence
import ImbalancedChen.P2OriginalCanonicalTentFrozenChambers

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Computed canonical fresh action -> its actual source form/mask, physical
point full/selected squares, and ORIGINAL selected-subproduct critical
interval at the SAME once-buffer cap. The total prefix is never replaced
by the selected sum; selectedMid is not used as a residual H/h query.
This proves a tent-source parameter licence, not full W/adopted coverage,
PP distribution, the query graph or the final lower estimate.
-/
namespace ImbalancedChen.P2CanonicalPairTentActualSourceLicence
noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerSelectedCapConstructor (Code prefixCode strictSquareGates)
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalFiniteTentBankSelectorMargins (tentMasks)
open P2EnhancedLowerPhysicalNode P2CanonicalPairTentWarmHistory
open P2OriginalPairFifthOnceBufferedSupport
open P2OriginalTentSquarePerturbation P2OriginalCanonicalTentCriticalLicence
open P2OriginalCanonicalTentFrozenChambers

/-- Read the actual computed choice; sourceCheck and the original critical
    interval are CONCLUSIONS, not pre-supplied arithmetic licences. -/
theorem computed_fresh_point_and_critical (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (hbuffer : 0 < buffer) (rank : Fin 6)
    (parent : ℝ) (code : Code mesh) (q argument : ℝ)
    (hchoice : checkedChoice R
      (P2OriginalCanonicalPairTentBank.bank R mesh (2*buffer) floor)
      (2*buffer) rank parent code = .fresh q argument)
    (x : Fin 5 → ℝ) (hx : inBox (box R (prefixCode rank.val code)) x)
    (kappa : ℝ) (hkappa : kappa ≤ (buffer : ℝ)) :
    ∃ b mask, mask ∈ tentMasks rank ∧
      select R (P2OriginalCanonicalPairTentBank.bank R mesh (2*buffer) floor)
        (2*buffer) rank code = some b ∧ b.form.supportMask = mask ∧
      (b.form = .tentLeft mask ∨ b.form = .tentRight mask) ∧
      q = (rowCap R (prefixCode rank.val code) (2*buffer) b : ℝ) ∧
      sourceCheck R rank (prefixCode rank.val code) (2*buffer) b ∧
      let pts := pointSlots rank (prefixCode rank.val code) mask x
      strictSquareGates q 0 (pts.map Slot.exponent) ∧
      strictSquareGates q (selectedWord pts).sum (remainingWord pts) ∧
      (q+(buffer : ℝ))+(buffer : ℝ)/2 ≤
        actualSelectedSubproductV (1+3*kappa) (∑ i ∈ mask, x i) ∧
      2*(q+(buffer : ℝ))-1 ≤ (∑ i ∈ mask, x i) ∧
      (∑ i ∈ mask, x i) ≤ actualSelectedSubproductUpper (1+3*kappa) (q+(buffer : ℝ)) := by
  rcases checked_choice_cases R mesh (2*buffer) floor rank parent code with hi | hf
  · rw [hi.1] at hchoice
    cases hchoice
  · obtain ⟨b,mask,hm,hsel,hside,hsource,hmask,hform,hcheck,hfresh,hfreeze⟩ := hf
    have heq := hfresh.symm.trans hchoice
    injection heq with hq harg
    have hsquares := sourceCheck_point_squares R (prefixCode rank.val code) rank
      (2*buffer) b x hx hsource
    rw [hq,hmask] at hsquares
    have hcritical := actual_moving_residue_critical_interval R
      (prefixCode rank.val code) mask b hside x hx buffer hbuffer kappa hkappa
    have hphysical : (rowCap R (prefixCode rank.val code) buffer b : ℝ) =
        q+(buffer : ℝ) := by
      rw [← hq]
      exact (rowCap_double_buffer R (prefixCode rank.val code) buffer b).symm
    rw [hphysical] at hcritical
    exact ⟨b,mask,hm,hsel,hmask,hform,hq.symm,hsource,
      hsquares.1,hsquares.2,hcritical.1,hcritical.2.1,hcritical.2.2⟩

/-- Actual codeAt prefix and physical coordinates discharge the box port.
    Padded future slots do not enter the selected sum: actual SourceForm
    eligibility has already proved every selected label appeared. -/
theorem actual_prefix_fresh_source_licence (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (hbuffer : 0 < buffer) (rank : Fin 6)
    (parent : ℝ) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ)) (q argument : ℝ)
    (hchoice : checkedChoice R
      (P2OriginalCanonicalPairTentBank.bank R mesh (2*buffer) floor)
      (2*buffer) rank parent (actualCode R mesh rank x) = .fresh q argument)
    (kappa : ℝ) (hkappa : kappa ≤ (buffer : ℝ)) :
    ∃ b mask, mask ∈ tentMasks rank ∧ b.form.supportMask = mask ∧
      (b.form = .tentLeft mask ∨ b.form = .tentRight mask) ∧
      q = (rowCap R (actualCode R mesh rank x) (2*buffer) b : ℝ) ∧
      sourceCheck R rank (actualCode R mesh rank x) (2*buffer) b ∧
      let pts := pointSlots rank (actualCode R mesh rank x) mask (actualPoint rank x)
      strictSquareGates q 0 (pts.map Slot.exponent) ∧
      strictSquareGates q (selectedWord pts).sum (remainingWord pts) ∧
      (q+(buffer : ℝ))+(buffer : ℝ)/2 ≤
        actualSelectedSubproductV (1+3*kappa) (∑ i ∈ mask, x i) ∧
      2*(q+(buffer : ℝ))-1 ≤ (∑ i ∈ mask, x i) ∧
      (∑ i ∈ mask, x i) ≤ actualSelectedSubproductUpper (1+3*kappa) (q+(buffer : ℝ)) := by
  have hprefix : prefixCode rank.val (actualCode R mesh rank x) = actualCode R mesh rank x := by
    funext i
    by_cases hi : i.val < rank.val
    · simp [prefixCode,actualCode_at,hi]
    · simp [prefixCode,actualCode_at,hi]
  have hbox : inBox (box R (prefixCode rank.val (actualCode R mesh rank x)))
      (actualPoint rank x) := by
    rw [hprefix]
    exact actualCode_point_in_box R mesh rank x hx
  obtain ⟨b,mask,hm,hsel,hmask,hform,hq,hsource,hfull,hselected,hcrit,hlo,hhi⟩ :=
    computed_fresh_point_and_critical R mesh buffer floor hbuffer rank parent
      (actualCode R mesh rank x) q argument hchoice (actualPoint rank x) hbox kappa hkappa
  have hrank : ∀ i ∈ mask, i.val < rank.val := by
    simpa only [hmask] using hsource.2.2.2.2
  have hsum : (∑ i ∈ mask, actualPoint rank x i) = (∑ i ∈ mask, x i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact if_pos (hrank i hi)
  rw [hprefix] at hq hsource hfull hselected
  rw [hsum] at hcrit hlo hhi
  exact ⟨b,mask,hm,hmask,hform,hq,hsource,hfull,hselected,hcrit,hlo,hhi⟩

end
end ImbalancedChen.P2CanonicalPairTentActualSourceLicence
