import ImbalancedChen.P5OriginalFifthArchiveFallbackSeparation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original eleven PhysicalCell domains themselves require t0 < mu.
On THESE actual six-prime histories, the above-mu fallback cannot change
the fifth causal parent. This proves an old/common identity from the
original source geometry; it does not equate the policies globally or
prove the remaining oldCap upper guard, full22 or full87 coverage.
-/
namespace ImbalancedChen.P5OriginalElevenBelowMuAncestor
noncomputable section
open scoped Classical
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSeedHull
open P5OriginalFifthArchiveFallbackSeparation

theorem actual_parent_eq_original_on_eleven (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 6) (c : SixthCell)
    (hc : Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c
      (primeHistoryLogCoordinates N 6 pre)) :
    actualParent5 d N pre = oldFifth d N (rosserAncestor 5 pre) := by
  have h5 : (rosserAncestor 5 pre).length = 5 := by
    rw [rosserAncestor_length, hlen]
    decide
  have hx := primeHistoryLogCoordinates_ancestor N hlen (by decide : 5 ≤ 6) (0 : Fin 5)
  have hx' : primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre) 0 =
      primeHistoryLogCoordinates N 6 pre 0 := hx
  apply fifth_eq_old_below_mu d N (rosserAncestor 5 pre) h5
  rw [hx']
  exact hc.largest.le

/-- The literal eligibility test can now use the independently defined
original parent ON ITS OWN SOURCE, without an assumed equality field. -/
theorem eligibleSixth_iff_original_parent (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (c : SixthCell) :
    eligibleSixth d N c pre ↔
      pre.length = 6 ∧
        Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c
          (primeHistoryLogCoordinates N 6 pre) ∧
        Certificates.P2OriginalSixthElevenLogSemantics.H5
          (primeHistoryLogCoordinates N 6 pre) < oldFifth d N (rosserAncestor 5 pre) ∧
        oldFifth d N (rosserAncestor 5 pre) ≤
          Certificates.P2OriginalSixthElevenLogSemantics.oldCap c
            (primeHistoryLogCoordinates N 6 pre) := by
  constructor
  · intro h
    have hp := actual_parent_eq_original_on_eleven d N pre h.1 c h.2.1
    exact ⟨h.1, h.2.1, hp ▸ h.2.2.1, hp ▸ h.2.2.2⟩
  · rintro ⟨hlen, hc, hlo, hhi⟩
    have hp := actual_parent_eq_original_on_eleven d N pre hlen c hc
    exact ⟨hlen, hc, hp.symm ▸ hlo, hp.symm ▸ hhi⟩

end
end ImbalancedChen.P5OriginalElevenBelowMuAncestor
