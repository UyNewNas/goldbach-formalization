import ImbalancedChen.P4AOriginalOrderedSavedGain
import ImbalancedChen.P4AOriginalOrderedLaterPaid
import ImbalancedChen.P4AOriginalFiniteFallbackSectorTransport

/-! The G4 and all eight later sixth changes survive the common high
first-prime dispatcher. Their genuine winners all have x below mu.
This is checked on the actual sixth ancestor used by the frozen policy. -/
namespace ImbalancedChen.P4AOriginalLaterSixthHighDispatch
noncomputable section
open VariableEnvelope
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFiniteFallbackPolicy (high dispatch Rule)
open P4AOriginalOrderedSixthStages (orderedLevel level policy)
open P4AOriginalFull87RawChronology (rawRoot)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalOrderedLaterPaid (total)

theorem physical_high (N : ℝ) (h : List ℕ) (hl : h.length=6) (hh : high N h) :
    mu<primeHistoryLogCoordinates N 6 h 0 := by
  change mu<primeHistoryLogCoordinates N 1 (rosserAncestor 1 h) 0 at hh
  simpa only [primeHistoryLogCoordinates_ancestor N hl (by decide : 1≤6) (0:Fin 1)] using hh

theorem on_words (m k n : ℕ) (d : OriginalData) (omega N : ℝ)
    (hc : ∀ h : List ℕ,h.length=6 → high N h →
      orderedLevel m n d omega N h=orderedLevel k n d omega N h)
    (b : Bool) (h : List ℕ) (hh : high N h) : policy m n d omega N b h=policy k n d omega N b h := by
  by_cases hl : h.length≤6
  · simp only [policy,firstExitDepthSplicePolicy,if_pos hl]
  · have hlen : (rosserAncestor 6 h).length=6 := by simp only [rosserAncestor,List.length_drop];omega
    have hh' : high N (rosserAncestor 6 h) := by
      simpa only [high,P4AOriginalFiniteFallbackPolicy.point,rosserAncestor_nested 1 6 (by decide)] using hh
    simp only [policy,firstExitDepthSplicePolicy,if_neg hl,frozenParityRosserPolicy,ancestorFrozenPolicy]
    rw [hc _ hlen hh']

theorem saved_words (n : ℕ) (d : OriginalData) (omega N : ℝ) :
    ∀ b h,high N h → policy 0 n d omega N b h=policy 1 n d omega N b h := by
  apply on_words
  intro h hl hh
  apply (P4AOriginalOrderedSavedGain.fixed_outside n _ d N h ?_).symm
  intro i hi
  have hcut := (P4AOriginalSavedSixthPrimeMean.bounds i ((P4AOriginalSavedSixthSourceGates.source_iff i _).mp hi).1 0).2
  have hx := physical_high N h hl hh
  dsimp [mu] at hx
  linarith

theorem later_words (n : ℕ) (d : OriginalData) (omega N : ℝ) :
    ∀ b h,high N h → policy 2 n d omega N b h=policy 10 n d omega N b h := by
  apply on_words
  intro h hl hh
  let R := P4AOriginalOrderedThirdFullPolicy.current d omega N h
  have heq (k : ℕ) : level (k+2) n R d N h=level 2 n R d N h := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hm := P4AOriginalOrderedSixthStages.level_mono n R d N h (show k+2≤k+3 by omega)
      have he : level (k+2) n R d N h=level (k+3) n R d N h := by
        by_contra hn
        obtain ⟨c,_,hc,_⟩ := P4AOriginalOrderedLaterChanged.changed_owner k n R d N h (lt_of_le_of_ne hm hn)
        exact (not_lt_of_ge (P4AOriginalSixthSquareRows.later_source_basic c _ hc).1.le) (physical_high N h hl hh)
      exact he.symm.trans ih
  exact (heq 8).symm

theorem dispatch_later (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) (U : Rule)
    (hU : ∀ h,U true h=true) :
    normalize N (rawRoot (dispatch N U (policy 2 n d omega (N:ℝ))) N-
      rawRoot (dispatch N U (policy 10 n d omega (N:ℝ))) N)=total n d omega N :=
  congrArg (normalize N) (P4AOriginalFiniteFallbackSectorTransport.local_increment N U _ _ hU
    (P4AOriginalOrderedSixthSigned.even 2 n d omega _) (P4AOriginalOrderedSixthSigned.even 10 n d omega _)
    (later_words n d omega _))

theorem dispatch_saved (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) (U : Rule)
    (hU : ∀ h,U true h=true) :
    normalize N (rawRoot (dispatch N U (policy 0 n d omega (N:ℝ))) N-
      rawRoot (dispatch N U (policy 1 n d omega (N:ℝ))) N)=
      normalize N (rawRoot (P4AOriginalOrderedSixthStages.orderedFifth n d omega (N:ℝ)) N-
        rawRoot (policy 1 n d omega (N:ℝ)) N) := by
  rw [P4AOriginalFiniteFallbackSectorTransport.local_increment N U _ _ hU
    (P4AOriginalOrderedSixthSigned.even 0 n d omega _) (P4AOriginalOrderedSixthSigned.even 1 n d omega _)
    (saved_words n d omega _),P4AOriginalOrderedSixthStages.policy_zero]

end
end ImbalancedChen.P4AOriginalLaterSixthHighDispatch
