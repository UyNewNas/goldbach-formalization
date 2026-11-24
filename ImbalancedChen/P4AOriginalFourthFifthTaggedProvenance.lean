import ImbalancedChen.P1FiniteMaxRowProvenance
import ImbalancedChen.P4AOriginalFull87BoxedWinner

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Deterministic provenance for the unchanged ORIGINAL fourth/fifth banks.
A row label belongs to the original finite bank; its eligibility, raw
attainment, selected mask, rounded cap and square licences are connected.
Closed fourth boxes and half-open fifth cells keep their original tests.
These are witness traces, not new policies or new arithmetic carriers.
-/
namespace ImbalancedChen.P4AOriginalFourthFifthTaggedProvenance
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P1AffineTaggedDecision
open P4AOriginalFourthFifthAffinePrograms P1GuardFrozenFiniteCapAlgebra
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalCompleteSixthChronology P4AOriginalFull87FiniteParentCaps
open P1OriginalVariableFourthContinuation
open P4AOriginalFourthFifthUniformActionLicense
open P4AOriginalFull87SourceDictionary
open P1QuantizedActionLicense (LowerLicense)
open P4AOriginalFull87HistoryCore (width)

abbrev Row4 (d : OriginalData) := P1FiniteMaxRowProvenance.Row d.rows4
abbrev Row5 (d : OriginalData) := P1FiniteMaxRowProvenance.Row d.rows5

def seed4 (b : ℚ) : Program 4 := atom (K (b : ℝ))
def seed5 (d : OriginalData) (b : ℚ) : Program 5 :=
  (fourthProgram d b).pull Fin.castSucc

def trace4 (n : ℕ) (d : OriginalData) (b : ℚ) : Trace 4 (Option (Row4 d)) :=
  P1FiniteMaxRowProvenance.decision d.rows4 (fourthTests d)
    (fourthCandidate d) (seed4 b) n b

def trace5 (n : ℕ) (d : OriginalData) (b : ℚ) : Trace 5 (Option (Row5 d)) :=
  P1FiniteMaxRowProvenance.decision d.rows5 (fifthTests d)
    (fifthCandidate d) (seed5 d b) n b

/-- The predecessor at rank four is the image of the ACTUAL third value,
not an arbitrary new floor. On the source slice lambda3=originalSeed=b. -/
def predecessor4 (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) : ℝ :=
  protect n (originalSeed (data e q om) N pre) (lambda3 (data e q om) N pre)

theorem values4 (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 4)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ)) :
    protect n b ((seed4 b).eval (primeHistoryLogCoordinates N 4 pre)) =
        predecessor4 n e q om N pre ∧
    protect n b ((fourthProgram (data e q om) b).eval
      (primeHistoryLogCoordinates N 4 pre)) = cap4 n e q om N pre := by
  constructor
  · simp only [predecessor4,hb,hseed,seed4,Program.eval,Affine.eval_const]
  · rw [fourth_at_history (data e q om) b N pre hlen hb,cap4,hseed]

theorem seed5_at_history (d : OriginalData) (b : ℚ) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 5)
    (hb : lambda3 d N pre = (b : ℝ)) :
    (seed5 d b).eval (primeHistoryLogCoordinates N 5 pre) =
      exponent4 d N (rosserAncestor 4 pre) := by
  have hc : (fun i : Fin 4 => primeHistoryLogCoordinates N 5 pre i.castSucc) =
      primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) := by
    funext i
    exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 4 ≤ 5) i).symm
  rw [seed5,Program.eval_pull,hc]
  apply fourth_at_history d b N _ (by simp [hlen])
  rw [lambda3_ancestor d N 4 (by decide),hb]

theorem values5 (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 5)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ)) :
    protect n b ((seed5 (data e q om) b).eval (primeHistoryLogCoordinates N 5 pre)) =
        cap4 n e q om N (rosserAncestor 4 pre) ∧
    protect n b ((fifthProgram (data e q om) b).eval
      (primeHistoryLogCoordinates N 5 pre)) = cap5 n e q om N pre := by
  constructor
  · rw [seed5_at_history (data e q om) b N pre hlen hb,
      cap4,originalSeed_ancestor _ _ 4 (by decide),hseed]
  · rw [fifth_at_history (data e q om) b N pre hlen hb,cap5_eq_protect,hseed]

theorem fourth_none_iff (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 4)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ)) (m : ℕ) :
    (trace4 n (data e q om) b).lookup m (primeHistoryLogCoordinates N 4 pre) = none ↔
      ¬predecessor4 n e q om N pre < cap4 n e q om N pre := by
  rw [Trace.lookup_exact]
  have h := P1FiniteMaxRowProvenance.decision_none_iff
    (data e q om).rows4 (fourthTests (data e q om)) (fourthCandidate (data e q om))
    (seed4 b) n b (primeHistoryLogCoordinates N 4 pre)
  change (trace4 n (data e q om) b).eval (primeHistoryLogCoordinates N 4 pre) = none ↔
    ¬protect n b ((seed4 b).eval (primeHistoryLogCoordinates N 4 pre)) <
      protect n b ((fourthProgram (data e q om) b).eval
        (primeHistoryLogCoordinates N 4 pre)) at h
  rw [(values4 n e q om N b pre hlen hb hseed).1,
    (values4 n e q om N b pre hlen hb hseed).2] at h
  exact h

theorem fifth_none_iff (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 5)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ)) (m : ℕ) :
    (trace5 n (data e q om) b).lookup m (primeHistoryLogCoordinates N 5 pre) = none ↔
      ¬cap4 n e q om N (rosserAncestor 4 pre) < cap5 n e q om N pre := by
  rw [Trace.lookup_exact]
  have h := P1FiniteMaxRowProvenance.decision_none_iff
    (data e q om).rows5 (fifthTests (data e q om)) (fifthCandidate (data e q om))
    (seed5 (data e q om) b) n b (primeHistoryLogCoordinates N 5 pre)
  change (trace5 n (data e q om) b).eval (primeHistoryLogCoordinates N 5 pre) = none ↔
    ¬protect n b ((seed5 (data e q om) b).eval (primeHistoryLogCoordinates N 5 pre)) <
      protect n b ((fifthProgram (data e q om) b).eval
        (primeHistoryLogCoordinates N 5 pre)) at h
  rw [(values5 n e q om N b pre hlen hb hseed).1,
    (values5 n e q om N b pre hlen hb hseed).2] at h
  exact h

/-- Every returned ROW belongs to the exact original bank. Its own
licence, not that of some other maximizing row, supplies the selected mask. -/
theorem fourth_some_licensed (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 4)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ))
    (ha : ArchiveLicenses n e q om) (m : ℕ) (r : Row4 (data e q om))
    (htag : (trace4 n (data e q om) b).lookup m
      (primeHistoryLogCoordinates N 4 pre) = some r) :
    predecessor4 n e q om N pre < cap4 n e q om N pre ∧
    producerEligible (data e q om).licensed4 r.val (primeHistoryLogCoordinates N 4 pre) ∧
    exponent4 (data e q om) N pre =
      r.val.bufferedCandidate ((data e q om).e : ℝ) (primeHistoryLogCoordinates N 4 pre) ∧
    cap4 n e q om N pre = (rounded n
      (r.val.bufferedCandidate ((data e q om).e : ℝ) (primeHistoryLogCoordinates N 4 pre)) : ℝ) ∧
    LowerLicense r.val.selected (primeHistoryLogCoordinates N 4 pre) (cap4 n e q om N pre) ∧
    cap4 n e q om N pre + width n + 2 * ((data e q om).e : ℝ) ≤
      VariableEnvelope.v (∑ i ∈ r.val.selected, primeHistoryLogCoordinates N 4 pre i) := by
  rw [Trace.lookup_exact] at htag
  have h := P1FiniteMaxRowProvenance.decision_some_sound
    (data e q om).rows4 (fourthTests (data e q om)) (fourthCandidate (data e q om))
    (seed4 b) n b (primeHistoryLogCoordinates N 4 pre) r htag
  change protect n b ((seed4 b).eval (primeHistoryLogCoordinates N 4 pre)) <
      protect n b ((fourthProgram (data e q om) b).eval (primeHistoryLogCoordinates N 4 pre)) ∧
    Passed (primeHistoryLogCoordinates N 4 pre) (fourthTests (data e q om) r.val) ∧
    (fourthProgram (data e q om) b).eval (primeHistoryLogCoordinates N 4 pre) =
      (fourthCandidate (data e q om) r.val).eval (primeHistoryLogCoordinates N 4 pre) ∧
    protect n b ((fourthProgram (data e q om) b).eval (primeHistoryLogCoordinates N 4 pre)) =
      (rounded n ((fourthCandidate (data e q om) r.val).eval
        (primeHistoryLogCoordinates N 4 pre)) : ℝ) at h
  rw [(values4 n e q om N b pre hlen hb hseed).1,
    (values4 n e q om N b pre hlen hb hseed).2,
    fourthTests_exact,fourth_at_history (data e q om) b N pre hlen hb,
    fourthCandidate_exact] at h
  obtain ⟨hwin,hel,hraw,hcap⟩ := h
  have hlic := ha.1 r.val r.property hel.1 _ hel.2
  exact ⟨hwin,hel,hraw,hcap,by rw [hcap]; exact hlic.1,
    by rw [hcap]; exact hlic.2⟩

theorem fifth_some_licensed (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 5)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ))
    (ha : ArchiveLicenses n e q om) (m : ℕ) (r : Row5 (data e q om))
    (htag : (trace5 n (data e q om) b).lookup m
      (primeHistoryLogCoordinates N 5 pre) = some r) :
    cap4 n e q om N (rosserAncestor 4 pre) < cap5 n e q om N pre ∧
    P1OriginalVariableFifthContinuation.eligible (data e q om).e (data e q om).chi
      (data e q om).m (data e q om).omega (data e q om).J5 r.val
      (primeHistoryLogCoordinates N 5 pre) ∧
    exponent5 (data e q om) N pre = P1OriginalVariableFifthContinuation.candidate
      ((data e q om).e : ℝ) r.val.selected (primeHistoryLogCoordinates N 5 pre) ∧
    cap5 n e q om N pre = (rounded n (P1OriginalVariableFifthContinuation.candidate
      ((data e q om).e : ℝ) r.val.selected (primeHistoryLogCoordinates N 5 pre)) : ℝ) ∧
    LowerLicense r.val.selected (primeHistoryLogCoordinates N 5 pre) (cap5 n e q om N pre) ∧
    cap5 n e q om N pre + width n + 2 * ((data e q om).e : ℝ) ≤
      VariableEnvelope.v (∑ i ∈ r.val.selected, primeHistoryLogCoordinates N 5 pre i) := by
  rw [Trace.lookup_exact] at htag
  have h := P1FiniteMaxRowProvenance.decision_some_sound
    (data e q om).rows5 (fifthTests (data e q om)) (fifthCandidate (data e q om))
    (seed5 (data e q om) b) n b (primeHistoryLogCoordinates N 5 pre) r htag
  change protect n b ((seed5 (data e q om) b).eval (primeHistoryLogCoordinates N 5 pre)) <
      protect n b ((fifthProgram (data e q om) b).eval (primeHistoryLogCoordinates N 5 pre)) ∧
    Passed (primeHistoryLogCoordinates N 5 pre) (fifthTests (data e q om) r.val) ∧
    (fifthProgram (data e q om) b).eval (primeHistoryLogCoordinates N 5 pre) =
      (fifthCandidate (data e q om) r.val).eval (primeHistoryLogCoordinates N 5 pre) ∧
    protect n b ((fifthProgram (data e q om) b).eval (primeHistoryLogCoordinates N 5 pre)) =
      (rounded n ((fifthCandidate (data e q om) r.val).eval
        (primeHistoryLogCoordinates N 5 pre)) : ℝ) at h
  rw [(values5 n e q om N b pre hlen hb hseed).1,
    (values5 n e q om N b pre hlen hb hseed).2,
    fifthTests_exact,fifth_at_history (data e q om) b N pre hlen hb,
    fifthCandidate_exact] at h
  obtain ⟨hwin,hel,hraw,hcap⟩ := h
  have hlic := ha.2 r.val r.property _ hel
  exact ⟨hwin,hel,hraw,hcap,by rw [hcap]; exact hlic.1,
    by rw [hcap]; exact hlic.2⟩

/-- The SAME third entry supplies both own-rank histories. A child neither
selects the earlier entry nor changes its value. No support input is added. -/
theorem source_seed_all (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre)) :
    ∃ b ∈ thirdAlphabet (data e q om).e (data e q om).chi (data e q om).m,
      originalSeed (data e q om) N pre = (b : ℝ) ∧
      ∀ k : ℕ, 3 ≤ k →
        originalSeed (data e q om) N (rosserAncestor k pre) = (b : ℝ) ∧
        lambda3 (data e q om) N (rosserAncestor k pre) = (b : ℝ) := by
  obtain ⟨b,hb,hseed,_hseed6,hb6⟩ :=
    P4AOriginalSixthTaggedWinner.source_seed e q om N pre hlen c hs
  rw [lambda3_ancestor _ _ 6 (by decide)] at hb6
  refine ⟨b,hb,hseed,?_⟩
  intro k hk
  exact ⟨by rw [originalSeed_ancestor _ _ k hk,hseed],
    by rw [lambda3_ancestor _ _ k hk,hb6]⟩

/-- On the actual realized source, the protected predecessor is exactly
the unchanged third level. This is not asserted for arbitrary negative
seed values outside that source; the real history supplies positivity. -/
theorem predecessor4_eq_third_on_history (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (hr : P4AOriginalFull87ActualCommonHistory.RealizedHistory e q om N pre c) :
    predecessor4 n e q om N (rosserAncestor 4 pre) =
      lambda3 (data e q om) N (rosserAncestor 4 pre) := by
  have hb := parent_bounds_of_history n e q om N pre hlen c hs hr
  let L := lambda3 (data e q om) N (rosserAncestor 4 pre)
  have h0 : 0 < L := hb.1
  have hLcmp : L ≤ comparison c (primeHistoryLogCoordinates N 8 pre) :=
    hb.2.1.trans (hb.2.2.1.trans (hb.2.2.2.1.trans hb.2.2.2.2.1))
  have hLcap : L ≤ VariableEnvelope.cap := hLcmp.trans
    ((source_improvement_terminal hs).1.le.trans (source_physical_ceiling hs).le)
  have hseed := P4AOriginalFull87CompleteSixthBound.actual_third_eq_original
    (data e q om) N pre hlen c hs
  change L = originalSeed (data e q om) N pre at hseed
  rw [predecessor4,originalSeed_ancestor _ _ 4 (by decide),← hseed]
  exact le_antisymm (protect_error n L L h0.le le_rfl hLcap).2.2
    (seed_le_protect n L L)

/-- These append equalities are literal causality, not a projection of a
child's exceptional wall into the earlier ancestor domain. -/
theorem fourth_descendants (n : ℕ) (d : OriginalData) (b : ℚ) (N : ℝ)
    (pre later : List ℕ) (hlen : 4 ≤ pre.length) :
    (trace4 n d b).eval (primeHistoryLogCoordinates N 4 (rosserAncestor 4 (later ++ pre))) =
      (trace4 n d b).eval (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre)) := by
  rw [rosserAncestor_append 4 later pre hlen]

theorem fifth_descendants (n : ℕ) (d : OriginalData) (b : ℚ) (N : ℝ)
    (pre later : List ℕ) (hlen : 5 ≤ pre.length) :
    (trace5 n d b).eval (primeHistoryLogCoordinates N 5 (rosserAncestor 5 (later ++ pre))) =
      (trace5 n d b).eval (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre)) := by
  rw [rosserAncestor_append 5 later pre hlen]


/-- Whole-box row licences are distinct from scalar constancy. This
intermediate theorem consumes an actual comparison certificate; the public
schedule constructs the covered boxes and thus discharges that obligation. -/
theorem fourth_closed_box_licensed (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (b : ℚ) (ha : ArchiveLicenses n e q om)
    (s : (trace4 n (data e q om) b).code.Signature)
    (lo hi : Fin 4 → ℝ)
    (hc : (trace4 n (data e q om) b).code.BoxCertificate s lo hi)
    (r : Row4 (data e q om))
    (htag : (trace4 n (data e q om) b).tableTag s = some r)
    (u : Fin 4 → ℝ) (hl : ∀ i, lo i ≤ u i) (hu : ∀ i, u i ≤ hi i) :
    producerEligible (data e q om).licensed4 r.val u ∧
    (fourthProgram (data e q om) b).eval u =
      r.val.bufferedCandidate ((data e q om).e : ℝ) u ∧
    protect n b ((fourthProgram (data e q om) b).eval u) =
      (rounded n (r.val.bufferedCandidate ((data e q om).e : ℝ) u) : ℝ) ∧
    LowerLicense r.val.selected u
      (protect n b ((fourthProgram (data e q om) b).eval u)) ∧
    protect n b ((fourthProgram (data e q om) b).eval u) + width n +
      2 * ((data e q om).e : ℝ) ≤ VariableEnvelope.v (∑ i ∈ r.val.selected, u i) := by
  have ht := ((trace4 n (data e q om) b).tag_on_closed_box s lo hi hc u hl hu).trans htag
  have h := P1FiniteMaxRowProvenance.decision_some_sound
    (data e q om).rows4 (fourthTests (data e q om)) (fourthCandidate (data e q om))
    (seed4 b) n b u r ht
  have hel := (fourthTests_exact (data e q om) r.val u).mp h.2.1
  have hraw : (fourthProgram (data e q om) b).eval u =
      r.val.bufferedCandidate ((data e q om).e : ℝ) u := by
    simpa only [fourthCandidate_exact] using h.2.2.1
  have hcap : protect n b ((fourthProgram (data e q om) b).eval u) =
      (rounded n (r.val.bufferedCandidate ((data e q om).e : ℝ) u) : ℝ) := by
    simpa only [fourthCandidate_exact] using h.2.2.2
  have hlic := ha.1 r.val r.property hel.1 u hel.2
  exact ⟨hel,hraw,hcap,by rw [hcap]; exact hlic.1,
    by rw [hcap]; exact hlic.2⟩

theorem fifth_closed_box_licensed (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (b : ℚ) (ha : ArchiveLicenses n e q om)
    (s : (trace5 n (data e q om) b).code.Signature)
    (lo hi : Fin 5 → ℝ)
    (hc : (trace5 n (data e q om) b).code.BoxCertificate s lo hi)
    (r : Row5 (data e q om))
    (htag : (trace5 n (data e q om) b).tableTag s = some r)
    (u : Fin 5 → ℝ) (hl : ∀ i, lo i ≤ u i) (hu : ∀ i, u i ≤ hi i) :
    P1OriginalVariableFifthContinuation.eligible (data e q om).e (data e q om).chi
      (data e q om).m (data e q om).omega (data e q om).J5 r.val u ∧
    (fifthProgram (data e q om) b).eval u = P1OriginalVariableFifthContinuation.candidate
      ((data e q om).e : ℝ) r.val.selected u ∧
    protect n b ((fifthProgram (data e q om) b).eval u) =
      (rounded n (P1OriginalVariableFifthContinuation.candidate
        ((data e q om).e : ℝ) r.val.selected u) : ℝ) ∧
    LowerLicense r.val.selected u
      (protect n b ((fifthProgram (data e q om) b).eval u)) ∧
    protect n b ((fifthProgram (data e q om) b).eval u) + width n +
      2 * ((data e q om).e : ℝ) ≤ VariableEnvelope.v (∑ i ∈ r.val.selected, u i) := by
  have ht := ((trace5 n (data e q om) b).tag_on_closed_box s lo hi hc u hl hu).trans htag
  have h := P1FiniteMaxRowProvenance.decision_some_sound
    (data e q om).rows5 (fifthTests (data e q om)) (fifthCandidate (data e q om))
    (seed5 (data e q om) b) n b u r ht
  have hel := (fifthTests_exact (data e q om) r.val u).mp h.2.1
  have hraw : (fifthProgram (data e q om) b).eval u =
      P1OriginalVariableFifthContinuation.candidate ((data e q om).e : ℝ) r.val.selected u := by
    simpa only [fifthCandidate_exact] using h.2.2.1
  have hcap : protect n b ((fifthProgram (data e q om) b).eval u) =
      (rounded n (P1OriginalVariableFifthContinuation.candidate
        ((data e q om).e : ℝ) r.val.selected u) : ℝ) := by
    simpa only [fifthCandidate_exact] using h.2.2.2
  have hlic := ha.2 r.val r.property u hel
  exact ⟨hel,hraw,hcap,by rw [hcap]; exact hlic.1,
    by rw [hcap]; exact hlic.2⟩

end
end ImbalancedChen.P4AOriginalFourthFifthTaggedProvenance
