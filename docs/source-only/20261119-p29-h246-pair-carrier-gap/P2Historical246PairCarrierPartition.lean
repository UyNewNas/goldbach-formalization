import ImbalancedChen.P2Historical246CausalW2Profile
import ImbalancedChen.P2EnhancedLowerPrimeChildCarriers

/-!
SOURCE ONLY / UNEVALUATED. Exact finite separation of one original W2
half-open pair-profile into the literal child gates and separately
labelled discarded pieces. No term is claimed negligible or paid.
-/
namespace ImbalancedChen.P2Historical246PairCarrierPartition

noncomputable section
open Set Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers
open P2OriginalHalfOpenProfileCarrier P2OriginalProfileThetaNormalization
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

abbrev Pair := Fin 2 → ℕ

def halfCarrier (N : ℕ) (L : ℝ) (j : Fin 36) (k : Fin 4) : Finset Pair :=
  (actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5)).filter
    (fun p => normalizedLog N L p ∈ pairHalf (originalW2At j) k)

def interior (N : ℕ) (L : ℝ) (j : Fin 36) (k : Fin 4) (p : Pair) : Prop :=
  normalizedLog N L p ∈ W2PairDomain (originalW2At j) k

def bothCoprime (N : ℕ) (old : List ℕ) (p : Pair) : Prop :=
  (p 0).Coprime (N*parentProduct old) ∧ (p 1).Coprime (N*parentProduct old)

def orderedCeiling (N : ℕ) (chi : ℝ) (p : Pair) : Prop :=
  p 0 < p 1 ∧ physicalPrime N (p 0) < chi ∧ physicalPrime N (p 1) < chi

def productGate (Q : ℝ) (old : List ℕ) (p : Pair) : Prop :=
  ((parentProduct old * p 1 * p 0 : ℕ) : ℝ) < Q

/-- The same parent and prime tests as the arithmetic child constructor.
Identification of normalizedLog with pairPoint is a separate issue. -/
theorem causal_child_has_physical_gates {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {j : Fin 36} {k : Fin 4} {p : Fin (N+1) × Fin (N+1)}
    (hp : p ∈ pairChildren j k N Q old chi) :
    parentWindow N Q old chi ∧ bothCoprime N old ![p.1.val,p.2.val] ∧
      orderedCeiling N chi ![p.1.val,p.2.val] ∧
      productGate Q old ![p.1.val,p.2.val] := by
  obtain ⟨⟨h0,h1⟩,hparent,horder,_,hc0,hc1,hprod⟩ := mem_pairChildren.mp hp
  simpa [bothCoprime,orderedCeiling,productGate] using
    (show parentWindow N Q old chi ∧
      (p.1.val.Coprime (N*parentProduct old) ∧ p.2.val.Coprime (N*parentProduct old)) ∧
      (p.1.val < p.2.val ∧ physicalPrime N p.1.val < chi ∧ physicalPrime N p.2.val < chi) ∧
      ((parentProduct old*p.2.val*p.1.val : ℕ) : ℝ) < Q from
      ⟨hparent,⟨h0.2,h1.2⟩,⟨horder,hc0,hc1⟩,hprod⟩)

/-- The closed-lower wall is retained, not erased as an integral-null set. -/
theorem noninterior_is_lower_wall {N : ℕ} {L : ℝ} {j : Fin 36} {k : Fin 4} {p : Pair}
    (hp : p ∈ halfCarrier N L j k) (hn : ¬ interior N L j k p) :
    normalizedLog N L p ∈ pairLowerWall (originalW2At j) k := by
  have hh := (Finset.mem_filter.mp hp).2
  have hw := ((pairHalf_partition (originalW2At j) k (normalizedLog N L p)).mp hh).resolve_left hn
  exact hw.2

/-- A finite signed sum over the actual half-open pair box splits into
six mutually exclusive gates. Parent failure is tested before prefix
collision, then order/ceiling, then the same-Q product cutoff. -/
theorem halfCarrier_partition_sum (N : ℕ) (Q L chi : ℝ) (old : List ℕ)
    (j : Fin 36) (k : Fin 4) (F : Pair → ℝ) :
    let S := halfCarrier N L j k
    (∑ p ∈ S, F p) =
      (∑ p ∈ S.filter (fun p => ¬ interior N L j k p), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ ¬ parentWindow N Q old chi), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
        ¬ bothCoprime N old p), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
        bothCoprime N old p ∧ ¬ orderedCeiling N chi p), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
        bothCoprime N old p ∧ orderedCeiling N chi p ∧ ¬ productGate Q old p), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
        bothCoprime N old p ∧ orderedCeiling N chi p ∧ productGate Q old p), F p) := by
  dsimp only
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases ho : interior N L j k p <;>
    by_cases hp : parentWindow N Q old chi <;>
    by_cases hc : bothCoprime N old p <;>
    by_cases hh : orderedCeiling N chi p <;>
    by_cases hq : productGate Q old p <;> simp [ho,hp,hc,hh,hq]

def oldPairAtom (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 4) (p : Pair) : ℝ :=
  thetaAtom N Q (d*p 0*p 1) *
    tableFunction false (outputAt 246 true) (pairProfile (originalW2At j) k (normalizedLog N L p))

/-- The exact finite 246th-predecessor pair-profile, before W2's /5,
uses these six terms for every original pair occurrence. -/
theorem generation246_pair_profile_partition (N : ℕ) (Q L chi : ℝ) (old : List ℕ)
    (j : Fin 36) (k : Fin 4) :
    pairThetaOldProfile N Q L (parentProduct old) (originalW2At j) k (outputAt 246 true) =
      let S := halfCarrier N L j k
      let F := oldPairAtom N Q L (parentProduct old) j k
      (∑ p ∈ S.filter (fun p => ¬ interior N L j k p), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ ¬ parentWindow N Q old chi), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
        ¬ bothCoprime N old p), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
        bothCoprime N old p ∧ ¬ orderedCeiling N chi p), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
        bothCoprime N old p ∧ orderedCeiling N chi p ∧ ¬ productGate Q old p), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
        bothCoprime N old p ∧ orderedCeiling N chi p ∧ productGate Q old p), F p) := by
  unfold pairThetaOldProfile
  rw [← Finset.sum_filter]
  change (∑ p ∈ halfCarrier N L j k, oldPairAtom N Q L (parentProduct old) j k p) = _
  exact halfCarrier_partition_sum N Q L chi old j k _

/-- The row and four separate lane lists are those actually scheduled at
246; no tag is deduplicated and no floor or /5 is recomputed. -/
theorem generation246_tagged_pair_profile_partition
    (N : ℕ) (Q L chi : ℝ) (old : List ℕ) {b : Tagged} (hb : b ∈ taggedW2 246) :
    ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
      (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
      ∀ k : Fin 4,
        pairThetaOldProfile N Q L (parentProduct old) (originalW2At j) k (outputAt 246 true) =
          let S := halfCarrier N L j k
          let F := oldPairAtom N Q L (parentProduct old) j k
          (∑ p ∈ S.filter (fun p => ¬ interior N L j k p), F p) +
          (∑ p ∈ S.filter (fun p => interior N L j k p ∧ ¬ parentWindow N Q old chi), F p) +
          (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
            ¬ bothCoprime N old p), F p) +
          (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
            bothCoprime N old p ∧ ¬ orderedCeiling N chi p), F p) +
          (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
            bothCoprime N old p ∧ orderedCeiling N chi p ∧ ¬ productGate Q old p), F p) +
          (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
            bothCoprime N old p ∧ orderedCeiling N chi p ∧ productGate Q old p), F p) := by
  obtain ⟨j,hp,hn,hlanes⟩ := actual_pair_lists 246 hb
  exact ⟨j,hp,hn,hlanes,fun k => generation246_pair_profile_partition N Q L chi old j k⟩

end
end ImbalancedChen.P2Historical246PairCarrierPartition
