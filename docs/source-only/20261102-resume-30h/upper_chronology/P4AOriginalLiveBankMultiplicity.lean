import ImbalancedChen.P4AOriginalLive19ActualChronology
import ImbalancedChen.ActualFrozenFrontierDensity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact finite source accounting on the original common incoming frontier.
The list is never replaced by a set: a state includes its original prefix,
sign, incoming mass and remaining primes, and every occurrence is retained.
The complementary, uncovered part of the frontier is still present.
-/
namespace ImbalancedChen.P4AOriginalLiveBankMultiplicity
noncomputable section
open scoped Classical BigOperators
open P4AOriginalLive171819Atlas P4AOriginalLive171819CommonParent
open P4AOriginalLive171819PrimeBank P4AOriginalLive19ActualChronology

abbrev Data := P5OriginalCommonRefinedConstructor.OriginalData

def commonFrontier (d : Data) (N cap : ℕ) (w z : ℝ) : List (FirstExitDepthState ℕ) :=
  firstExitDepthFrontier 8 (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))
    (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z)

def bankHit (c : LiveCell) (d : Data) (N : ℕ) (s : FirstExitDepthState ℕ) : Prop :=
  ∃ j ∈ bank c d.e d.chi d.m d.omega,
    primeHistoryTuple 8 s.selectedPrefix ∈ P4AOriginalCell0HalfOpenPrimeCarrier.primeBox d.m N j

def liveUnion (d : Data) (N cap : ℕ) (w z : ℝ) : List (FirstExitDepthState ℕ) :=
  (commonFrontier d N cap w z).filter fun s => decide (∃ c : LiveCell, bankHit c d N s)

def uncovered (d : Data) (N cap : ℕ) (w z : ℝ) : List (FirstExitDepthState ℕ) :=
  (commonFrontier d N cap w z).filter fun s => decide (¬ ∃ c : LiveCell, bankHit c d N s)

theorem selected_mem_iff (c : LiveCell) (d : Data) (N cap : ℕ) (w z : ℝ)
    (s : FirstExitDepthState ℕ) :
    s ∈ selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)) ↔
      s ∈ commonFrontier d N cap w z ∧ bankHit c d N s := by
  simp only [selected, commonFrontier, bankHit, List.mem_filter, decide_eq_true_eq]

theorem bankHit_unique (d : Data) (he : 0 ≤ d.e) (N cap : ℕ) (hN : 1 < N)
    (w z : ℝ) (s : FirstExitDepthState ℕ) (hs : s ∈ commonFrontier d N cap w z)
    (c c' : LiveCell) (hc : bankHit c d N s) (hc' : bankHit c' d N s) : c = c' := by
  have hsel := (selected_mem_iff c d N cap w z s).mpr ⟨hs, hc⟩
  have hsel' := (selected_mem_iff c' d N cap w z s).mpr ⟨hs, hc'⟩
  exact (actual_common_bank_owner c' c d he N cap hN w z s hsel').mp hsel

/-- A reusable exact LIST partition. Uniqueness is required only on real
list occurrences, and no nodup hypothesis or nonnegative weight is used. -/
private theorem filter_partition {α ι : Type*} [Fintype ι]
    (p : ι → α → Prop) (f : α → ℝ) (L : List α)
    (hunique : ∀ a ∈ L, ∀ i j, p i a → p j a → i = j) :
    (∑ i : ι, ((L.filter fun a => decide (p i a)).map f).sum) =
      ((L.filter fun a => decide (∃ i : ι, p i a)).map f).sum := by
  classical
  revert hunique
  induction L with
  | nil => intro _; simp
  | cons a L ih =>
      intro hunique
      have htail : ∀ b ∈ L, ∀ i j, p i b → p j b → i = j := by
        intro b hb i j hi hj
        exact hunique b (List.mem_cons_of_mem a hb) i j hi hj
      have hhead : (∑ i : ι, if p i a then f a else 0) =
          if ∃ i : ι, p i a then f a else 0 := by
        by_cases hex : ∃ i : ι, p i a
        · obtain ⟨i, hi⟩ := hex
          rw [if_pos ⟨i, hi⟩]
          rw [Finset.sum_eq_single i]
          · simp only [if_pos hi]
          · intro j _ hji
            have hj : ¬p j a := by
              intro hj
              exact hji (hunique a (by simp) j i hj hi)
            simp only [if_neg hj]
          · intro hnot
            exact (hnot (Finset.mem_univ i)).elim
        · have hnone : ∀ i : ι, ¬p i a := fun i hi => hex ⟨i, hi⟩
          simp [hex, hnone]
      have hsplit (i : ι) :
          (((a :: L).filter fun b => decide (p i b)).map f).sum =
            (if p i a then f a else 0) + ((L.filter fun b => decide (p i b)).map f).sum := by
        by_cases hi : p i a <;> simp [hi]
      rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
        ih htail, hhead]
      by_cases hex : ∃ i : ι, p i a <;> simp [hex]

/-- The exact 43-bank decomposition of the covered incoming frontier.
The arbitrary state functional can read sign, mass AND remaining primes.
Therefore repeated prime states retain their original multiplicity. -/
theorem actual_common_live_partition
    (d : Data) (he : 0 ≤ d.e) (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (f : FirstExitDepthState ℕ → ℝ) :
    (∑ c : LiveCell, ((selected c d.e d.chi d.m d.omega N cap w z
        (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map f).sum) =
      ((liveUnion d N cap w z).map f).sum := by
  have hu : ∀ s ∈ commonFrontier d N cap w z,
      ∀ c c', bankHit c d N s → bankHit c' d N s → c = c' := by
    intro s hs c c' hc hc'
    exact bankHit_unique d he N cap hN w z s hs c c' hc hc'
  simpa only [selected, commonFrontier, bankHit, liveUnion] using
    filter_partition (bankHit · d N) f (commonFrontier d N cap w z) hu

/-- Keep the uncovered complement explicitly; the live43 atlas is not
claimed to exhaust the full original58/87 adopted source domains. -/
theorem actual_common_frontier_split
    (d : Data) (he : 0 ≤ d.e) (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (f : FirstExitDepthState ℕ → ℝ) :
    ((commonFrontier d N cap w z).map f).sum =
      (∑ c : LiveCell, ((selected c d.e d.chi d.m d.omega N cap w z
        (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map f).sum) +
      ((uncovered d N cap w z).map f).sum := by
  rw [actual_common_live_partition d he N cap hN w z f]
  unfold liveUnion uncovered
  generalize commonFrontier d N cap w z = L
  induction L with
  | nil => simp
  | cons a L ih =>
      by_cases ha : ∃ c : LiveCell, bankHit c d N a
      · simp [ha, ih, add_assoc]
      · simp [ha, ih] <;> ring

/-- Real-valued occurrence counts make the multiplicity consequence
explicit, even if the same entire frontier state occurs more than once. -/
def occurrences (s : FirstExitDepthState ℕ) (L : List (FirstExitDepthState ℕ)) : ℝ :=
  (L.map fun a => if a = s then (1 : ℝ) else 0).sum

theorem actual_common_occurrence_partition
    (d : Data) (he : 0 ≤ d.e) (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (s : FirstExitDepthState ℕ) :
    (∑ c : LiveCell, occurrences s (selected c d.e d.chi d.m d.omega N cap w z
        (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)))) =
      occurrences s (liveUnion d N cap w z) :=
  actual_common_live_partition d he N cap hN w z (fun a => if a = s then 1 else 0)

/-- Original actual-density consumer on each LIVE19 bank: the true
slot19 residual term equals the literal ascending138 residual term.
This is a finite exact identity, not a raw-density limit or floor. -/
theorem actual_live19_density_terms
    (i : Fin 13) (d : Data) (he : 0 ≤ d.e) (N cap : ℕ) (hN : 1 < N) (w z : ℝ) :
    ((selected (.ascending19 i) d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map (fun s =>
        actualFrozenFrontierDensityTerm false N cap
          (fun pre => (N : ℝ) ^ P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)
            (rosserAncestor 6 pre)) s.selectedPrefix -
        actualFrozenFrontierDensityTerm false N cap
          (fun pre => (N : ℝ) ^ P4AOriginalPrior58Chronology.slot19 (N : ℝ)
            (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) pre) s.selectedPrefix)).sum =
    ((selected (.ascending19 i) d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))).map (fun s =>
        actualFrozenFrontierDensityTerm false N cap
          (fun pre => (N : ℝ) ^ P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)
            (rosserAncestor 6 pre)) s.selectedPrefix -
        actualFrozenFrontierDensityTerm false N cap
          (fun pre => (N : ℝ) ^ P5OriginalAdoptedEighthPhysicalMasks.newCap
            (sourceIndex (.ascending19 i)) (point8 (N : ℝ) pre)) s.selectedPrefix)).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  have hcap := (actual_common_live19 i d he N cap hN w z s hs).2.2.2
  simp only [actualFrozenFrontierDensityTerm, hcap]

end
end ImbalancedChen.P4AOriginalLiveBankMultiplicity
