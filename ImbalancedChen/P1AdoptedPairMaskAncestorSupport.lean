import ImbalancedChen.P1AdoptedE0E1ActualSupport
import ImbalancedChen.P1AdoptedMaskAncestors
import ImbalancedChen.FrozenRosserPolicy

/-!
SOURCE ONLY, 2026-10-24. Imports name the eventual integration module paths;
the first two dependencies are currently owned source-only draft files.

The arithmetic pair mask reads processing coordinates 0 and 1, which are the
earliest selected primes in the reverse-stored history. Later selections are
prepended. A literal Chen increasing pair (p,q) has history [p,q], whose
processing coordinates are (log_N q,log_N p). A full increasing Chen tuple
((p1,p2),(p3,p4)) has history [p1,p2,p3,p4], so this mask reads its last pair.

The pair mask alone supplies neither z nor w. The strict lower outer
endpoints and all inner-fibre conditions remain explicit below.
-/

namespace ImbalancedChen.P1AdoptedPairMaskAncestorSupport

noncomputable section

open Certificates.PairedV2
open FullMask.P1E0E1

/-- Exact first two processing coordinates of the existing reverse-stored list. -/
def historyPairCoordinates (N : ℝ) (history : List ℕ) : ℝ × ℝ :=
  (primeHistoryLogCoordinates N 2 (rosserAncestor 2 history) 0,
    primeHistoryLogCoordinates N 2 (rosserAncestor 2 history) 1)

/-- Prime values in the increasing-pair orientation expected by deletionMask. -/
def historyPairValues (history : List ℕ) : ℕ × ℕ :=
  (primeHistoryTuple 2 (rosserAncestor 2 history) 1,
    primeHistoryTuple 2 (rosserAncestor 2 history) 0)

theorem primePairCoordinates_historyPairValues (N : ℝ) (history : List ℕ) :
    primePairCoordinates N (historyPairValues history) = historyPairCoordinates N history := by
  rfl

/-- Correct history length makes the rank-two reading exactly the first
two coordinates of the full processing-order tuple. -/
theorem historyPairCoordinates_eq_full (N : ℝ) {k : ℕ} (hk : 2 ≤ k)
    (history : List ℕ) (hlen : history.length = k) :
    historyPairCoordinates N history =
      (primeHistoryLogCoordinates N k history ⟨0, by omega⟩,
        primeHistoryLogCoordinates N k history ⟨1, by omega⟩) := by
  simp only [historyPairCoordinates, primeHistoryLogCoordinates_ancestor N hlen hk]

theorem historyPairCoordinates_ancestor (N : ℝ) {m : ℕ} (hm : 2 ≤ m)
    (history : List ℕ) :
    historyPairCoordinates N (rosserAncestor m history) = historyPairCoordinates N history := by
  simp only [historyPairCoordinates, rosserAncestor_nested 2 m hm]

theorem historyPairCoordinates_eq_rank (N : ℝ) {m : ℕ} (hm : 2 ≤ m)
    (history : List ℕ) (hlen : m ≤ history.length) :
    historyPairCoordinates N history =
      (primeHistoryLogCoordinates N m (rosserAncestor m history) ⟨0, by omega⟩,
        primeHistoryLogCoordinates N m (rosserAncestor m history) ⟨1, by omega⟩) := by
  have ha : (rosserAncestor m history).length = m := by
    rw [rosserAncestor_length, min_eq_left hlen]
  rw [← historyPairCoordinates_ancestor N hm history]
  exact historyPairCoordinates_eq_full N hm (rosserAncestor m history) ha

theorem historyPairCoordinates_append (N : ℝ) (later history : List ℕ)
    (hlen : 2 ≤ history.length) :
    historyPairCoordinates N (later ++ history) = historyPairCoordinates N history := by
  simp only [historyPairCoordinates, rosserAncestor_append 2 later history hlen]

def historyDeletionMask (N : ℝ) (history : List ℕ) : Prop :=
  historyPairCoordinates N history ∈ pairRegion

theorem historyDeletionMask_eq_pairMask (N : ℝ) (history : List ℕ) :
    historyDeletionMask N history ↔ deletionMask N (historyPairValues history) := by
  rfl

theorem historyDeletionMask_unique_owner (N : ℝ) (history : List ℕ) :
    historyDeletionMask N history ↔
      ∃! r : FullMask.Row, historyPairCoordinates N history ∈ pairCell r := by
  exact pair_region_unique_owner _

theorem historyDeletionMask_ancestor (N : ℝ) {m : ℕ} (hm : 2 ≤ m)
    (history : List ℕ) :
    historyDeletionMask N (rosserAncestor m history) ↔ historyDeletionMask N history := by
  unfold historyDeletionMask
  rw [historyPairCoordinates_ancestor N hm]

theorem historyDeletionMask_append (N : ℝ) (later history : List ℕ)
    (hlen : 2 ≤ history.length) :
    historyDeletionMask N (later ++ history) ↔ historyDeletionMask N history := by
  unfold historyDeletionMask
  rw [historyPairCoordinates_append N later history hlen]

theorem historyDeletionMask_iff_labels (N : ℝ) (history : List ℕ) :
    historyDeletionMask N history ↔
      historyPairCoordinates N history ∈ e0PairRegion ∨
        historyPairCoordinates N history ∈ e1PairRegion := by
  change historyPairCoordinates N history ∈ pairRegion ↔
    historyPairCoordinates N history ∈ e0PairRegion ∪ e1PairRegion
  rw [pair_region_union]

theorem history_e0_label_append (N : ℝ) (later history : List ℕ)
    (hlen : 2 ≤ history.length) :
    historyPairCoordinates N (later ++ history) ∈ e0PairRegion ↔
      historyPairCoordinates N history ∈ e0PairRegion := by
  rw [historyPairCoordinates_append N later history hlen]

theorem history_e1_label_append (N : ℝ) (later history : List ℕ)
    (hlen : 2 ≤ history.length) :
    historyPairCoordinates N (later ++ history) ∈ e1PairRegion ↔
      historyPairCoordinates N history ∈ e1PairRegion := by
  rw [historyPairCoordinates_append N later history hlen]

/-- The unique row of a pair-mask hit is unchanged at ranks three and four. -/
theorem history_common_pair_owner (N : ℝ) (history : List ℕ)
    (hmask : historyDeletionMask N history) :
    ∃! r : FullMask.Row,
      historyPairCoordinates N history ∈ pairCell r ∧
      historyPairCoordinates N (rosserAncestor 3 history) ∈ pairCell r ∧
      historyPairCoordinates N (rosserAncestor 4 history) ∈ pairCell r := by
  obtain ⟨r, hr, huniq⟩ := (historyDeletionMask_unique_owner N history).1 hmask
  refine ⟨r, ?_, ?_⟩
  · rw [historyPairCoordinates_ancestor N (by omega : 2 ≤ 3),
      historyPairCoordinates_ancestor N (by omega : 2 ≤ 4)]
    exact ⟨hr, hr, hr⟩
  · intro s hs
    exact huniq s hs.1

/-- Exact extra conditions needed to recover an actual strict rank-three
fibre from a half-open arithmetic outer rectangle. -/
theorem ancestor3_support_iff_pairCell (r : FullMask.Row) (y : Fin 3 → ℝ) :
    y ∈ P1AdoptedMaskAncestors.Mask.ancestor3Support r ↔
      (y 0, y 1) ∈ pairCell r ∧
      (tLower (FullMask.indices r).1 : ℝ) < y 0 ∧
      (uLower (FullMask.indices r).2 : ℝ) < y 1 ∧
      (a : ℝ) < y 2 ∧ y 2 < (FullMask.cutoff r : ℝ) := by
  constructor
  · rintro ⟨htl, htr, hul, hur, haz, hz⟩
    exact ⟨⟨htl.le, htr, hul.le, hur⟩, htl, hul, haz, hz⟩
  · rintro ⟨⟨_, htr, _, hur⟩, htl, hul, haz, hz⟩
    exact ⟨htl, htr, hul, hur, haz, hz⟩

/-- Pair membership leaves both missing coordinates and the strict lower
outer boundaries as separate, necessary conditions. -/
theorem fibre_support_iff_pairCell (r : FullMask.Row) (x : Fin 4 → ℝ) :
    x ∈ FullMask.support r ↔
      (x 0, x 1) ∈ pairCell r ∧
      (tLower (FullMask.indices r).1 : ℝ) < x 0 ∧
      (uLower (FullMask.indices r).2 : ℝ) < x 1 ∧
      (a : ℝ) < x 3 ∧ x 3 < x 2 ∧ x 2 < (FullMask.cutoff r : ℝ) := by
  constructor
  · rintro ⟨htl, htr, hul, hur, haw, hwz, hz⟩
    exact ⟨⟨htl.le, htr, hul.le, hur⟩, htl, hul, haw, hwz, hz⟩
  · rintro ⟨⟨_, htr, _, hur⟩, htl, hul, haw, hwz, hz⟩
    exact ⟨htl, htr, hul, hur, haw, hwz, hz⟩

/-- Explicit real lift; this constructs coordinates, not additional primes. -/
def liftPair (r : FullMask.Row) (y : ℝ × ℝ) : Fin 4 → ℝ :=
  ![y.1, y.2, ((a : ℝ) + (FullMask.cutoff r : ℝ)) / 2,
    (3 * (a : ℝ) + (FullMask.cutoff r : ℝ)) / 4]

theorem liftPair_mem_fibre (r : FullMask.Row) (y : ℝ × ℝ)
    (hy : y ∈ pairCell r)
    (ht : (tLower (FullMask.indices r).1 : ℝ) < y.1)
    (hu : (uLower (FullMask.indices r).2 : ℝ) < y.2) :
    liftPair r y ∈ FullMask.support r := by
  apply (fibre_support_iff_pairCell r _).2
  have haz : (a : ℝ) < (FullMask.cutoff r : ℝ) := by
    exact_mod_cast (FullMask.row_endpoint_bounds r).1
  refine ⟨hy, ht, hu, ?_, ?_, ?_⟩ <;> dsimp [liftPair] <;> linarith

/-- The exact image is the strict interior of the half-open rectangle.
Lower arithmetic boundary points are expressly excluded from the reverse lift. -/
theorem fibre_image_pair_projection (r : FullMask.Row) :
    (fun x : Fin 4 → ℝ => (x 0, x 1)) '' FullMask.support r =
      {y | y ∈ pairCell r ∧
        (tLower (FullMask.indices r).1 : ℝ) < y.1 ∧
        (uLower (FullMask.indices r).2 : ℝ) < y.2} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := (fibre_support_iff_pairCell r x).1 hx
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · rintro ⟨hy, ht, hu⟩
    exact ⟨liftPair r y, liftPair_mem_fibre r y hy ht hu, rfl⟩

/-- A full real history fibre supplies the pair-mask owner and the existing
rank-three ancestor owner, with the same original adopted row. -/
theorem history_fibre_projects_same_row (N : ℝ) {k : ℕ} (hk : 4 ≤ k)
    (history : List ℕ) (hlen : history.length = k) (r : FullMask.Row)
    (hmask : historicalPrefixProject hk (primeHistoryLogCoordinates N k history) ∈
      FullMask.support r) :
    historyPairCoordinates N history ∈ pairCell r ∧
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
        P1AdoptedMaskAncestors.Mask.ancestor3Support r := by
  constructor
  · rw [historyPairCoordinates_eq_rank N (by omega : 2 ≤ 4) history (by omega)]
    exact fibre_mem_pairCell
      (P1AdoptedMaskAncestors.history_ancestors_mem_same_row N hk history hlen r hmask).1
  · exact
      (P1AdoptedMaskAncestors.history_ancestors_mem_same_row N hk history hlen r hmask).2

theorem history_rank4_fibre_iff_pairCell (N : ℝ) (history : List ℕ)
    (hlen : 4 ≤ history.length) (r : FullMask.Row) :
    let x := primeHistoryLogCoordinates N 4 (rosserAncestor 4 history)
    x ∈ FullMask.support r ↔
      historyPairCoordinates N history ∈ pairCell r ∧
      (tLower (FullMask.indices r).1 : ℝ) < x 0 ∧
      (uLower (FullMask.indices r).2 : ℝ) < x 1 ∧
      (a : ℝ) < x 3 ∧ x 3 < x 2 ∧ x 2 < (FullMask.cutoff r : ℝ) := by
  dsimp only
  rw [historyPairCoordinates_eq_rank N (by omega : 2 ≤ 4) history hlen]
  exact fibre_support_iff_pairCell r _

/-- Literal pair history: no sorting of the values is performed. -/
theorem historyPairCoordinates_pair (N : ℝ) (p : ℕ × ℕ) :
    historyPairCoordinates N [p.1, p.2] = primePairCoordinates N p := by
  rfl

theorem historyDeletionMask_pair (N : ℝ) (p : ℕ × ℕ) :
    historyDeletionMask N [p.1, p.2] ↔ deletionMask N p := by
  rfl

/-- The full Chen tuple's last pair is exactly the earliest processing pair
of its literal reverse-stored history. -/
theorem historyPairCoordinates_fullChen (N : ℝ)
    (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    historyPairCoordinates N [p.1.1, p.1.2, p.2.1, p.2.2] =
      primePairCoordinates N p.2 := by
  rfl

theorem historyDeletionMask_fullChen (N : ℝ)
    (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    historyDeletionMask N [p.1.1, p.1.2, p.2.1, p.2.2] ↔ deletionMask N p.2 := by
  rfl

theorem selectedY6_history_dictionary (n : ℕ) (A H D N : ℝ) (p : ℕ × ℕ) :
    p ∈ chenY6SelectedTuples n A H D (deletionMask N) ↔
      p ∈ chenY6Tuples n A H D ∧ historyDeletionMask N [p.1, p.2] := by
  rw [mem_chenY6SelectedTuples, historyDeletionMask_pair]

theorem selectedY11_history_dictionary (n : ℕ) (A H D N : ℝ)
    (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    p ∈ chenY11SelectedTuples n A H D (deletionMask N) ↔
      p ∈ chenY11FullTuples n A H D ∧
        historyDeletionMask N [p.1.1, p.1.2, p.2.1, p.2.2] := by
  rw [mem_chenY11SelectedTuples, historyDeletionMask_fullChen]

/-- Later selected labels cannot alter actual Y11 mask membership. -/
theorem selectedY11_later_history_dictionary (n : ℕ) (A H D N : ℝ)
    (p : (ℕ × ℕ) × (ℕ × ℕ)) (later : List ℕ) :
    p ∈ chenY11SelectedTuples n A H D (deletionMask N) ↔
      p ∈ chenY11FullTuples n A H D ∧
        historyDeletionMask N (later ++ [p.1.1, p.1.2, p.2.1, p.2.2]) := by
  rw [historyDeletionMask_append N later _ (by simp), selectedY11_history_dictionary]

end

end ImbalancedChen.P1AdoptedPairMaskAncestorSupport
