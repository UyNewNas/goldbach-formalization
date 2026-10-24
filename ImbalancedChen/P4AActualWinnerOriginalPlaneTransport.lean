import ImbalancedChen.ActualExtendedThirdWholeCellActions
import ImbalancedChen.ActualThirdOriginalSixTentCandidates

/-!
SOURCE_WRITTEN / UNCOMPILED / MAIN OPEN30.

Transport the actual Fin8 least winner to the original ordinary leaf's
`TentSum`, `TentSide`, `sourceActive`, `tentPlane`, and `ClosedCutTree` APIs.
The actual coarse policy and the numerical minorant chooser have DIFFERENT
selection criteria. This file never identifies those two selectors. It proves
the useful common pointwise constraints on every descendant closed leaf.
Original rise-first equality and fall-after-failure are retained literally.
-/
namespace ImbalancedChen.P4AActualWinnerOriginalPlaneTransportSourceOnly

noncomputable section
open Set VariableEnvelope
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdBoxMomentsSourceOnly

/-- The original source sum enumeration is x,y,xy,xz,yz,xyz; the physical
coarse winner enumeration is x,y,xy,xyz,Wxyz,Wxzy,xz,yz. -/
def actualTentIndex : TentSum → Fin 8
  | .x => 0 | .y => 1 | .xy => 2 | .xz => 6 | .yz => 7 | .xyz => 3

/-- Reuse the already proved least winner. Pair fallback values are removed
only by its actual gate theorem, not by an ungated-envelope replacement. -/
theorem actual_winning_tent_candidate (s : TentSum) {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hk : actualExtendedThirdLeastWinningIndex e m j = actualTentIndex s) :
    actualExtendedThirdRobustCandidate e m j (actualTentIndex s) =
      actualExtendedThirdCellInf m j (fun t => v (tentSum s t)) := by
  cases s with
  | x => simp [actualTentIndex, actualExtendedThirdRobustCandidate,
      actualExtendedThirdRobustBaseBranch, tentSum, sumX, sumY, sumZ]
  | y => simp [actualTentIndex, actualExtendedThirdRobustCandidate,
      actualExtendedThirdRobustBaseBranch, tentSum, sumX, sumY, sumZ]
  | xy => simp [actualTentIndex, actualExtendedThirdRobustCandidate,
      actualExtendedThirdRobustBaseBranch, tentSum, sumX, sumY, sumZ]
  | xyz => simp [actualTentIndex, actualExtendedThirdRobustCandidate,
      actualExtendedThirdRobustBaseBranch, tentSum, sumX, sumY, sumZ]
  | xz =>
      have hg := actualExtendedThirdLeastWinningIndex_pairXZ_gate hk
      simp [actualTentIndex, actualExtendedThirdRobustCandidate, hg,
        actualExtendedThirdPairXZ, tentSum, sumX, sumY, sumZ]
  | yz =>
      have hg := actualExtendedThirdLeastWinningIndex_pairYZ_gate hk
      simp [actualTentIndex, actualExtendedThirdRobustCandidate, hg,
        actualExtendedThirdPairYZ, tentSum, sumX, sumY, sumZ]

theorem actual_winning_tent_pointwise (s : TentSum) {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hk : actualExtendedThirdLeastWinningIndex e m j = actualTentIndex s)
    {t : BoxPoint} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdBaseParameter e m j + e ≤ v (tentSum s t) := by
  have hc : Continuous (fun u : BoxPoint => v (tentSum s u)) := by
    apply continuous_v.comp
    cases s <;> unfold tentSum sumX sumY sumZ <;> fun_prop
  have hi := actualExtendedThirdCellInf_le hc ht
  rw [← actual_winning_tent_candidate s hk, ← hk,
    ← actualExtendedThirdFullGamma_eq_leastWinningValue] at hi
  unfold actualExtendedThirdBaseParameter
  linarith

/-- The source's actual active minimum plane bounds the actual selected
coarse parameter, on the full intersection with the original source box. -/
theorem actual_winner_le_original_active_plane
    (s : TentSum) (side : TentSide) (a b : BoxPoint)
    {e : ℝ} {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (hk : actualExtendedThirdLeastWinningIndex e m j = actualTentIndex s)
    (ha : sourceActive s side a b) {t : BoxPoint}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) (hbox : t ∈ Icc a b) :
    actualExtendedThirdBaseParameter e m j + e ≤ tentPlane s side t := by
  rw [active_plane_eq_v s side a b ha hbox]
  exact actual_winning_tent_pointwise s hk ht

/-- Equality of the source's upper delta belongs to the first `if` arm. -/
theorem original_min_tie_is_rise (s : TentSum) (a b : BoxPoint)
    (h : sourceDelta s b = 0) :
    sourceActive s .rise a b ∧ ¬ sourceActive s .fall a b := by
  simp [sourceActive, h]

theorem original_active_sides_exclusive (s : TentSum) (a b : BoxPoint)
    (h : sourceActive s .rise a b) : ¬ sourceActive s .fall a b := by
  exact fun hf => hf.1 h

/-- A crossing leaf has no whole-box active tent plane. A future serialized
tree must split it or select a different legitimate candidate. -/
theorem original_crossing_has_no_active_side (s : TentSum) (a b : BoxPoint)
    (hl : sourceDelta s a < 0) (hu : 0 < sourceDelta s b) (side : TentSide) :
    ¬ sourceActive s side a b := by
  cases side <;> simp only [sourceActive] <;> intro h
  · linarith
  · linarith [h.2]

/-- This is the original closed-cut tree, with its original DEN unchanged.
Every child leaf is a subset of its actual root; ordering-wall points stay. -/
theorem mem_closedLeaves_subset (tree : ClosedCutTree) (root leaf : Set Point)
    (h : leaf ∈ closedLeaves tree root) : leaf ⊆ root := by
  induction tree generalizing root leaf with
  | leaf =>
      simp only [closedLeaves, List.mem_singleton] at h
      subst leaf
      exact Subset.rfl
  | split axis cut left right ihL ihR =>
      change leaf ∈ closedLeaves left
        (root ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}) ++
        closedLeaves right
        (root ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis}) at h
      rcases List.mem_append.mp h with h | h
      · exact (ihL _ _ h).trans inter_subset_left
      · exact (ihR _ _ h).trans inter_subset_left

/-- Actual selected action level reaches each original active affine plane
on a descendant leaf. This consumes genuine source tests and actual coarse
membership, and accepts no cap inequality or K target as a premise. -/
theorem actual_winner_active_plane_on_closed_leaf
    (tree : ClosedCutTree) (s : TentSum) (side : TentSide) (a b : BoxPoint)
    {e : ℝ} {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (hk : actualExtendedThirdLeastWinningIndex e m j = actualTentIndex s)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    (hactive : sourceActive s side a b) {leaf : Set Point}
    (hleaf : leaf ∈ closedLeaves tree (actualExtendedThirdPhysicalCell m j ∩ Icc a b))
    {t : Point} (ht : t ∈ leaf) :
    actualExtendedThirdPhysicalLevel e m j + e ≤ actualExtendedThirdBaseParameter e m j ∧
      actualExtendedThirdBaseParameter e m j + e ≤ tentPlane s side t := by
  have hp := mem_closedLeaves_subset tree _ leaf hleaf ht
  exact ⟨actualExtendedThirdBaseParameter_above_level hfull,
    actual_winner_le_original_active_plane s side a b hk hactive hp.1 hp.2⟩

/-- The actual nonleading-pair action keeps its original chosen parameter;
its whole-cell upper license is exactly the active original tent plane. -/
theorem actual_selected_pair_le_original_active_plane
    (side : TentSide) (a b : BoxPoint)
    {e : ℝ} {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : BoxPoint} (ht : t ∈ actualExtendedThirdPhysicalCell m j) (yz : Bool)
    (hk : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6)
    (ha : sourceActive (if yz then TentSum.yz else TentSum.xz) side a b)
    {u : BoxPoint} (hu : u ∈ actualExtendedThirdPhysicalCell m j) (hb : u ∈ Icc a b) :
    actualExtendedThirdPairParameter e m j t yz + e / 4 ≤
      tentPlane (if yz then TentSum.yz else TentSum.xz) side u := by
  have haction := actualExtendedThirdSelectedPair_wholeCell he0 he hmesh hfull ht yz hk
  have hp := (haction.2.2.2 u hu).2
  rw [active_plane_eq_v _ side a b ha hb]
  cases yz <;> simpa [tentSum, sumX, sumY, sumZ] using hp

/-- The close rescue arm really uses the baseline parameter. Its comparison
with the source x-plane does not pretend that index 4 or 5 is index zero. -/
theorem actual_selected_close_rescue_le_original_x_plane
    (side : TentSide) (a b : BoxPoint)
    {e : ℝ} {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : BoxPoint} (ht : t ∈ actualExtendedThirdPhysicalCell m j) (swapped : Bool)
    (hk : actualExtendedThirdLeastWinningIndex e m j = if swapped then 5 else 4)
    (hclose :
      (if swapped then wInner (t 0) (t 2) (t 1) else wInner (t 0) (t 1) (t 2)) - v (t 0) ≤ e / 4)
    (ha : sourceActive .x side a b)
    {u : BoxPoint} (hu : u ∈ actualExtendedThirdPhysicalCell m j) (hb : u ∈ Icc a b) :
    actualExtendedThirdBaseParameter e m j + e / 2 ≤ tentPlane .x side u := by
  have haction := actualExtendedThirdSelectedRescue_wholeCell he0 he hmesh hfull ht swapped hk
  rcases haction with hbase | hrescue
  · rw [active_plane_eq_v .x side a b ha hb]
    simpa [tentSum, sumX, sumY, sumZ] using hbase.2.2.2.2 u hu
  · exact False.elim ((not_lt_of_ge hclose) hrescue.1)

/-- Rescue minima really are the original B planes below mu. This pays the
two discarded minimum inequalities through wInner_eq_B; it is not a new
assumption asserting that a rescue winner equals a numerical leaf winner. -/
theorem actual_rescue_minimum_eq_original_B {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he : 0 ≤ e)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : BoxPoint} (ht : t ∈ actualExtendedThirdPhysicalCell m j) (swapped : Bool) :
    (if swapped then wInner (t 0) (t 2) (t 1) else wInner (t 0) (t 1) (t 2)) =
      B (if swapped then t 1 else t 2) := by
  have hx : t 0 ≤ mu := by linarith [(ht.1 0 (mem_univ _)).2]
  have hy : t 1 ≤ mu := ht.2.2.2.trans hx
  have hz : t 2 ≤ mu := ht.2.2.1.trans hy
  cases swapped
  · exact wInner_eq_B (t 0) hy ht.2.1
  · exact wInner_eq_B (t 0) hz (ht.2.1.trans ht.2.2.1)

/-- For the actual selected rescue action, the positive-surplus arm has a
uniform margin below B(z), the literal first candidate in original minorant.
Both unswapped B(z) and swapped B(y) actions retain their original parameter. -/
theorem actual_selected_rescue_le_original_B
    {e : ℝ} {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : BoxPoint} (ht : t ∈ actualExtendedThirdPhysicalCell m j) (swapped : Bool)
    (hk : actualExtendedThirdLeastWinningIndex e m j = if swapped then 5 else 4)
    (hgap : e / 4 <
      (if swapped then wInner (t 0) (t 2) (t 1) else wInner (t 0) (t 1) (t 2)) - v (t 0))
    {u : BoxPoint} (hu : u ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdRescueParameter e m j t + e / 16 ≤ B (u 2) := by
  have haction := actualExtendedThirdSelectedRescue_wholeCell he0 he hmesh hfull ht swapped hk
  rcases haction with hclose | hrescue
  · exact False.elim ((not_lt_of_ge hclose.1) hgap)
  · have hr := (hrescue.2.2.2.2 u hu).2
    rw [actual_rescue_minimum_eq_original_B he0.le hfull hu swapped] at hr
    have hB : B (if swapped then u 1 else u 2) ≤ B (u 2) := by
      cases swapped
      · exact le_rfl
      · dsimp [B]; linarith [hu.2.2.1]
    exact hr.trans hB

end
end ImbalancedChen.P4AActualWinnerOriginalPlaneTransportSourceOnly
