import ImbalancedChen.ActualSelectedPrefixCapSelector
import ImbalancedChen.FirstExitHistoricalLevels
import ImbalancedChen.ActualRosserInitialResidualSaving
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Powerset

/-!
# Original saving 16: fourteen further ascending eighth cells

SOURCE ONLY; no compiler, producer, numerical replay, or runtime was run.

Frozen release sources, read as text:
* eighth-prefix-family-independent-20261009.py
  SHA256 d7cd61539cf51b924ddfb94dd63df3545f7353fbd021f4883627dceed44eb2ed;
* eighth-prefix-cell-independent-20261009.py, literal `semantics` and M
  SHA256 fc972c3ed33a0b0679c3373ef767b8443582821b6c12adafed848d3191935a35;
* eighth-prefix-family-20261009.tex
  SHA256 d8e63ef277a7d6ac9163283948445287b879c0c6134908950678bd053e2005a8.

The selected family is ascending cells 0,...,14 except 7; mask129 is the
physical subset {1,8}, not a sixth-node action.  Cell7 is already adopted
and is excluded by the producer.  No finite cell geometry is asserted here.

The old comparison is R=D(t2+t3)=L3=R6.  The new cap is the actual tent
minimum at t1+t8, minus 10^-6; on this ascending family it equals A-10^-6.
The actual causal parent can be smaller than R.  Its lower bound comes
from the retained seventh history H7<current, not from R-S8>t8.

This file proves real branch/support dictionaries, the actual quotient
residual comparison with coefficient 4, and a rank-eight frozen-frontier
identity against an inherited sixth cap.  There is no Chen quarter factor
and no factorial on the ordered physical domain.  Missing suppliers remain
the original fourteen complete cell data/geometry, a common finite old
policy realizing the required histories, its existing signed compiler,
and the aggregate integral enclosure.  No final saving is a premise.
-/

namespace ImbalancedChen.P2OriginalAscendingEighthCapDictionary

noncomputable section

open Set VariableEnvelope
open scoped Classical BigOperators

abbrev Point := Fin 8 → ℝ

def eta : ℝ := 1 / 1000000
def selected129 : Finset (Fin 8) := {0, 7}
def winner6 : Finset (Fin 6) := {1, 2}
def S (t : Point) : ℝ := ∑ i, t i
def d (t : Point) : ℝ := t 1 + t 2
def selectedSum (t : Point) : ℝ := t 0 + t 7
def R (t : Point) : ℝ := C (d t)
def M (t : Point) : ℝ := min (A (selectedSum t)) (C (selectedSum t)) - eta
def splitLeft (t : Point) : ℝ := 25 / 32 - 3 * d t

def prefixSum (t : Point) (j : Fin 8) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => i < j), t i

def fullSquare (t : Point) (j : Fin 8) : ℝ := prefixSum t j + 2 * t j
def oddCube (t : Point) (j : Fin 8) : ℝ := prefixSum t j + 3 * t j

/-- Once mask129 is selected, the remaining initial slots are t2,...,t7. -/
def selectedRemainingSquare (t : Point) (j : Fin 8) : ℝ :=
  selectedSum t + (∑ i ∈ Finset.univ.filter
    (fun i : Fin 8 => 0 < i ∧ i < j), t i) + 2 * t j

def subsetSum (t : Point) (I : Finset (Fin 6)) : ℝ :=
  ∑ i ∈ I, t ⟨i.val, by omega⟩

def oldMasks : Finset (Finset (Fin 6)) := Finset.univ.erase ∅

theorem winner6_mem : winner6 ∈ oldMasks := by
  simp [oldMasks, winner6]

theorem oldMasks_nonempty : oldMasks.Nonempty := ⟨winner6, winner6_mem⟩

/-- Literal all-63-subset old raw envelope, with its original W branch. -/
def rawSixthEnvelope (t : Point) : ℝ :=
  max (B (t 2)) (oldMasks.sup' oldMasks_nonempty (fun I => v (subsetSum t I)))

theorem selected129_sum (t : Point) : (∑ i ∈ selected129, t i) = selectedSum t := by
  norm_num [selected129, selectedSum]

theorem winner6_sum (t : Point) : subsetSum t winner6 = d t := by
  norm_num [subsetSum, winner6, d]

theorem new_cap_eq_tent (t : Point) : M t = v (selectedSum t) - eta := by
  rw [M, v_eq_min]

theorem new_cap_ascending (t : Point)
    (hhalf : A (selectedSum t) < C (selectedSum t)) :
    M t = (1 + t 0 + t 7) / 2 - 1 / 1000000 := by
  rw [M, min_eq_left hhalf.le]
  dsimp [A, selectedSum, eta]
  ring

theorem new_cap_strict_license (t : Point) : M t < v (∑ i ∈ selected129, t i) := by
  rw [selected129_sum, new_cap_eq_tent]
  dsimp [eta]
  linarith

theorem ascending_half_iff (t : Point) :
    A (selectedSum t) < C (selectedSum t) ↔ selectedSum t < mu := by
  dsimp [A, C, mu]
  constructor <;> intro h <;> linarith

/-- Exact old branch separation, including equality on either closed side. -/
theorem old_tent_below_R_iff (t : Point) (s : ℝ) :
    v s ≤ R t ↔ s ≤ splitLeft t ∨ d t ≤ s := by
  rw [v_eq_min, min_le_iff]
  dsimp [A, C, R, splitLeft]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

theorem old_branch_gap (t : Point) : d t - splitLeft t = 4 * (d t - mu) := by
  dsimp [splitLeft, mu]
  ring

theorem old_descending_iff (t : Point) : C (d t) < A (d t) ↔ mu < d t := by
  dsimp [C, A, mu]
  constructor <;> intro h <;> linarith

/-- Distinct branch assignments are disjoint whenever they disagree on a
subset: their gap is positive, rather than just a difference of labels. -/
theorem incompatible_old_branches (t : Point) (s : ℝ)
    (hd : mu < d t) (hleft : s ≤ splitLeft t) (hright : d t ≤ s) : False := by
  have hg := old_branch_gap t
  linarith

def chosenOldPlane (planes : Finset (Fin 6) → Bool) (t : Point)
    (I : Finset (Fin 6)) : ℝ :=
  if planes I then C (subsetSum t I) else A (subsetSum t I)

def OldPlaneRows (planes : Finset (Fin 6) → Bool) (t : Point) : Prop :=
  ∀ I ∈ oldMasks, chosenOldPlane planes t I ≤ R t

theorem old_tents_below_R (planes : Finset (Fin 6) → Bool) (t : Point)
    (hrows : OldPlaneRows planes t) (I : Finset (Fin 6)) (hI : I ∈ oldMasks) :
    v (subsetSum t I) ≤ R t := by
  rw [v_eq_min]
  have h := hrows I hI
  unfold chosenOldPlane at h
  split_ifs at h with hp
  · exact (min_le_right _ _).trans h
  · exact (min_le_left _ _).trans h

/-- All saved old-subset planes plus the actual descending winner prove
the raw envelope equality on the entire real cell. -/
theorem rawSixthEnvelope_eq_R (planes : Finset (Fin 6) → Bool) (t : Point)
    (hrows : OldPlaneRows planes t) (hdesc : C (d t) ≤ A (d t))
    (hW : B (t 2) ≤ R t) : rawSixthEnvelope t = R t := by
  have hwin : v (subsetSum t winner6) = R t := by
    rw [winner6_sum, v_eq_min, min_eq_right hdesc]
    rfl
  apply le_antisymm
  · exact max_le hW (Finset.sup'_le _ _ (old_tents_below_R planes t hrows))
  · have hl := Finset.le_sup' (fun I => v (subsetSum t I)) winner6_mem
    rw [hwin] at hl
    exact hl.trans (le_max_right _ _)

/-- The producer's real support conditions, with the two constant identities
kept as identities. The finite fourteen-cell geometry is a separate task. -/
structure CellGuard (planes : Finset (Fin 6) → Bool) (t : Point) : Prop where
  order : StrictAnti t
  last_pos : 0 < t 7
  largest : t 0 < mu
  third_activation : 1 / 100 < t 2
  compact_cutoff : 53 / 13824 < t 7
  first_history : 3 * t 0 < R t
  history3 : oddCube t 2 < R t
  history5 : oddCube t 4 < R t
  history7 : oddCube t 6 < R t
  old_descending : C (d t) < A (d t)
  old_W : B (t 2) < R t
  old_planes : OldPlaneRows planes t
  new_ascending : A (selectedSum t) < C (selectedSum t)
  improvement : R t < M t
  full_squares : ∀ j, fullSquare t j < M t
  selected_squares : ∀ j : Fin 8, 0 < j → j < 7 → selectedRemainingSquare t j < M t
  old_residual : S t + t 7 < R t
  new_residual : M t < S t + 3 * t 7

theorem CellGuard.rawSixth_eq {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) : rawSixthEnvelope t = R t :=
  rawSixthEnvelope_eq_R planes t h.old_planes h.old_descending.le h.old_W.le

/-- The third comparison is the existing gated original envelope. Its
equality with R is proved through the established ordered six-branch API. -/
theorem CellGuard.originalThird_eq {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) : VariableEnvelope.original (t 0) (t 1) (t 2) = R t := by
  have h0 : v (t 0) ≤ R t := by
    simpa [subsetSum] using old_tents_below_R planes t h.old_planes {0}
      (by simp [oldMasks])
  have h01 : v (t 0 + t 1) ≤ R t := by
    simpa [subsetSum] using old_tents_below_R planes t h.old_planes {0, 1}
      (by simp [oldMasks])
  have h012 : v (t 0 + t 1 + t 2) ≤ R t := by
    simpa [subsetSum, add_assoc] using old_tents_below_R planes t h.old_planes {0, 1, 2}
      (by simp [oldMasks])
  have h02 : v (t 0 + t 2) ≤ R t := by
    simpa [subsetSum] using old_tents_below_R planes t h.old_planes {0, 2}
      (by simp [oldMasks])
  have h12 : v (t 1 + t 2) = R t := by
    rw [v_eq_min, min_eq_right h.old_descending.le]
    rfl
  have h6 : six (t 0) (t 1) (t 2) = R t := by
    rw [six, h12]
    apply le_antisymm
    · exact max_le h0 (max_le h01 (max_le h012 (max_le h.old_W.le (max_le h02 le_rfl))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_right _ _))))
  have hordered : Ordered (t 0) (t 1) (t 2) :=
    ⟨(h.last_pos.trans (h.order (by decide : (2 : Fin 8) < 7))).le,
      (h.order (by decide : (1 : Fin 8) < 2)).le,
      (h.order (by decide : (0 : Fin 8) < 1)).le, h.largest.le⟩
  exact (original_eq_six hordered).trans h6

/-- A different complete old-branch pattern cannot share a point with the
same strict descending winner. This proves geometric separation of labels. -/
theorem CellGuard.incompatible_patterns
    {planes other : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) (ho : CellGuard other t)
    (I : Finset (Fin 6)) (hI : I ∈ oldMasks) (hdiff : planes I ≠ other I) : False := by
  have hleft := h.old_planes I hI
  have hright := ho.old_planes I hI
  have hdescending := h.old_descending
  cases hp : planes I <;> cases hq : other I <;>
    simp [chosenOldPlane, hp, hq] at hdiff hleft hright
  all_goals
    dsimp [A, C, R] at hleft hright hdescending
    linarith

/-- Exact physical square-gate dictionary, with no inverse coordinate map
or sampled vertex used to justify a support inequality. -/
theorem CellGuard.support_dictionary {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) :
    (∀ j, (∑ i ∈ Finset.univ.filter (fun i : Fin 8 => i < j), t i) + 2 * t j < M t) ∧
    (∀ j : Fin 8, 0 < j → j < 7 →
      (∑ i ∈ selected129, t i) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin 8 => 0 < i ∧ i < j), t i) +
          2 * t j < M t) ∧
      M t < v (∑ i ∈ selected129, t i) := by
  refine ⟨h.full_squares, ?_, new_cap_strict_license t⟩
  intro j hj0 hj7
  rw [selected129_sum]
  exact h.selected_squares j hj0 hj7

theorem seventh_history_minus_sum (t : Point) :
    oddCube t 6 - S t = 2 * t 6 - t 7 := by
  norm_num [oddCube, prefixSum, S, Finset.sum_filter, Fin.sum_univ_succ]
  <;> ring

/-- The actual inherited cap is controlled from below by retained history.
The upper comparison R by itself cannot supply this lower bound. -/
def CurrentParentGuard (t : Point) (current : ℝ) : Prop :=
  oddCube t 6 < current ∧ current ≤ R t

theorem residual_parameter_range {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) (current : ℝ) (hc : CurrentParentGuard t current) :
    0 < t 7 ∧ t 7 < current - S t ∧ current - S t ≤ 3 * t 7 ∧
      t 7 < M t - S t ∧ M t - S t ≤ 3 * t 7 := by
  have h76 : t 7 < t 6 := h.order (by decide : (6 : Fin 8) < 7)
  have hhist := seventh_history_minus_sum t
  rcases hc with ⟨hlo, hhi⟩
  refine ⟨h.last_pos, ?_, ?_, ?_, ?_⟩ <;>
    linarith [h.improvement, h.new_residual]

def sourceGain (old new : ℝ) (t : Point) : ℝ :=
  4 * (new - old) / ((old - S t) * (new - S t))

/-- Original density normalization: coefficient 4, with one physical
reciprocal-coordinate factor for each of the eight ordered slots. -/
def sourceDensity (t : Point) : ℝ :=
  4 * (M t - R t) / ((R t - S t) * (M t - S t) * ∏ i, t i)

theorem sourceDensity_eq (t : Point) :
    sourceDensity t = sourceGain (R t) (M t) t / (∏ i, t i) := by
  simp only [sourceDensity, sourceGain, div_div]

theorem CellGuard.coordinate_pos {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) (i : Fin 8) : 0 < t i := by
  by_cases hi : i = 7
  · simpa only [hi] using h.last_pos
  · have hi7 : i < 7 := by omega
    exact h.last_pos.trans (h.order hi7)

theorem CellGuard.density_pos {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) : 0 < sourceDensity t := by
  have hgap : 0 < M t - R t := sub_pos.mpr h.improvement
  have hR : 0 < R t - S t := by linarith [h.last_pos, h.old_residual]
  have hM : 0 < M t - S t := by linarith [h.improvement]
  have hprod : 0 < ∏ i, t i := Finset.prod_pos (fun i _hi => h.coordinate_pos i)
  unfold sourceDensity
  positivity

theorem sourceGain_eq_difference (old new : ℝ) (t : Point)
    (ho : 0 < old - S t) (hn : 0 < new - S t) :
    sourceGain old new t = 4 / (old - S t) - 4 / (new - S t) := by
  unfold sourceGain
  field_simp [ho.ne', hn.ne'] <;> ring

theorem comparison_gain_le_current {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) (current : ℝ) (hc : CurrentParentGuard t current) :
    sourceGain (R t) (M t) t ≤ sourceGain current (M t) t := by
  have hp := residual_parameter_range h current hc
  have hcur : 0 < current - S t := hp.1.trans hp.2.1
  have hR : 0 < R t - S t := by linarith [h.last_pos, h.old_residual]
  have hM : 0 < M t - S t := hp.1.trans hp.2.2.2.1
  have hi := one_div_le_one_div_of_le hcur (sub_le_sub_right hc.2 (S t))
  have h4 : 4 / (R t - S t) ≤ 4 / (current - S t) := by
    convert mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring
  rw [sourceGain_eq_difference _ _ t hR hM, sourceGain_eq_difference _ _ t hcur hM]
  exact sub_le_sub_right h4 _

/-- A noncircular pointwise theorem for the actual real quotient residuals.
The uniform threshold comes from the existing two-sided actual density
limit; no finite coefficient monotonicity or integrated gain is assumed. -/
theorem exists_actual_eighth_increment_threshold
    {planes : Finset (Fin 6) → Bool} {t : Point} (h : CellGuard planes t)
    (current : ℝ) (hc : CurrentParentGuard t current)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y : ℝ, 0 < P → 0 < y →
        Real.log P / Real.log (N : ℝ) = S t →
        Real.log y / Real.log (N : ℝ) = t 7 →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          sourceGain (R t) (M t) t - epsilon <
            (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ current / P) -
              actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ M t / P)) *
                Real.log (N : ℝ) / singularSeries N := by
  let T : Set (ℝ × ℝ) := {(current - S t, t 7)} ∪ {(M t - S t, t 7)}
  have hT : IsCompact T := isCompact_singleton.union isCompact_singleton
  have hp := residual_parameter_range h current hc
  have hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2 := by
    intro p hpT
    rcases hpT with hpT | hpT
    · have heq := Set.mem_singleton_iff.mp hpT
      subst p
      exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
    · have heq := Set.mem_singleton_iff.mp hpT
      subst p
      exact ⟨hp.1, hp.2.2.2.1, hp.2.2.2.2⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_quotient_saving_threshold T hT hparam epsilon hepsilon
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y hP hy hlogP hlogy cap hcap
  have hOld : actualRosserQuotientParameters (N : ℝ) P y current ∈ T := by
    simp only [actualRosserQuotientParameters, hlogP, hlogy]
    exact Or.inl (Set.mem_singleton _)
  have hNew : actualRosserQuotientParameters (N : ℝ) P y (M t) ∈ T := by
    simp only [actualRosserQuotientParameters, hlogP, hlogy]
    exact Or.inr (Set.mem_singleton _)
  have hb := abs_lt.mp (hbound N hN hEven P y current (M t) hP hy hOld hNew cap hcap)
  rw [hlogP] at hb
  have hcomparison := comparison_gain_le_current h current hc
  unfold sourceGain at hcomparison ⊢
  linarith [hb.1]

/-- The current cap is frozen at its sixth ancestor. It can contain all
already adopted causal sixth actions and is never replaced by R itself. -/
def inheritedExponent (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  lambda6 (rosserAncestor 6 history)

def currentLevel (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  N ^ inheritedExponent lambda6 history

/-- A real geometric action is taken after all eight labels are observed.
Outside it the actual current action is retained, including equality faces. -/
def actionGuard (planes : Finset (Fin 6) → Bool) (t : Point) (current : ℝ) : Prop :=
  CellGuard planes t ∧ CurrentParentGuard t current

def nextExponent (N : ℝ) (lambda6 : List ℕ → ℝ)
    (planes : Finset (Fin 6) → Bool) (history : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates N 8 history
  if actionGuard planes t (inheritedExponent lambda6 history) then M t
  else inheritedExponent lambda6 history

def nextLevel (N : ℝ) (lambda6 : List ℕ → ℝ)
    (planes : Finset (Fin 6) → Bool) (history : List ℕ) : ℝ :=
  N ^ nextExponent N lambda6 planes history

theorem currentExponent_le_next (N : ℝ) (lambda6 : List ℕ → ℝ)
    (planes : Finset (Fin 6) → Bool) (history : List ℕ) :
    inheritedExponent lambda6 history ≤ nextExponent N lambda6 planes history := by
  unfold nextExponent
  dsimp only
  split_ifs with h
  · exact h.2.2.trans h.1.improvement.le
  · exact le_rfl

theorem currentLevel_le_next (N : ℝ) (hN : 1 ≤ N) (lambda6 : List ℕ → ℝ)
    (planes : Finset (Fin 6) → Bool) (history : List ℕ) :
    currentLevel N lambda6 history ≤ nextLevel N lambda6 planes history := by
  exact Real.rpow_le_rpow_of_exponent_le hN (currentExponent_le_next N lambda6 planes history)

def sourcePolicy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (planes : Finset (Fin 6) → Bool) (parent : Bool → List ℕ → Bool) :
    Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 parent
    (frozenParityRosserPolicy false 8 (nextLevel N lambda6 planes))

theorem sourcePolicy_frontier_eight (N : ℝ) (lambda6 : List ℕ → ℝ)
    (planes : Finset (Fin 6) → Bool) (parent : Bool → List ℕ → Bool)
    (weight : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (sourcePolicy N lambda6 planes parent)
        weight pre positive mass carrier =
      firstExitDepthFrontier 8 parent weight pre positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 8 8 le_rfl parent _ weight pre carrier positive mass

/-- Rank eight is an even positive coefficient and its remaining ordinary
residual is upper. This is a literal definition-level identity. -/
theorem actual_rank_eight_density (N cap : ℕ) (Q : List ℕ → ℝ) (pre : List ℕ)
    (hlen : pre.length = 8) :
    actualFrozenFrontierDensityTerm false N cap Q pre =
      ((pre.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod) *
        actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ) (Q pre / (pre.prod : ℝ)) := by
  unfold actualFrozenFrontierDensityTerm
  rw [signedTreeCoefficient_evenListLength_eq_negOnePow, hlen]
  norm_num [ordinaryRosserResidualLower]

/-- The product exponent and the last selected cutoff are the actual
history coordinates, with no independent quotient parameters invented. -/
theorem rank_eight_log_dictionary (N : ℝ) (hN : 1 < N) (pre : List ℕ)
    (hlen : pre.length = 8) (hpos : ∀ p ∈ pre, 0 < p) :
    S (primeHistoryLogCoordinates N 8 pre) = Real.log (pre.prod : ℝ) / Real.log N ∧
      primeHistoryLogCoordinates N 8 pre 7 = Real.log (pre.headD 0 : ℝ) / Real.log N := by
  constructor
  · exact sum_primeHistoryLogCoordinates N hN hlen hpos
  · change Real.log (primeHistoryTuple 8 pre (Fin.last 7) : ℝ) / Real.log N = _
    rw [primeHistoryTuple_last hlen]

/-- The exact rank-eight residual integrand on a real prime history. -/
def actualEighthResidualDifference (N cap : ℕ) (Qold Qnew : List ℕ → ℝ)
    (pre : List ℕ) : ℝ :=
  ((pre.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod) *
    (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ) (Qold pre / (pre.prod : ℝ)) -
      actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ) (Qnew pre / (pre.prod : ℝ)))

theorem actual_rank_eight_difference (N cap : ℕ) (Qold Qnew : List ℕ → ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) :
    actualFrozenFrontierDensityTerm false N cap Qold pre -
        actualFrozenFrontierDensityTerm false N cap Qnew pre =
      actualEighthResidualDifference N cap Qold Qnew pre := by
  rw [actual_rank_eight_density N cap Qold pre hlen,
    actual_rank_eight_density N cap Qnew pre hlen]
  exact (mul_sub _ _ _).symm

/-- Frontier membership itself supplies the rank used in the upper residual
dictionary; no independent tuple length or coefficient sign is assumed. -/
theorem actual_frontier_eighth_difference (N cap : ℕ) (z : ℝ)
    (parent : Bool → List ℕ → Bool) (Qold Qnew : List ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 8 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)) :
    actualFrozenFrontierDensityTerm false N cap Qold state.selectedPrefix -
        actualFrozenFrontierDensityTerm false N cap Qnew state.selectedPrefix =
      actualEighthResidualDifference N cap Qold Qnew state.selectedPrefix := by
  have hlen := firstExitDepthFrontier_selected_length 8 parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1
    (by simp) state hstate
  exact actual_rank_eight_difference N cap Qold Qnew state.selectedPrefix hlen

/-- Exact finite same-parent identity, with all current sixth decisions
still inherited. Old prefix admission is a genuine finite-policy input;
new admission follows from the proved cap increase. -/
theorem actual_eighth_source_splice_saving (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ)
    (lambda6 : List ℕ → ℝ) (planes : Finset (Fin 6) → Bool)
    (parent : Bool → List ℕ → Bool)
    (hold : ∀ state ∈ firstExitDepthFrontier 8 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ordinaryRosserPrefixAdmissible false (currentLevel (N : ℝ) lambda6 state.selectedPrefix)
        state.selectedPrefix) :
    firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy 8 parent
          (frozenParityRosserPolicy false 8 (currentLevel (N : ℝ) lambda6)))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (sourcePolicy (N : ℝ) lambda6 planes parent)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      ((firstExitDepthFrontier 8 parent (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 z)).map (fun state =>
          actualFrozenFrontierDensityTerm false N cap (currentLevel (N : ℝ) lambda6)
              state.selectedPrefix -
            actualFrozenFrontierDensityTerm false N cap (nextLevel (N : ℝ) lambda6 planes)
              state.selectedPrefix)).sum := by
  apply firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum false 8 (by omega)
    parent (nextLevel (N : ℝ) lambda6 planes) (currentLevel (N : ℝ) lambda6) N cap z
  · intro state hstate
    exact ordinaryRosserPrefixAdmissible_mono false state.selectedPrefix
      (currentLevel_le_next (N : ℝ) hN lambda6 planes state.selectedPrefix) (hold state hstate)
  · exact hold

/-- The fourteen selected identifiers, explicitly excluding the adopted
ascending pattern 7. Their saved pattern maps remain a separate supplier. -/
def selectedCellIndices : Finset (Fin 15) := Finset.univ.erase 7

theorem mem_selectedCellIndices (i : Fin 15) : i ∈ selectedCellIndices ↔ i ≠ 7 := by
  simp [selectedCellIndices]

def SelectedFamilyGuard (patterns : Fin 15 → Finset (Fin 6) → Bool) (t : Point) : Prop :=
  ∃ i ∈ selectedCellIndices, CellGuard (patterns i) t

theorem SelectedFamilyGuard.adopted_excluded
    {patterns : Fin 15 → Finset (Fin 6) → Bool} {t : Point}
    (h : SelectedFamilyGuard patterns t) :
    ∃ i : Fin 15, i ≠ 7 ∧ CellGuard (patterns i) t := by
  rcases h with ⟨i, hi, ht⟩
  exact ⟨i, (mem_selectedCellIndices i).mp hi, ht⟩

/-- A single existential selector takes the common new mask129 cap once;
it does not sum a contribution for every label that happens to contain t. -/
def familyNextExponent (N : ℝ) (lambda6 : List ℕ → ℝ)
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (history : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates N 8 history
  if SelectedFamilyGuard patterns t ∧ CurrentParentGuard t (inheritedExponent lambda6 history)
    then M t else inheritedExponent lambda6 history

def familyNextLevel (N : ℝ) (lambda6 : List ℕ → ℝ)
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (history : List ℕ) : ℝ :=
  N ^ familyNextExponent N lambda6 patterns history

theorem currentLevel_le_familyNext (N : ℝ) (hN : 1 ≤ N) (lambda6 : List ℕ → ℝ)
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (history : List ℕ) :
    currentLevel N lambda6 history ≤ familyNextLevel N lambda6 patterns history := by
  apply Real.rpow_le_rpow_of_exponent_le hN
  unfold familyNextExponent
  dsimp only
  split_ifs with h
  · obtain ⟨i, _hi, ht⟩ := h.1
    exact h.2.2.trans ht.improvement.le
  · exact le_rfl

def familySourcePolicy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (parent : Bool → List ℕ → Bool) :
    Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 parent
    (frozenParityRosserPolicy false 8 (familyNextLevel N lambda6 patterns))

/-- The literal fourteen-cell union adapter on the same actual rank-eight
frontier. The cap increase proves new admission from old admission. -/
theorem actual_fourteen_family_splice_saving
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ)
    (lambda6 : List ℕ → ℝ) (patterns : Fin 15 → Finset (Fin 6) → Bool)
    (parent : Bool → List ℕ → Bool)
    (hold : ∀ state ∈ firstExitDepthFrontier 8 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ordinaryRosserPrefixAdmissible false (currentLevel (N : ℝ) lambda6 state.selectedPrefix)
        state.selectedPrefix) :
    firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy 8 parent
          (frozenParityRosserPolicy false 8 (currentLevel (N : ℝ) lambda6)))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (familySourcePolicy (N : ℝ) lambda6 patterns parent)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      ((firstExitDepthFrontier 8 parent (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 z)).map (fun state =>
          actualEighthResidualDifference N cap (currentLevel (N : ℝ) lambda6)
            (familyNextLevel (N : ℝ) lambda6 patterns) state.selectedPrefix)).sum := by
  have hfinite := firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum
    false 8 (by omega) parent (familyNextLevel (N : ℝ) lambda6 patterns)
    (currentLevel (N : ℝ) lambda6) N cap z
    (fun state hstate => ordinaryRosserPrefixAdmissible_mono false state.selectedPrefix
      (currentLevel_le_familyNext (N : ℝ) hN lambda6 patterns state.selectedPrefix)
      (hold state hstate)) hold
  unfold familySourcePolicy
  rw [hfinite]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  exact actual_frontier_eighth_difference N cap z parent _ _ state hstate

end

end ImbalancedChen.P2OriginalAscendingEighthCapDictionary
