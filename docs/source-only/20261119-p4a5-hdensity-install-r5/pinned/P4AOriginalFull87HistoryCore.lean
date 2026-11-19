import ImbalancedChen.P4AOriginalFull87SourceDictionary
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

A single compact history carrier for ALL original87 sources. It trims only
positive history/order margins; it does not test a future prime, replace
Source by a physical witness, or discard an original source permanently.
Every point of every exact original Source eventually lies in these cores.
The intersection with a strict Source is not asserted to be compact: the
compact object is the common history carrier itself. Full switching-wall
and finite cap approximation remain separate obligations.
-/
namespace ImbalancedChen.P4AOriginalFull87HistoryCore
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope P4AOriginalFull87SourceDictionary

abbrev oldHistory := P4AOriginalRemainingEighthSources.history

def thirdValue (t : Point) : ℝ := six (t 0) (t 1) (t 2)

def slack (t : Point) : Fin 7 → ℝ :=
  ![mu - t 0, t 0 - t 1, t 1 - t 2,
    thirdValue t - oldHistory t 0, thirdValue t - oldHistory t 1,
    thirdValue t - oldHistory t 2, thirdValue t - oldHistory t 3]

theorem thirdValue_continuous : Continuous thirdValue := by
  unfold thirdValue six v A B C
  fun_prop

theorem oldHistory_continuous (j : Fin 4) : Continuous (fun t : Point => oldHistory t j) := by
  fin_cases j <;> dsimp [oldHistory, P4AOriginalRemainingEighthSources.history] <;> fun_prop

theorem slack_continuous (j : Fin 7) : Continuous (fun t : Point => slack t j) := by
  fin_cases j
  all_goals dsimp only [slack, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first | fun_prop | exact thirdValue_continuous.sub (oldHistory_continuous _)

/-- The compact carrier is independent of c, q, N, and all prime labels. -/
def core (delta : ℝ) : Set Point :=
  Icc (fun _ => (0 : ℝ)) (fun _ => mu) ∩
    ⋂ j : Fin 7, {t | delta ≤ slack t j}

theorem mem_core (delta : ℝ) (t : Point) :
    t ∈ core delta ↔
      (∀ i, 0 ≤ t i) ∧ (∀ i, t i ≤ mu) ∧ (∀ j, delta ≤ slack t j) := by
  simp only [core, mem_inter_iff, mem_Icc, Pi.le_def, mem_iInter, mem_setOf_eq,
    and_assoc]

theorem isClosed_core (delta : ℝ) : IsClosed (core delta) :=
  isClosed_Icc.inter (isClosed_iInter fun j => isClosed_le continuous_const (slack_continuous j))

theorem isCompact_core (delta : ℝ) : IsCompact (core delta) :=
  isCompact_Icc.of_isClosed_subset (isClosed_core delta) (fun _ ht => ht.1)

theorem core_antitone {delta eta : ℝ} (hle : delta ≤ eta) : core eta ⊆ core delta := by
  intro t ht
  obtain ⟨hlo, hup, hs⟩ := (mem_core eta t).mp ht
  exact (mem_core delta t).mpr ⟨hlo, hup, fun j => hle.trans (hs j)⟩

theorem core_margins {delta : ℝ} {t : Point} (ht : t ∈ core delta) :
    delta ≤ mu - t 0 ∧ delta ≤ t 0 - t 1 ∧ delta ≤ t 1 - t 2 ∧
      ∀ j : Fin 4, delta ≤ thirdValue t - oldHistory t j := by
  have hs := ((mem_core delta t).mp ht).2.2
  refine ⟨by simpa [slack] using hs 0, by simpa [slack] using hs 1,
    by simpa [slack] using hs 2, ?_⟩
  intro j
  fin_cases j
  · simpa [slack] using hs 3
  · simpa [slack] using hs 4
  · simpa [slack] using hs 5
  · simpa [slack] using hs 6

/-- The old ideal cap is only used to DERIVE the strict six-envelope
margin from original rows; it is not substituted for the finite lookup. -/
theorem source_history_lt_thirdValue {c : Cell} {t : Point} (hs : Source c t)
    (j : Fin 4) : oldHistory t j < thirdValue t := by
  have h := source_histories_original_ideal hs j
  have ho := source_ordered hs
  have hi : actualExtendedThirdIdealCap (t 0) (t 1) (t 2) ≤ thirdValue t := by
    rw [actualExtendedThirdIdealCap_eq, if_pos ho.2.2.2, original_eq_six ho]
    exact min_le_right _ _
  exact h.trans_le hi

theorem source_slack_pos {c : Cell} {t : Point} (hs : Source c t) :
    ∀ j : Fin 7, 0 < slack t j := by
  obtain ⟨hx, hz, hr, ho⟩ := source_basic hs
  have h0 := source_history_lt_thirdValue hs (0 : Fin 4)
  have h1 := source_history_lt_thirdValue hs (1 : Fin 4)
  have h2 := source_history_lt_thirdValue hs (2 : Fin 4)
  have h3 := source_history_lt_thirdValue hs (3 : Fin 4)
  intro j
  fin_cases j <;> simp only [slack, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first | exact sub_pos.mpr hx | exact sub_pos.mpr (ho 0) |
    exact sub_pos.mpr (ho 1) | exact sub_pos.mpr h0 | exact sub_pos.mpr h1 |
    exact sub_pos.mpr h2 | exact sub_pos.mpr h3

theorem source_in_cube {c : Cell} {t : Point} (hs : Source c t) :
    (∀ i, 0 ≤ t i) ∧ (∀ i, t i ≤ mu) := by
  obtain ⟨hx, hz, hr, ho⟩ := source_basic hs
  have ha : StrictAnti t := Fin.strictAnti_iff_succ_lt.mpr ho
  constructor
  · intro i
    have hi : t 7 ≤ t i := ha.antitone (by have := i.isLt; omega)
    linarith
  · intro i
    exact (ha.antitone (Fin.zero_le i)).trans hx.le

/-- Existence of a real positive margin, derived separately for every
actual source point; no claim of uniformity on the untrimmed open union. -/
theorem source_mem_some_core {c : Cell} {t : Point} (hs : Source c t) :
    ∃ delta : ℝ, 0 < delta ∧ t ∈ core delta := by
  have hp := source_slack_pos hs
  let delta : ℝ := min (slack t 0) (min (slack t 1) (min (slack t 2)
    (min (slack t 3) (min (slack t 4) (min (slack t 5) (slack t 6))))))
  have hd : 0 < delta := by
    dsimp [delta]
    exact lt_min (hp 0) (lt_min (hp 1) (lt_min (hp 2)
      (lt_min (hp 3) (lt_min (hp 4) (lt_min (hp 5) (hp 6))))))
  obtain ⟨hlo, hup⟩ := source_in_cube hs
  refine ⟨delta, hd, (mem_core delta t).mpr ⟨hlo, hup, ?_⟩⟩
  intro j
  fin_cases j <;> dsimp [delta] <;> simp

/-- Explicit refinement scale; no source family chooses its own N. -/
def width (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem width_pos (n : ℕ) : 0 < width n := by unfold width; positivity

theorem width_tendsto : Tendsto width atTop (nhds 0) := by
  simpa only [width] using
    (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.add_const (1 : ℝ)) :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0))

/-- Every original source point, including one arbitrarily near a proper
wall, is eventually retained. No source-domain measure or saving is input. -/
theorem source_eventually_in_core {c : Cell} {t : Point} (hs : Source c t) :
    ∀ᶠ n : ℕ in atTop, t ∈ core (width n) := by
  obtain ⟨delta, hd, ht⟩ := source_mem_some_core hs
  filter_upwards [width_tendsto.eventually (gt_mem_nhds hd)] with n hn
  exact core_antitone hn.le ht

/-- Source membership remains literal; the trim never creates new labels. -/
def retained (c : Cell) (delta : ℝ) : Set Point := {t | Source c t} ∩ core delta

theorem retained_subset_source (c : Cell) (delta : ℝ) :
    retained c delta ⊆ {t | Source c t} := fun _ ht => ht.1

theorem source_eq_iUnion_retained (c : Cell) :
    {t | Source c t} = ⋃ n : ℕ, retained c (width n) := by
  ext t
  constructor
  · intro hs
    obtain ⟨n, hn⟩ := (source_eventually_in_core hs).exists
    exact mem_iUnion.mpr ⟨n, hs, hn⟩
  · intro ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact hn.1

end
end ImbalancedChen.P4AOriginalFull87HistoryCore
