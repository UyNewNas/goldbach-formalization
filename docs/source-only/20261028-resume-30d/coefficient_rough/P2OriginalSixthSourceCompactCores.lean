import ImbalancedChen.P2CompactOriginalRetainedSixth
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

Explicit compact inner truncations of the eleven ORIGINAL sixth source
cells.  Every strict physical face is buffered; the weak raw31/first3
branch tests, W dominance and old comparison are retained exactly.  No
unrelated compact set or replacement numerical region is introduced.
-/

namespace ImbalancedChen.P2OriginalSixthSourceCompactCores

noncomputable section
open Classical Set Filter MeasureTheory
open scoped Topology BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics
open P2CompactThirdHistorySelection

def sourceRegion (c : Cell) : Set Physical := {t | PhysicalCell c t}

def pairAboveSlack (c : Cell) (t : Physical) : ℝ :=
  if c.family = .pair17 ∨ c.family = .pair12 then oldCap c t - R0 t else 1

def winnerSlack (c : Cell) (t : Physical) : ℝ :=
  match c.family with
  | .pair17 => t 0 + t 4 - mu
  | .pair12 => mu - (t 2 + t 3)
  | _ => 1

def prioritySlack (c : Cell) (t : Physical) : ℝ :=
  match c with
  | .singleton34_1371 => newCap c t - descending33 t
  | .singleton50_1353 | .singleton50_1355 =>
      min (newCap c t - descending33 t) (newCap c t - ascending34 t)
  | .tent33_1371 | .tent33_1867 => clippedCap t - ascending33 t
  | _ => 1

theorem pairAboveSlack_pos_iff (c : Cell) (t : Physical) :
    0 < pairAboveSlack c t ↔
      (c.family = .pair17 ∨ c.family = .pair12 → R0 t < oldCap c t) := by
  by_cases h : c.family = .pair17 ∨ c.family = .pair12 <;>
    simp [pairAboveSlack, h, sub_pos]

theorem winnerSlack_pos_iff (c : Cell) (t : Physical) :
    0 < winnerSlack c t ↔ winnerPlane c t := by
  cases c <;> simp [winnerSlack, winnerPlane, Cell.family, sub_pos]

theorem prioritySlack_pos_iff (c : Cell) (t : Physical) :
    0 < prioritySlack c t ↔ priority c t := by
  cases c <;> simp [prioritySlack, priority, lt_min_iff, sub_pos]

@[fun_prop] theorem continuous_R0 : Continuous R0 := by unfold R0; fun_prop
@[fun_prop] theorem continuous_S5 : Continuous S5 := by unfold S5; fun_prop
@[fun_prop] theorem continuous_S6 : Continuous S6 := by unfold S6; fun_prop
@[fun_prop] theorem continuous_H3 : Continuous H3 := by unfold H3; fun_prop
@[fun_prop] theorem continuous_H5 : Continuous H5 := by unfold H5; fun_prop
@[fun_prop] theorem continuous_W : Continuous W := by unfold W; fun_prop
@[fun_prop] theorem continuous_oldCap (c : Cell) : Continuous (oldCap c) := by
  cases c <;> simp only [oldCap, Cell.family] <;> fun_prop
@[fun_prop] theorem continuous_newCap (c : Cell) : Continuous (newCap c) := by
  cases c <;> simp [newCap, Cell.family, clippedCap, ascending33, S5] <;> fun_prop
@[fun_prop] theorem continuous_subsetSum (mask : ℕ) : Continuous (subsetSum mask) := by
  unfold subsetSum
  fun_prop
@[fun_prop] theorem continuous_selectedSum (mask : ℕ) : Continuous (selectedSum mask) := by
  unfold selectedSum
  fun_prop
@[fun_prop] theorem continuous_fullSquare (i : Fin 6) :
    Continuous (fullSquare i) := by unfold fullSquare; fun_prop
@[fun_prop] theorem continuous_remainingSquare (mask : ℕ) (i : Fin 6) :
    Continuous (remainingSquare mask i) := by unfold remainingSquare; fun_prop
@[fun_prop] theorem continuous_pairAboveSlack (c : Cell) :
    Continuous (pairAboveSlack c) := by
  unfold pairAboveSlack
  split_ifs <;> fun_prop
@[fun_prop] theorem continuous_winnerSlack (c : Cell) : Continuous (winnerSlack c) := by
  cases c <;> simp [winnerSlack, Cell.family] <;> fun_prop
@[fun_prop] theorem continuous_prioritySlack (c : Cell) : Continuous (prioritySlack c) := by
  cases c <;> simp [prioritySlack, clippedCap, descending33, ascending33, ascending34, S5] <;> fun_prop

/-- These nineteen entries are exactly the scalar strict fields of the
source PhysicalCell.  The full/complement square fields are added below. -/
def baseFace (c : Cell) : Fin 19 → Physical → ℝ :=
  ![fun t => t 5, fun t => t 4 - t 5, fun t => t 3 - t 4,
    fun t => t 2 - t 3, fun t => t 1 - t 2, fun t => t 0 - t 1,
    fun t => mu - t 0, fun t => 1 / 50 - t 5,
    fun t => t 5 - 53 / 4608, fun t => R0 t - H3 t, fun t => R0 t - H5 t,
    pairAboveSlack c, winnerSlack c, fun t => newCap c t - oldCap c t,
    fun t => (1 + selectedSum c.selectedMask t) / 2 - newCap c t,
    fun t => 57 / 64 - 3 * selectedSum c.selectedMask t / 2 - newCap c t,
    fun t => R0 t - S6 t - t 5,
    fun t => 3 * t 5 - newResidual c t, prioritySlack c]

def fullFace (c : Cell) (i : Fin 6) (t : Physical) : ℝ :=
  newCap c t - fullSquare i t

def complementFace (c : Cell) (i : Fin 6) (t : Physical) : ℝ :=
  if bit c.selectedMask i.val = false then newCap c t - remainingSquare c.selectedMask i t
  else 1

def sourceFaces (c : Cell) : List (Physical → ℝ) :=
  List.ofFn (baseFace c) ++ (List.ofFn (fullFace c) ++ List.ofFn (complementFace c))

def strictMargin (c : Cell) (t : Physical) : ℝ :=
  (sourceFaces c).foldr (fun f z => min (f t) z) 1

private theorem fold_min_pos (fs : List (Physical → ℝ)) (t : Physical) :
    0 < fs.foldr (fun f z => min (f t) z) 1 ↔ ∀ f ∈ fs, 0 < f t := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp [lt_min_iff, ih]

private theorem continuous_fold_min (fs : List (Physical → ℝ))
    (hc : ∀ f ∈ fs, Continuous f) :
    Continuous (fun t => fs.foldr (fun f z => min (f t) z) 1) := by
  induction fs with
  | nil => exact continuous_const
  | cons f fs ih =>
      exact (hc f (by simp)).min (ih (fun g hg => hc g (by simp [hg])))

@[fun_prop] theorem continuous_strictMargin (c : Cell) : Continuous (strictMargin c) := by
  apply continuous_fold_min
  intro f hf
  rcases List.mem_append.mp hf with hb | hrest
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    fin_cases i <;> simp only [baseFace, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      simp only [newResidual] <;> fun_prop
  · rcases List.mem_append.mp hrest with hfull | hcomp
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hfull
      unfold fullFace
      fun_prop
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hcomp
      unfold complementFace
      split_ifs <;> fun_prop

/-- All weak fields of the same source cell, including the branch of
each numerical raw31 mask, stay weak and unchanged in every truncation. -/
def closedLicense (c : Cell) (t : Physical) : Prop :=
  W t ≤ R0 t ∧
  (∀ mask ∈ Finset.Icc 1 31,
    branchLicense (c.descending mask) (oldCap c t) (subsetSum mask t)) ∧
  (∀ mask ∈ Finset.Icc 1 7,
    branchLicense (c.descending mask) (R0 t) (subsetSum mask t)) ∧
  R0 t ≤ oldCap c t

theorem physicalCell_iff (c : Cell) (t : Physical) :
    PhysicalCell c t ↔ closedLicense c t ∧ 0 < strictMargin c t := by
  have hbaseMem (i : Fin 19) : baseFace c i ∈ sourceFaces c := by
    exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hfullMem (i : Fin 6) : fullFace c i ∈ sourceFaces c := by
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have hcompMem (i : Fin 6) : complementFace c i ∈ sourceFaces c := by
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  constructor
  · intro hc
    refine ⟨⟨hc.oldW, hc.oldBranches, hc.first3Branches, hc.comparison⟩, ?_⟩
    apply (fold_min_pos (sourceFaces c) t).mpr
    have hb : ∀ i : Fin 19, 0 < baseFace c i t := by
      intro i
      fin_cases i
      · exact hc.rpos
      · exact sub_pos.mpr hc.order.1
      · exact sub_pos.mpr hc.order.2.1
      · exact sub_pos.mpr hc.order.2.2.1
      · exact sub_pos.mpr hc.order.2.2.2.1
      · exact sub_pos.mpr hc.order.2.2.2.2
      · exact sub_pos.mpr hc.largest
      · exact sub_pos.mpr hc.oldCutoff
      · exact sub_pos.mpr hc.compactCutoff
      · exact sub_pos.mpr hc.history3
      · exact sub_pos.mpr hc.history5
      · exact (pairAboveSlack_pos_iff c t).mpr hc.pairAbove
      · exact (winnerSlack_pos_iff c t).mpr hc.winner
      · exact sub_pos.mpr hc.positiveGap
      · exact sub_pos.mpr hc.selectedAscending
      · exact sub_pos.mpr hc.selectedDescending
      · exact sub_pos.mpr hc.oldArgument
      · exact sub_pos.mpr hc.newArgument
      · exact (prioritySlack_pos_iff c t).mpr hc.priority
    intro f hf
    rcases List.mem_append.mp hf with h | h
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
      exact hb i
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
        exact sub_pos.mpr (hc.fullSquares i)
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
        unfold complementFace
        split_ifs with hi
        · exact sub_pos.mpr (hc.remainingSquares i hi)
        · norm_num
  · rintro ⟨hweak, hmargin⟩
    have hfaces := (fold_min_pos (sourceFaces c) t).mp hmargin
    have hb (i : Fin 19) : 0 < baseFace c i t := hfaces _ (hbaseMem i)
    refine ⟨hb 0, ⟨sub_pos.mp (hb 1), sub_pos.mp (hb 2), sub_pos.mp (hb 3),
      sub_pos.mp (hb 4), sub_pos.mp (hb 5)⟩,
      sub_pos.mp (hb 6), sub_pos.mp (hb 7), sub_pos.mp (hb 8),
      sub_pos.mp (hb 9), sub_pos.mp (hb 10), hweak.1, hweak.2.1, hweak.2.2.1,
      hweak.2.2.2, (pairAboveSlack_pos_iff c t).mp (hb 11),
      (winnerSlack_pos_iff c t).mp (hb 12), sub_pos.mp (hb 13),
      sub_pos.mp (hb 14), sub_pos.mp (hb 15), ?_, ?_,
      sub_pos.mp (hb 16), sub_pos.mp (hb 17), (prioritySlack_pos_iff c t).mp (hb 18)⟩
    · intro i
      exact sub_pos.mp (hfaces _ (hfullMem i))
    · intro i hi
      have h := hfaces _ (hcompMem i)
      simpa only [complementFace, if_pos hi, sub_pos] using h

theorem isClosed_closedLicense (c : Cell) : IsClosed {t | closedLicense c t} := by
  have hold : IsClosed {t : Physical | W t ≤ R0 t} := isClosed_le continuous_W continuous_R0
  have hcompare : IsClosed {t : Physical | R0 t ≤ oldCap c t} :=
    isClosed_le continuous_R0 (continuous_oldCap c)
  have hrows (hi : ℕ) (cap : Physical → ℝ) (hcap : Continuous cap) :
      IsClosed {t : Physical | ∀ mask ∈ Finset.Icc 1 hi,
        branchLicense (c.descending mask) (cap t) (subsetSum mask t)} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro mask
    apply isClosed_iInter
    intro _
    cases hd : c.descending mask <;> simp only [branchLicense, hd,
      Bool.false_eq_true, if_false, if_true]
    · exact isClosed_le (continuous_subsetSum mask) (by fun_prop)
    · exact isClosed_le (by fun_prop) hcap
  exact hold.inter ((hrows 31 (oldCap c) (continuous_oldCap c)).inter
    ((hrows 7 R0 continuous_R0).inter hcompare))

def ambientCube : Set Physical := Set.univ.pi (fun _ : Fin 6 => Icc (0 : ℝ) 1)

theorem physicalCell_mem_ambientCube (c : Cell) (t : Physical) (hc : PhysicalCell c t) :
    t ∈ ambientCube := by
  intro i _
  refine ⟨(hc.coordinates_pos i).le, ?_⟩
  have hmu : mu < (1 : ℝ) := by norm_num [mu]
  fin_cases i <;> linarith [hc.largest, hc.order.1, hc.order.2.1,
    hc.order.2.2.1, hc.order.2.2.2.1, hc.order.2.2.2.2]

def compactCore (c : Cell) (delta : ℝ) : Set Physical :=
  (ambientCube ∩ {t | closedLicense c t}) ∩ {t | delta ≤ strictMargin c t}

theorem isCompact_compactCore (c : Cell) (delta : ℝ) : IsCompact (compactCore c delta) :=
  ((isCompact_univ_pi (fun _ : Fin 6 => isCompact_Icc)).inter_right
    (isClosed_closedLicense c)).inter_right
      (isClosed_le continuous_const (continuous_strictMargin c))

theorem compactCore_subset_sourceRegion (c : Cell) {delta : ℝ} (hd : 0 < delta) :
    compactCore c delta ⊆ sourceRegion c := by
  intro t ht
  exact (physicalCell_iff c t).mpr ⟨ht.1.2, hd.trans_le ht.2⟩

theorem measurableSet_sourceRegion (c : Cell) : MeasurableSet (sourceRegion c) := by
  have heq : sourceRegion c = {t | closedLicense c t} ∩ {t | 0 < strictMargin c t} := by
    ext t
    exact physicalCell_iff c t
  rw [heq]
  exact (isClosed_closedLicense c).measurableSet.inter
    (isOpen_lt continuous_const (continuous_strictMargin c)).measurableSet

def coreSequence (c : Cell) (n : ℕ) : Set Physical := compactCore c (1 / (n + 1 : ℝ))
def omittedSource (c : Cell) (n : ℕ) : Set Physical := sourceRegion c \ coreSequence c n

theorem coreSequence_subset_sourceRegion (c : Cell) (n : ℕ) :
    coreSequence c n ⊆ sourceRegion c := compactCore_subset_sourceRegion c (by positivity)

theorem coreSequence_mono (c : Cell) : Monotone (coreSequence c) := by
  intro n m hnm t ht
  refine ⟨ht.1, ?_⟩
  have hden : (n + 1 : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hnm 1
  exact (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n + 1) hden).trans ht.2

theorem eventually_mem_coreSequence (c : Cell) {t : Physical} (ht : t ∈ sourceRegion c) :
    ∀ᶠ n : ℕ in atTop, t ∈ coreSequence c n := by
  have hmargin := (physicalCell_iff c t).mp ht
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hmargin.2))
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  exact ⟨⟨physicalCell_mem_ambientCube c t ht, hmargin.1⟩, (hn m hm).le⟩

/-- Exact exhaustion includes every original weak raw-branch face.  It
does not silently replace the source domain by its topological interior. -/
theorem iUnion_coreSequence (c : Cell) : (⋃ n : ℕ, coreSequence c n) = sourceRegion c := by
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
    exact coreSequence_subset_sourceRegion c n hn
  · intro t ht
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (eventually_mem_coreSequence c ht)
    exact Set.mem_iUnion.mpr ⟨n, hn n le_rfl⟩

/-- The previous compact selection construction now receives these
explicit source cores, with no caller compactness or support premise. -/
theorem original_core_thirdChoice (c : Cell) (n : ℕ) :
    Nonempty (CompactThirdChoice (coreSequence c n)) := by
  apply exists_compactThirdChoice _ (isCompact_compactCore c _)
  intro t ht
  exact ⟨c, coreSequence_subset_sourceRegion c n ht⟩

/-- The original numerical coordinates are already physical for pair12;
the other ten cells use the frozen inverse chart. -/
def encode (c : Cell) (t : Physical) : Physical :=
  if c.family = .pair12 then t else chart t

theorem decode_encode (c : Cell) (t : Physical) : decode c (encode c t) = t := by
  by_cases h : c.family = .pair12 <;> simp [decode, encode, h, physical_chart]

theorem encode_decode (c : Cell) (q : Physical) : encode c (decode c q) = q := by
  by_cases h : c.family = .pair12 <;> simp [decode, encode, h, chart_physical]

theorem continuous_encode (c : Cell) : Continuous (encode c) := by
  unfold encode
  split_ifs
  · exact continuous_id
  · unfold chart
    fun_prop

def sourceCoordinateCore (c : Cell) (n : ℕ) : Set Physical := encode c '' coreSequence c n

theorem isCompact_sourceCoordinateCore (c : Cell) (n : ℕ) :
    IsCompact (sourceCoordinateCore c n) :=
  (isCompact_compactCore c _).image (continuous_encode c)

theorem sourceCoordinateCore_iff_decode (c : Cell) (n : ℕ) (q : Physical) :
    q ∈ sourceCoordinateCore c n ↔ decode c q ∈ coreSequence c n := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa only [decode_encode] using ht
  · intro hq
    exact ⟨decode c q, hq, encode_decode c q⟩

/-- These are truncations of the actual source-coordinate domain used
by the eleven named producers; there is no surrogate box substitution. -/
theorem iUnion_sourceCoordinateCore (c : Cell) :
    (⋃ n : ℕ, sourceCoordinateCore c n) = {q | PhysicalCell c (decode c q)} := by
  ext q
  constructor
  · intro hq
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hq
    exact coreSequence_subset_sourceRegion c n
      ((sourceCoordinateCore_iff_decode c n q).mp hn)
  · intro hq
    have hmem : decode c q ∈ ⋃ n : ℕ, coreSequence c n := by
      rw [iUnion_coreSequence]
      exact hq
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact Set.mem_iUnion.mpr ⟨n, (sourceCoordinateCore_iff_decode c n q).mpr hn⟩

end
end ImbalancedChen.P2OriginalSixthSourceCompactCores
