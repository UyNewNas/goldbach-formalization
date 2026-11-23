import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Compact typed owner for selected upper saving 3: new fifth C/F boxes

SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.  This is a data and geometry layer for
the original disjoint fifth saving `D_{5,new}`.  Each saved NPZ row consists of
ten integers `(grid, lower[0..4], mask, d, aa, bb)` and a separate positive
Q80 floor.  The C blocks use grid 400; the F blocks use grid 800.  The
physical owner is the half-open five-coordinate logarithmic box.  A fine
row's coarse parent is coordinatewise integer division by two.

The source archive reports 43,236 C rows and 1,720,184 F rows in 47 blocks
each.  No complete array is imported here, and no certificate arithmetic is
replayed.  The ownership predicates below are proof obligations for a future
exact importer; they are not asserted for all archived rows.  In particular
the saved Q80 floor is not equated with the actual fifth gain integral.
-/

namespace ImbalancedChen.Entry3NewFifthTypedOwners

open Set

abbrev BoxKey := Fin 5 → ℕ

/-- One literal saved row plus its separate floor field.  `gap`, `ratioNum`,
and `ratioDen` are source columns 7, 8, and 9, not inferred estimates. -/
structure SavedRow where
  grid : ℕ
  lower : BoxKey
  mask : ℕ
  gap : ℕ
  ratioNum : ℕ
  ratioDen : ℕ
  floorQ80 : ℕ
  deriving DecidableEq

/-- Exact half-open log-coordinate owner.  The strict upper faces ensure
that equal-grid box interiors and their boundary assignment have one key. -/
def indexBox (grid : ℕ) (lower : BoxKey) : Set (Fin 5 → ℝ) :=
  {t | ∀ i, (lower i : ℝ) / grid ≤ t i ∧
    t i < ((lower i : ℝ) + 1) / grid}

def SavedRow.owner (r : SavedRow) : Set (Fin 5 → ℝ) :=
  indexBox r.grid r.lower

def fineParent (lower : BoxKey) : BoxKey :=
  fun i => lower i / 2

/-- Any grid-800 child lies in its exact grid-400 parent.  No floating-point
rounding or measure-zero deletion is used. -/
theorem fine_box_subset_parent (lower : BoxKey) :
    indexBox 800 lower ⊆ indexBox 400 (fineParent lower) := by
  intro t ht i
  let k : ℕ := lower i
  have hki : 2 * (k / 2) ≤ k := by omega
  have hkj : k + 1 ≤ 2 * (k / 2) + 2 := by omega
  have hkiR : (2 : ℝ) * (k / 2 : ℕ) ≤ (k : ℝ) := by
    exact_mod_cast hki
  have hkjR : (k : ℝ) + 1 ≤ 2 * (k / 2 : ℕ) + 2 := by
    exact_mod_cast hkj
  have hfl : (k : ℝ) ≤ 800 * t i :=
    (div_le_iff₀ (by norm_num : (0 : ℝ) < 800)).mp (ht i).1
  have hfu : 800 * t i < (k : ℝ) + 1 :=
    (lt_div_iff₀ (by norm_num : (0 : ℝ) < 800)).mp (ht i).2
  change ((k / 2 : ℕ) : ℝ) / 400 ≤ t i ∧
    t i < (((k / 2 : ℕ) : ℝ) + 1) / 400
  constructor
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 400)).mpr
    nlinarith only [hkiR, hfl]
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 400)).mpr
    nlinarith only [hkjR, hfu]

/-- A point has a unique half-open index at any positive fixed grid. -/
theorem indexBox_owner_unique {grid : ℕ} (hgrid : 0 < grid)
    {a b : BoxKey} {t : Fin 5 → ℝ}
    (ha : t ∈ indexBox grid a) (hb : t ∈ indexBox grid b) : a = b := by
  funext i
  have hg : (0 : ℝ) < grid := by exact_mod_cast hgrid
  have haLo : (a i : ℝ) ≤ (grid : ℝ) * t i :=
    (div_le_iff₀ hg).mp (ha i).1
  have haHi : (grid : ℝ) * t i < (a i : ℝ) + 1 :=
    (lt_div_iff₀ hg).mp (ha i).2
  have hbLo : (b i : ℝ) ≤ (grid : ℝ) * t i :=
    (div_le_iff₀ hg).mp (hb i).1
  have hbHi : (grid : ℝ) * t i < (b i : ℝ) + 1 :=
    (lt_div_iff₀ hg).mp (hb i).2
  have hab : a i < b i + 1 := by
    exact_mod_cast (show (a i : ℝ) < (b i : ℝ) + 1 by linarith)
  have hba : b i < a i + 1 := by
    exact_mod_cast (show (b i : ℝ) < (a i : ℝ) + 1 by linarith)
  omega

/-- The exact archive ownership checks are stated as key-level predicates.
They require an independent checked import of the old O keys and the new C
keys; a scalar gain or a row-count assertion cannot supply either check. -/
def CoarseOwned (oldKeys : Finset BoxKey) (r : SavedRow) : Prop :=
  r.grid = 400 ∧ r.lower ∉ oldKeys

def FineOwned (oldKeys coarseKeys : Finset BoxKey) (r : SavedRow) : Prop :=
  r.grid = 800 ∧ fineParent r.lower ∉ oldKeys ∧
    fineParent r.lower ∉ coarseKeys

/-- A fine row is physically inside its coarse parent box and can touch no
old or newly selected coarse owner when the archived key exclusions are
proved for this row. -/
theorem fine_owner_parent_and_exclusion
    {oldKeys coarseKeys : Finset BoxKey} {r : SavedRow}
    (hown : FineOwned oldKeys coarseKeys r)
    {t : Fin 5 → ℝ} (ht : t ∈ r.owner) :
    t ∈ indexBox 400 (fineParent r.lower) ∧
      (∀ old ∈ oldKeys, t ∉ indexBox 400 old) ∧
      (∀ coarse ∈ coarseKeys, t ∉ indexBox 400 coarse) := by
  have hf : t ∈ indexBox 800 r.lower := by
    simpa only [SavedRow.owner, hown.1] using ht
  have hp := fine_box_subset_parent r.lower hf
  refine ⟨hp, ?_, ?_⟩
  · intro old hold htold
    have heq := indexBox_owner_unique (by norm_num : 0 < 400) hp htold
    have hmem : fineParent r.lower ∈ oldKeys := by rw [heq]; exact hold
    exact hown.2.1 hmem
  · intro coarse hcoarse htcoarse
    have heq := indexBox_owner_unique (by norm_num : 0 < 400) hp htcoarse
    have hmem : fineParent r.lower ∈ coarseKeys := by rw [heq]; exact hcoarse
    exact hown.2.2 hmem

/-- A literal static sample from C block 0005.  Its source row is
`(400,76,67,28,22,9,18,256,1152,288)` and its separate floor is
`2092644346019902`; no whole-block verification is inferred. -/
def coarseBlock05First : SavedRow :=
  ⟨400, ![76, 67, 28, 22, 9], 18, 256, 1152, 288,
    2092644346019902⟩

/-- A literal static sample from F block 0005. -/
def fineBlock05First : SavedRow :=
  ⟨800, ![141, 136, 57, 44, 19], 17, 256, 2416, 608,
    37708750149112⟩

theorem sample_grids_and_parent :
    coarseBlock05First.grid = 400 ∧ fineBlock05First.grid = 800 ∧
      fineParent fineBlock05First.lower = ![70, 68, 28, 22, 9] := by
  constructor
  · rfl
  constructor
  · rfl
  · funext i
    fin_cases i <;> norm_num [fineParent, fineBlock05First]

end ImbalancedChen.Entry3NewFifthTypedOwners
