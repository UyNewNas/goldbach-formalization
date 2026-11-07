import ImbalancedChen.P1OriginalFifthRawBoxSelectorEquivalence
import Mathlib.Data.List.Nodup
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The geometry key of a saved grid400 UNIT box consists of its five signed
lower indices. The mask and all three saved statistics are excluded.
Common membership in two half-open unit boxes forces equality of all five
integer indices. A finite loaded key-Nodup check therefore supplies genuine
pairwise disjointness, including every boundary face and signed index.

The checker is defined before Classical and uses integer key equality only.
No historical payload is evaluated; the actual292633-row passing witness
is UNEXECUTED / ready=false. A Finset of complete records by itself is not
an adequate key-Nodup witness, because masks/statistics can differ.
-/
namespace ImbalancedChen.P1FifthGrid400UnitBoxPartition

open P1OriginalPrefixRowDecodeSoundness

abbrev UnitBoxKey := Fin 5 → ℤ

def rowKey (raw : FifthWireRow) : UnitBoxKey := raw.lo

/-- Executable check on the original loaded list, before any record deduplication. -/
def unitKeyCheck (raw : Array FifthWireRow) : Bool :=
  decide ((raw.toList.map rowKey).Nodup)

def grid400Check (raw : Array FifthWireRow) : Bool :=
  raw.toList.all (fun row => decide (row.grid = 400))

def unitFamilyPartitionCheck (raw : Array FifthWireRow) : Bool :=
  grid400Check raw && unitKeyCheck raw

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

theorem unitKeyCheck_sound (raw : Array FifthWireRow)
    (hc : unitKeyCheck raw = true) : (raw.toList.map rowKey).Nodup :=
  of_decide_eq_true hc

theorem grid400Check_sound (raw : Array FifthWireRow)
    (hc : grid400Check raw = true) : ∀ row ∈ raw.toList, row.grid = 400 := by
  simpa only [grid400Check, List.all_eq_true, decide_eq_true_eq] using hc

theorem unitFamilyPartitionCheck_sound (raw : Array FifthWireRow)
    (hc : unitFamilyPartitionCheck raw = true) :
    (∀ row ∈ raw.toList, row.grid = 400) ∧ (raw.toList.map rowKey).Nodup := by
  have hp : grid400Check raw = true ∧ unitKeyCheck raw = true :=
    Bool.and_eq_true.mp hc
  exact ⟨grid400Check_sound raw hp.1, unitKeyCheck_sound raw hp.2⟩

/-- Two source1/400 half-open intervals cannot share a point unless their
signed integer keys are equal. No positivity of either index is required. -/
theorem unit_interval_key_unique (a b : ℤ) (x : ℝ)
    (ha : (a : ℝ) / 400 ≤ x ∧ x < ((a : ℝ) + 1) / 400)
    (hb : (b : ℝ) / 400 ≤ x ∧ x < ((b : ℝ) + 1) / 400) : a = b := by
  have habR : (a : ℝ) < (b : ℝ) + 1 := by linarith
  have hbaR : (b : ℝ) < (a : ℝ) + 1 := by linarith
  have habZ : a < b + 1 := by exact_mod_cast habR
  have hbaZ : b < a + 1 := by exact_mod_cast hbaR
  omega

theorem common_point_keys_eq (a b : FifthWireRow)
    (hga : a.grid = 400) (hgb : b.grid = 400) (t : Fin 5 → ℝ)
    (ha : t ∈ a.originalBox) (hb : t ∈ b.originalBox) : rowKey a = rowKey b := by
  funext i
  apply unit_interval_key_unique (a.lo i) (b.lo i) (t i)
  · simpa [FifthWireRow.lower, FifthWireRow.upper, hga] using ha i
  · simpa [FifthWireRow.lower, FifthWireRow.upper, hgb] using hb i

theorem unit_boxes_disjoint_of_key_ne (a b : FifthWireRow)
    (hga : a.grid = 400) (hgb : b.grid = 400) (hne : rowKey a ≠ rowKey b) :
    Disjoint a.originalBox b.originalBox := by
  apply Set.disjoint_left.2
  intro t ha hb
  exact hne (common_point_keys_eq a b hga hgb t ha hb)

/-- All irrelevant payload fields may differ while a unit box stays identical. -/
theorem unit_boxes_eq_of_key_eq (a b : FifthWireRow)
    (hga : a.grid = 400) (hgb : b.grid = 400) (hkey : rowKey a = rowKey b) :
    a.originalBox = b.originalBox := by
  ext t
  have hcoord : ∀ i, a.lo i = b.lo i := fun i => congrFun hkey i
  simp only [FifthWireRow.originalBox, mem_setOf_eq]
  simp [FifthWireRow.lower, FifthWireRow.upper, hga, hgb, hcoord]

theorem loaded_key_injective (raw : Array FifthWireRow)
    (hc : unitKeyCheck raw = true) :
    ∀ a ∈ raw.toList, ∀ b ∈ raw.toList, rowKey a = rowKey b → a = b := by
  exact List.inj_on_of_nodup_map (unitKeyCheck_sound raw hc)

/-- The original loaded row list is itself duplicate-free when its keys are. -/
theorem loaded_rows_nodup (raw : Array FifthWireRow)
    (hc : unitKeyCheck raw = true) : raw.toList.Nodup :=
  List.Nodup.of_map rowKey (unitKeyCheck_sound raw hc)

def KeyInjective (records : Finset FifthWireRow) : Prop :=
  ∀ a ∈ records, ∀ b ∈ records, rowKey a = rowKey b → a = b

theorem loaded_key_injective_finset (raw : Array FifthWireRow)
    (hc : unitKeyCheck raw = true) : KeyInjective raw.toList.toFinset := by
  intro a ha b hb hkey
  exact loaded_key_injective raw hc a (List.mem_toFinset.mp ha)
    b (List.mem_toFinset.mp hb) hkey

theorem records_pairwise_disjoint (records : Finset FifthWireRow)
    (hgrid : ∀ row ∈ records, row.grid = 400) (hkey : KeyInjective records) :
    Set.PairwiseDisjoint (records : Set FifthWireRow) FifthWireRow.originalBox := by
  intro a ha b hb hne
  apply unit_boxes_disjoint_of_key_ne a b (hgrid a ha) (hgrid b hb)
  intro heq
  exact hne (hkey a ha b hb heq)

/-- A passing finite checker supplies geometry, not an assumed disjointness
or a target gain. Its actual full-table passing witness is not executed. -/
theorem loaded_records_pairwise_disjoint (raw : Array FifthWireRow)
    (hc : unitFamilyPartitionCheck raw = true) :
    Set.PairwiseDisjoint (raw.toList.toFinset : Set FifthWireRow)
      FifthWireRow.originalBox := by
  have hp := unitFamilyPartitionCheck_sound raw hc
  exact records_pairwise_disjoint raw.toList.toFinset
    (fun row hr => hp.1 row (List.mem_toFinset.mp hr))
    (loaded_key_injective_finset raw (Bool.and_eq_true.mp hc).2)

/-- Common membership now identifies the complete record within this family. -/
theorem records_common_point_eq (records : Finset FifthWireRow)
    (hgrid : ∀ row ∈ records, row.grid = 400) (hkey : KeyInjective records)
    (a b : FifthWireRow) (ha : a ∈ records) (hb : b ∈ records)
    (t : Fin 5 → ℝ) (hta : t ∈ a.originalBox) (htb : t ∈ b.originalBox) : a = b :=
  hkey a ha b hb (common_point_keys_eq a b (hgrid a ha) (hgrid b hb) t hta htb)

theorem measurableSet_originalBox (raw : FifthWireRow) : MeasurableSet raw.originalBox := by
  have heq : raw.originalBox =
      logPrimeBox (fun i => (raw.lower i : ℝ)) (fun i => (raw.upper i : ℝ)) := by
    ext t
    exact mem_logPrimeBox.symm
  rw [heq]
  exact measurableSet_logPrimeBox _ _

/-- Ambient or same-history clipping preserves the actual disjointness. -/
theorem clipped_records_pairwise_disjoint (records : Finset FifthWireRow)
    (hgrid : ∀ row ∈ records, row.grid = 400) (hkey : KeyInjective records)
    (ambient : Set (Fin 5 → ℝ)) :
    Set.PairwiseDisjoint (records : Set FifthWireRow)
      (fun raw => raw.originalBox ∩ ambient) := by
  intro a ha b hb hne
  exact ((records_pairwise_disjoint records hgrid hkey) ha hb hne).mono
    inter_subset_left inter_subset_left

end
end ImbalancedChen.P1FifthGrid400UnitBoxPartition
