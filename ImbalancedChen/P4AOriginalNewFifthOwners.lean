import ImbalancedChen.P4AOriginalNewFifthArchive
import ImbalancedChen.P4AOriginalNewFifthUnion
import ImbalancedChen.Entry3NewFifthTypedOwners
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Basic

/-! An independent whole-input owner lookup, with the physical semantics
of the original half-open cells. Every new key must look up its own
block and source position. Fine rows must miss both old and new coarse
parents. Equality of dictionary reads proves uniqueness independently of
the dictionary's internal bucket or collision behavior. -/
namespace ImbalancedChen.P4AOriginalNewFifthOwners
open P4AOriginalNewFifthArchiveReader P4AOriginalNewFifthArchiveData P4AOriginalNewFifthArchive
open P1OriginalPrefixRowDecodeSoundness
open P1HistoricalFifthIndexedOwnerArchive (ArchiveIndex archiveRow archiveRow_source_member)
open Entry3NewFifthTypedOwners (BoxKey indexBox fineParent fine_box_subset_parent indexBox_owner_unique)

def lower (r : FifthWireRow) : BoxKey := fun k => (r.lo k).toNat
def key (r : FifthWireRow) : List ℕ := List.ofFn (lower r)
def parentKey (fine : Bool) (r : FifthWireRow) : List ℕ :=
  if fine then List.ofFn (fineParent (lower r)) else key r

/-- Both author loops enumerate increasing five-subsets of [8,78)
lexicographically, reverse their coordinates on the wire, and put
262144 candidates in each block. Fine children use their coarse
parent's block. The predicate below independently checks each stored
row's computed block; only equality of block reads is used in proofs. -/
def ways (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => n
  | 2 => n*(n-1)/2
  | 3 => n*(n-1)*(n-2)/6
  | 4 => n*(n-1)*(n-2)*(n-3)/24
  | 5 => n*(n-1)*(n-2)*(n-3)*(n-4)/120
  | _ => 0

def lexRank (remaining start : ℕ) : List ℕ → ℕ
  | [] => 0
  | t :: ts => ways (78-start) remaining - ways (78-t) remaining +
      lexRank (remaining-1) (t+1) ts

def home (coarseKey : List ℕ) : ℕ := lexRank 5 8 coarseKey.reverse / 262144

def numbered {α : Type*} (start : ℕ) : List α → List (α × ℕ)
  | [] => []
  | x::xs => (x,start)::numbered (start+1) xs

private theorem mem_numbered {α : Type*} (xs : List α) (start : ℕ) :
    ∀ (j : ℕ) (hj : j < xs.length), (xs[j],start+j) ∈ numbered start xs := by
  induction xs generalizing start with
  | nil => simp
  | cons x xs ih =>
    intro j hj
    cases j with
    | zero => simp [numbered]
    | succ j =>
      have hj' : j < xs.length := by simpa using hj
      apply List.mem_cons_of_mem
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (start+1) j hj'

def indexedRows (b : BlockIndex) := numbered 0 (block b).words.list

def ownersOn (b : BlockIndex) : Std.HashMap (List ℕ) ℕ :=
  Std.HashMap.ofList ((indexedRows b).map (fun x => (key (wire x.1), x.2)))

def oldKeys : Std.HashSet (List ℕ) := Std.HashSet.ofList
  (Data.P1HistoricalFifthSavedTableData.rows.toList.map key)

def Lookup (b : BlockIndex) (dict coarse : Std.HashMap (List ℕ) ℕ) (old : Std.HashSet (List ℕ))
    (x : (ℕ × ℕ) × ℕ) : Prop :=
  let r := wire x.1
  let parent := parentKey b.1 r
  home parent = b.2.val ∧ dict.get? (key r) = some x.2 ∧
    old.contains parent = false ∧ (b.1 = true → coarse.get? parent = none)

instance (b : BlockIndex) (dict coarse : Std.HashMap (List ℕ) ℕ) (old : Std.HashSet (List ℕ))
    (x : (ℕ × ℕ) × ℕ) : Decidable (Lookup b dict coarse old x) := by
  unfold Lookup
  infer_instance

def lookups (b : BlockIndex) : Bool :=
  let dict := ownersOn b
  let coarse := ownersOn (false,b.2)
  let old := oldKeys
  (indexedRows b).all (fun x => decide (Lookup b dict coarse old x))

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0000 : lookups (false,0) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0001 : lookups (false,1) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0002 : lookups (false,2) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0003 : lookups (false,3) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0004 : lookups (false,4) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0005 : lookups (false,5) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0006 : lookups (false,6) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0007 : lookups (false,7) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0008 : lookups (false,8) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0009 : lookups (false,9) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0010 : lookups (false,10) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0011 : lookups (false,11) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0012 : lookups (false,12) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0013 : lookups (false,13) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0014 : lookups (false,14) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0015 : lookups (false,15) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0016 : lookups (false,16) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0017 : lookups (false,17) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0018 : lookups (false,18) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0019 : lookups (false,19) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0020 : lookups (false,20) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0021 : lookups (false,21) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0022 : lookups (false,22) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0023 : lookups (false,23) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0024 : lookups (false,24) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0025 : lookups (false,25) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0026 : lookups (false,26) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0027 : lookups (false,27) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0028 : lookups (false,28) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0029 : lookups (false,29) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0030 : lookups (false,30) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0031 : lookups (false,31) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0032 : lookups (false,32) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0033 : lookups (false,33) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0034 : lookups (false,34) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0035 : lookups (false,35) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0036 : lookups (false,36) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0037 : lookups (false,37) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0038 : lookups (false,38) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0039 : lookups (false,39) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0040 : lookups (false,40) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0041 : lookups (false,41) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0042 : lookups (false,42) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0043 : lookups (false,43) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0044 : lookups (false,44) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0045 : lookups (false,45) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerC0046 : lookups (false,46) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0000 : lookups (true,0) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0001 : lookups (true,1) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0002 : lookups (true,2) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0003 : lookups (true,3) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0004 : lookups (true,4) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0005 : lookups (true,5) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0006 : lookups (true,6) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0007 : lookups (true,7) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0008 : lookups (true,8) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0009 : lookups (true,9) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0010 : lookups (true,10) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0011 : lookups (true,11) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0012 : lookups (true,12) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0013 : lookups (true,13) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0014 : lookups (true,14) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0015 : lookups (true,15) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0016 : lookups (true,16) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0017 : lookups (true,17) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0018 : lookups (true,18) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0019 : lookups (true,19) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0020 : lookups (true,20) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0021 : lookups (true,21) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0022 : lookups (true,22) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0023 : lookups (true,23) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0024 : lookups (true,24) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0025 : lookups (true,25) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0026 : lookups (true,26) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0027 : lookups (true,27) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0028 : lookups (true,28) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0029 : lookups (true,29) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0030 : lookups (true,30) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0031 : lookups (true,31) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0032 : lookups (true,32) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0033 : lookups (true,33) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0034 : lookups (true,34) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0035 : lookups (true,35) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0036 : lookups (true,36) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0037 : lookups (true,37) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0038 : lookups (true,38) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0039 : lookups (true,39) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0040 : lookups (true,40) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0041 : lookups (true,41) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0042 : lookups (true,42) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0043 : lookups (true,43) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0044 : lookups (true,44) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0045 : lookups (true,45) = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem ownerF0046 : lookups (true,46) = true := by decide

theorem all_lookups (b : BlockIndex) : lookups b = true := by
  rcases b with ⟨fine,k⟩
  cases fine
  · fin_cases k
    · exact ownerC0000
    · exact ownerC0001
    · exact ownerC0002
    · exact ownerC0003
    · exact ownerC0004
    · exact ownerC0005
    · exact ownerC0006
    · exact ownerC0007
    · exact ownerC0008
    · exact ownerC0009
    · exact ownerC0010
    · exact ownerC0011
    · exact ownerC0012
    · exact ownerC0013
    · exact ownerC0014
    · exact ownerC0015
    · exact ownerC0016
    · exact ownerC0017
    · exact ownerC0018
    · exact ownerC0019
    · exact ownerC0020
    · exact ownerC0021
    · exact ownerC0022
    · exact ownerC0023
    · exact ownerC0024
    · exact ownerC0025
    · exact ownerC0026
    · exact ownerC0027
    · exact ownerC0028
    · exact ownerC0029
    · exact ownerC0030
    · exact ownerC0031
    · exact ownerC0032
    · exact ownerC0033
    · exact ownerC0034
    · exact ownerC0035
    · exact ownerC0036
    · exact ownerC0037
    · exact ownerC0038
    · exact ownerC0039
    · exact ownerC0040
    · exact ownerC0041
    · exact ownerC0042
    · exact ownerC0043
    · exact ownerC0044
    · exact ownerC0045
    · exact ownerC0046
  · fin_cases k
    · exact ownerF0000
    · exact ownerF0001
    · exact ownerF0002
    · exact ownerF0003
    · exact ownerF0004
    · exact ownerF0005
    · exact ownerF0006
    · exact ownerF0007
    · exact ownerF0008
    · exact ownerF0009
    · exact ownerF0010
    · exact ownerF0011
    · exact ownerF0012
    · exact ownerF0013
    · exact ownerF0014
    · exact ownerF0015
    · exact ownerF0016
    · exact ownerF0017
    · exact ownerF0018
    · exact ownerF0019
    · exact ownerF0020
    · exact ownerF0021
    · exact ownerF0022
    · exact ownerF0023
    · exact ownerF0024
    · exact ownerF0025
    · exact ownerF0026
    · exact ownerF0027
    · exact ownerF0028
    · exact ownerF0029
    · exact ownerF0030
    · exact ownerF0031
    · exact ownerF0032
    · exact ownerF0033
    · exact ownerF0034
    · exact ownerF0035
    · exact ownerF0036
    · exact ownerF0037
    · exact ownerF0038
    · exact ownerF0039
    · exact ownerF0040
    · exact ownerF0041
    · exact ownerF0042
    · exact ownerF0043
    · exact ownerF0044
    · exact ownerF0045
    · exact ownerF0046

theorem source_lookup (i : Position) :
    home (parentKey i.1.1 (rawRow i)) = i.1.2.val ∧
      (ownersOn i.1).get? (key (rawRow i)) = some i.2.val ∧
      oldKeys.contains (parentKey i.1.1 (rawRow i)) = false ∧
      (i.1.1 = true → (ownersOn (false,i.1.2)).get? (parentKey i.1.1 (rawRow i)) = none) := by
  have hm : (packed i,i.2.val) ∈ indexedRows i.1 := by
    simpa only [indexedRows,packed,Nat.zero_add] using mem_numbered (block i.1).words.list 0 i.2.val i.2.isLt
  exact of_decide_eq_true ((List.all_eq_true.mp (all_lookups i.1)) _ hm)

theorem same_grid_key_unique (i j : Position) (hg : i.1.1 = j.1.1)
    (hk : key (rawRow i) = key (rawRow j)) : i = j := by
  have hlow : lower (rawRow i) = lower (rawRow j) := List.ofFn_injective hk
  have hparent : parentKey i.1.1 (rawRow i) = parentKey j.1.1 (rawRow j) := by
    simp only [parentKey,key,hg,hlow]
  have hb : i.1.2.val = j.1.2.val :=
    (source_lookup i).1.symm.trans ((congrArg home hparent).trans (source_lookup j).1)
  have hi := (source_lookup i).2.1
  have hj := (source_lookup j).2.1
  rcases i with ⟨⟨b,k⟩,u⟩
  rcases j with ⟨⟨b',k'⟩,u'⟩
  change b = b' at hg
  subst b'
  have he : k = k' := Fin.ext hb
  subst k'
  rw [hk] at hi
  have hpos : u = u' := Fin.ext (Option.some.inj (hi.symm.trans hj))
  subst u'
  rfl

noncomputable section
open Set

theorem originalBox_eq (r : FifthWireRow) (g : ℕ) (hg : r.grid = (g : ℤ)) (hl : ∀ k, 0 ≤ r.lo k) :
    r.originalBox = indexBox g (lower r) := by
  have hk (k : Fin 5) : (((r.lo k).toNat : ℕ) : ℝ) = (r.lo k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hl k)
  ext t
  simp [FifthWireRow.originalBox, FifthWireRow.lower, FifthWireRow.upper, indexBox, lower, hg, hk]

theorem actual_owner (i : Position) :
    (rawRow i).originalBox = indexBox (grid i.1) (lower (rawRow i)) :=
  originalBox_eq _ _ (row_grid i) (geometry i).1

def parent (i : Position) : BoxKey :=
  if i.1.1 then fineParent (lower (rawRow i)) else lower (rawRow i)

theorem key_of_parent (i : Position) : List.ofFn (parent i) = parentKey i.1.1 (rawRow i) := by
  cases hi : i.1.1 <;> simp [parent, parentKey, key, hi]

theorem contained_in_parent (i : Position) :
    (rawRow i).originalBox ⊆ indexBox 400 (parent i) := by
  rw [actual_owner]
  cases hi : i.1.1
  · simp [grid, parent, hi]
  · simpa [grid, parent, hi] using fine_box_subset_parent (lower (rawRow i))

theorem old_key_recorded (i : ArchiveIndex) : oldKeys.contains (key (archiveRow i)) = true := by
  apply Std.HashSet.contains_iff_mem.mpr
  have h : key (archiveRow i) ∈ Data.P1HistoricalFifthSavedTableData.rows.toList.map key :=
    List.mem_map.mpr ⟨archiveRow i,archiveRow_source_member i,rfl⟩
  simpa [oldKeys] using h

theorem new_box_excludes_old (i : Position) (t : Fin 5 → ℝ) (ht : t ∈ (rawRow i).originalBox) :
    P4AOriginalNewFifthExclusion.outsideOld t := by
  intro o ho
  have hgeo := P1HistoricalFifthTypedBaseGeometry.archiveRow_baseGeometry o
  have oldbox := originalBox_eq (archiveRow o) 400 hgeo.1 (fun k => (by omega : (0 : ℤ) ≤ 1).trans (hgeo.2.2.1 k))
  rw [oldbox] at ho
  have hk := indexBox_owner_unique (by decide : 0 < 400) (contained_in_parent i ht) ho
  have he : parentKey i.1.1 (rawRow i) = key (archiveRow o) := by
    rw [← key_of_parent, hk, key]
  have hx := (source_lookup i).2.2.1
  rw [he, old_key_recorded] at hx
  contradiction

private theorem fine_disjoint_coarse (i j : Position) (hfi : i.1.1 = true) (hcj : j.1.1 = false)
    (t : Fin 5 → ℝ) (hi : t ∈ (rawRow i).originalBox) (hj : t ∈ (rawRow j).originalBox) : False := by
  have he := indexBox_owner_unique (by decide : 0 < 400)
    (contained_in_parent i hi) (contained_in_parent j hj)
  have hk : parentKey i.1.1 (rawRow i) = key (rawRow j) := by
    rw [← key_of_parent,he,key_of_parent,hcj]
    rfl
  have hpj : parentKey j.1.1 (rawRow j) = key (rawRow j) := by simp [parentKey,hcj]
  have hk' := hk.trans hpj.symm
  have hb : i.1.2 = j.1.2 := Fin.ext
    ((source_lookup i).1.symm.trans ((congrArg home hk').trans (source_lookup j).1))
  have hh := (source_lookup i).2.2.2 hfi
  have hj' := (source_lookup j).2.1
  have heq : (false,j.1.2) = j.1 := Prod.ext hcj.symm rfl
  rw [hb,heq,hk,hj'] at hh
  contradiction

theorem boxes_pairwise_disjoint (i j : Position) (hne : i ≠ j) :
    Disjoint (rawRow i).originalBox (rawRow j).originalBox := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  by_cases hg : i.1.1 = j.1.1
  · have hg' : grid i.1 = grid j.1 := by unfold grid; rw [hg]
    rw [actual_owner i, hg'] at hi
    rw [actual_owner j] at hj
    have hpos : 0 < grid j.1 := by unfold grid; split <;> decide
    have he := indexBox_owner_unique hpos hi hj
    exact hne (same_grid_key_unique i j hg (congrArg List.ofFn he))
  · cases hfi : i.1.1 <;> cases hfj : j.1.1
    · exact hg (hfi.trans hfj.symm)
    · exact fine_disjoint_coarse j i hfj hfi t hj hi
    · exact fine_disjoint_coarse i j hfi hfj t hi hj
    · exact hg (hfi.trans hfj.symm)

/-- On an old box the union producer is its original fifth producer. -/
theorem union_eq_original_on_old (o : ArchiveIndex) (e : ℚ) (q : ℕ) (a N : ℝ)
    (pre : List ℕ) (ht : primeHistoryLogCoordinates N 5 pre ∈ (archiveRow o).originalBox) :
    P5OriginalCommonRefinedConstructor.exponent5 (P4AOriginalNewFifthUnion.data e q a) N pre =
      P5OriginalCommonRefinedConstructor.exponent5 (P4AOriginalNewFifthUnion.original e q a) N pre :=
  P4AOriginalNewFifthUnion.union_eq_original_off_new e q a N pre (fun i hi => new_box_excludes_old i _ hi o ht)

/-- At an original new owner the previous implementation used only rank
four. The union supplies this owner's independently admitted row action. -/
theorem before_and_after_on_new (i : Position) (e : ℚ) (q : ℕ) (a N : ℝ) (pre : List ℕ)
    (h5 : pre.length = 5) (j : P1OriginalVariableFifthContinuation.Label5
      (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q))
    (hj : j ∈ P4AOriginalNewFifthUnion.owners i e q a)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ logPrimeMeshCell 0 (19/96)
      (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) j) :
    P5OriginalCommonRefinedConstructor.exponent5 (P4AOriginalNewFifthUnion.original e q a) N pre =
      P5OriginalCommonRefinedConstructor.exponent4 (P4AOriginalNewFifthUnion.original e q a) N
        (rosserAncestor 4 pre) ∧
    P1OriginalFifthRawBoxSelectorEquivalence.rawCandidate (e : ℝ) (rawRow i)
      (primeHistoryLogCoordinates N 5 pre) ≤
      P5OriginalCommonRefinedConstructor.exponent5 (P4AOriginalNewFifthUnion.data e q a) N pre := by
  have hbox := (decodeFifthRows_source_geometry _ _ _ (P4AOriginalNewFifthUnion.rowAt_decodes i e q a j hj) _ ht).2.2.2
  exact ⟨P4AOriginalNewFifthExclusion.common_fifth_eq_fourth_on_complement e q a N pre h5
    (new_box_excludes_old i _ hbox), P4AOriginalNewFifthUnion.new_candidate_le_union i e q a N pre h5 j hj ht⟩

end
end ImbalancedChen.P4AOriginalNewFifthOwners
