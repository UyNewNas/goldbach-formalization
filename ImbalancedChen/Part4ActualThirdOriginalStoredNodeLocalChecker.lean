import ImbalancedChen.ActualThirdOriginalRationalQuery
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / MAIN OPEN30.

The proposed import means the exact seven-module V4 chain bound by recipe
SHA4e99ee817cdf636c229253ce4ffb7eb0b8e59eee1374bc9683c16382caae43a6.
Its seventh source is fb71227e943daa7169fd03b896705691dec5a43e942df76e9da63ec687d1aa43;
the literal node supplier is 4fd761f70f6629691f66ec4c3b65e8ac336706ea0cd9d5a0eda5cc64cf2c809c.
These dependencies remain SOURCEONLY; this text makes no installation claim.

This is a finite certificate SOUNDNESS interface, not a replay result.
Four supplied integer arrays have exactly the original 196609 slots, indexed
0..196608. They are the proposed decoding target for ChordTable's Llo,Lhi,
Hlo,Hhi, with n=16384, maximum=12, P=2^112. No array values are supplied here.
The already read original JSON outputs contain summary/query/cell-stream
information, not a serialized full four-array witness. A future exporter,
exact decoder and byte/hash binding remain required; a digest alone never
constructs these arrays or proves any Boolean below true.

The checker computes ONLY original finite integer field equalities. It checks
the uniform initialized prefix0..32768 and all updates32769..196608 in40
blocks of4096. Expected updates read the supplied arrays at the literal prior
indices; they never evaluate literalNodeState or originalFinalNodes. The
checker has no real/analytic enclosure field or expected final query bound.
No Classical decidability instance is introduced in the checker definitions.

The theorem proves that IF these exact finite checks are true, stored nodes
enclose the actual L,H by the existing noncircular update-preservation theorem.
It does not claim a computed table/check=true, equality of imported bytes with
a historical in-memory Python object, or completed Lean elaboration. All
computational obligations are explicit and remain unperformed here.
-/

namespace ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly
open ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

/- The checker call graph below uses its own pure integer transcriptions.
This avoids depending on code generation for arithmetic declarations inside
the mathematical parent's noncomputable sections. Their exact correspondence
is proved by unfolding, rather than assumed as a checker input. -/
def integerP : ℤ := 2^112
def integerWeightA (j : ℕ) : ℤ :=
  30*(j : ℤ)^4-10*(j : ℤ)^3+5*(j : ℤ)^2-3*(j : ℤ)
def integerWeightB (j : ℕ) : ℤ :=
  30*(j : ℤ)^4-20*(j : ℤ)^3+15*(j : ℤ)^2-12*(j : ℤ)
def integerWeightC (j : ℕ) : ℤ :=
  60*(j : ℤ)^4-30*(j : ℤ)^3+20*(j : ℤ)^2-15*(j : ℤ)
def integerWeightDen (j : ℕ) : ℤ := 60*(j : ℤ)^5
def integerWeight0Lo (j : ℕ) : ℤ := integerWeightA j*integerP/integerWeightDen j
def integerWeight0Hi (j : ℕ) : ℤ := -(-((integerWeightA j+2)*integerP)/integerWeightDen j)
def integerWeight1Lo (j : ℕ) : ℤ := integerWeightB j*integerP/integerWeightDen j
def integerWeight1Hi (j : ℕ) : ℤ := -(-((integerWeightB j+10)*integerP)/integerWeightDen j)
def integerLogLo (j : ℕ) : ℤ := integerWeightC j*integerP/integerWeightDen j
def integerLogHi (j : ℕ) : ℤ := -(-((integerWeightC j+12)*integerP)/integerWeightDen j)
def integerChordLo (j : ℕ) (a b : ℤ) : ℤ :=
  (a*integerWeight0Lo j+b*integerWeight1Lo j)/integerP
def integerChordHi (j : ℕ) (a b : ℤ) : ℤ :=
  -(-(a*integerWeight0Hi j+b*integerWeight1Hi j)/integerP)
def integerError (j : ℕ) : ℤ :=
  -(-integerP/(12*16384*(j : ℤ)*((j : ℤ)-16384)))
def integerInitial : OriginalNode := ⟨0,0,integerP,integerP⟩

theorem integerInitial_eq_original : integerInitial = initialNode := by
  rfl

/-- Literal four original arrays, with exact dimensions as typed data.
Size proofs certify shape only; all numerical values remain untrusted. -/
structure StoredFourArrays where
  Llo : Array ℤ
  Lhi : Array ℤ
  Hlo : Array ℤ
  Hhi : Array ℤ
  Llo_size : Llo.size = 196609
  Lhi_size : Lhi.size = 196609
  Hlo_size : Hlo.size = 196609
  Hhi_size : Hhi.size = 196609

/-- Total lookup. Every certified index is inside the typed bounds.
The defaults mirror the original initialized arrays and are never used
to certify an out-of-range index. -/
def StoredFourArrays.read (T : StoredFourArrays) (i : ℕ) : OriginalNode :=
  { Llo := T.Llo[i]?.getD 0
    Lhi := T.Lhi[i]?.getD 0
    Hlo := T.Hlo[i]?.getD integerP
    Hhi := T.Hhi[i]?.getD integerP }

theorem legal_index_in_bounds (T : StoredFourArrays) {i : ℕ}
    (hi : i ≤ 196608) :
    i < T.Llo.size ∧ i < T.Lhi.size ∧ i < T.Hlo.size ∧ i < T.Hhi.size := by
  rw [T.Llo_size, T.Lhi_size, T.Hlo_size, T.Hhi_size]
  omega

/-- Four decidable INTEGER equalities, not an analytic envelope test. -/
def nodeEqCheck (x y : OriginalNode) : Bool :=
  decide (x.Llo = y.Llo ∧ x.Lhi = y.Lhi ∧ x.Hlo = y.Hlo ∧ x.Hhi = y.Hhi)

theorem nodeEqCheck_sound {x y : OriginalNode} (h : nodeEqCheck x y = true) : x = y := by
  have he : x.Llo = y.Llo ∧ x.Lhi = y.Lhi ∧ x.Hlo = y.Hlo ∧ x.Hhi = y.Hhi :=
    of_decide_eq_true h
  cases x
  cases y
  simpa only [OriginalNode.mk.injEq] using he

/-- Original local integer update, with ordinary decidability for its
three natural-index branches. The exact integer transcriptions above
retain P112, denominator12, both floor/ceiling rounds and max.
This evaluates a SINGLE row using stored inputs, never a recursive table. -/
def checkedUpdate (i : ℕ) (old : ℕ → OriginalNode) : OriginalNode :=
  if i ≤ 32768 then integerInitial else
  let p := old (i-1)
  let j := i-16385
  { Llo := if i ≤ 65536 then p.Llo+integerLogLo j else
      max p.Llo (p.Llo+integerChordLo j (old j).Hlo (old (j+1)).Hlo-integerError j)
    Lhi := if i ≤ 65536 then p.Lhi+integerLogHi j else
      p.Lhi+integerChordHi j (old j).Hhi (old (j+1)).Hhi
    Hlo := if i ≤ 49152 then integerP else
      p.Hlo+integerChordLo j (old j).Llo (old (j+1)).Llo
    Hhi := if i ≤ 49152 then integerP else
      p.Hhi+integerChordHi j (old j).Lhi (old (j+1)).Lhi+integerError j }

theorem checkedUpdate_eq_original (i : ℕ) (old : ℕ → OriginalNode) :
    checkedUpdate i old = originalNodeUpdate i old := by
  rfl

theorem checked_update_read_indices {i : ℕ} (hi : 32769 ≤ i) (himax : i ≤ 196608) :
    i-1 ≤ 196608 ∧ delayedIndex i ≤ 196608 ∧ delayedIndex i+1 ≤ 196608 ∧
      i-1 < i ∧ delayedIndex i < i ∧ delayedIndex i+1 < i := by
  unfold delayedIndex
  omega

def checkStep (T : StoredFourArrays) (i : ℕ) : Bool :=
  nodeEqCheck (T.read i) (checkedUpdate i T.read)

theorem checkStep_sound {T : StoredFourArrays} {i : ℕ}
    (h : checkStep T i = true) : T.read i = originalNodeUpdate i T.read := by
  exact (nodeEqCheck_sound h).trans (checkedUpdate_eq_original i T.read)

/-- Includes all originally initialized slots, not merely the analytic
base node32768. No assertion about an unchecked prefix is silently used. -/
def checkInitialPrefix (T : StoredFourArrays) : Bool :=
  (List.range 32769).all (fun i => nodeEqCheck (T.read i) integerInitial)

theorem checkInitialPrefix_sound {T : StoredFourArrays}
    (h : checkInitialPrefix T = true) {i : ℕ} (hi : i ≤ 32768) :
    T.read i = initialNode := by
  have he : T.read i = integerInitial := nodeEqCheck_sound
    (List.all_eq_true.mp h i (List.mem_range.mpr (by omega)))
  exact he.trans integerInitial_eq_original

/-- Reusable arbitrary finite update block. A block checks only its own
rows. Whole-table soundness requires every prescribed block, so a supplied
earlier-row value is never certified merely because a later block read it. -/
def checkBlock (T : StoredFourArrays) (lo count : ℕ) : Bool :=
  (List.range count).all (fun k => checkStep T (lo+k))

theorem checkBlock_step {T : StoredFourArrays} {lo count : ℕ}
    (h : checkBlock T lo count = true) {k : ℕ} (hk : k < count) :
    checkStep T (lo+k) = true := by
  exact List.all_eq_true.mp h k (List.mem_range.mpr hk)

theorem checkBlock_sound {T : StoredFourArrays} {lo count : ℕ}
    (h : checkBlock T lo count = true) {k : ℕ} (hk : k < count) :
    T.read (lo+k) = originalNodeUpdate (lo+k) T.read := by
  exact checkStep_sound (checkBlock_step h hk)

/-- Exactly40 blocks partition the163840 original update rows. -/
def checkChunk (T : StoredFourArrays) (b : ℕ) : Bool :=
  checkBlock T (32769+4096*b) 4096

def checkAllChunks (T : StoredFourArrays) : Bool :=
  checkInitialPrefix T && (List.range 40).all (fun b => checkChunk T b)

/-- Arithmetic coverage of the fixed chunks. Premises are only exact
finite Boolean checks; no target analytic enclosure is a hypothesis. -/
theorem checkAllChunks_local_equations {T : StoredFourArrays}
    (h : checkAllChunks T = true) :
    (∀ i : ℕ, i ≤ 32768 → T.read i = initialNode) ∧
      (∀ i : ℕ, 32769 ≤ i → i ≤ 196608 →
        T.read i = originalNodeUpdate i T.read) := by
  have hh : checkInitialPrefix T = true ∧
      (List.range 40).all (fun b => checkChunk T b) = true := by
    simpa only [checkAllChunks, Bool.and_eq_true] using h
  refine ⟨fun i hi => checkInitialPrefix_sound hh.1 hi, ?_⟩
  intro i hi hlo
  let b := (i-32769)/4096
  let k := (i-32769)%4096
  have hb : b < 40 := by dsimp [b]; omega
  have hk : k < 4096 := by dsimp [k]; omega
  have he : 32769+4096*b+k = i := by dsimp [b, k]; omega
  have hchunk : checkChunk T b = true :=
    List.all_eq_true.mp hh.2 b (List.mem_range.mpr hb)
  have hrow : T.read (32769+4096*b+k) =
      originalNodeUpdate (32769+4096*b+k) T.read := checkBlock_sound hchunk hk
  simpa only [he] using hrow

/-- THE certificate soundness consumer. The local stored equations are
used in strong induction; only strictly earlier verified rows feed the
existing actual update theorem. No saved enclosure appears as a premise.
This proves enclosure, not that a historical JSON contains these arrays. -/
theorem checked_stored_nodes_enclose {T : StoredFourArrays}
    (h : checkAllChunks T = true) :
    ∀ i : ℕ, 32768 ≤ i → i ≤ 196608 → NodeEncloses (T.read i) i := by
  rcases checkAllChunks_local_equations h with ⟨hinit, hsteps⟩
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hlow hhigh
      by_cases hi : i = 32768
      · subst i
        rw [hinit 32768 (by omega)]
        exact initialNode_encloses
      · have hi' : 32769 ≤ i := by omega
        rw [hsteps i hi' hhigh]
        apply originalNodeUpdate_preserves actualWeightedCellRemainders i hlow T.read
        intro j hj hjlow
        exact ih j hj hjlow (by omega)

/-- A fixed supplied table and its single exact finite check obligation.
After this is proved once, future query proofs read the stored endpoints
and this theorem, without reducing literalNodeState196608 per query. -/
structure CheckedStoredTable where
  data : StoredFourArrays
  checked : checkAllChunks data = true

theorem CheckedStoredTable.encloses (T : CheckedStoredTable) (i : ℕ)
    (hi : 32768 ≤ i) (himax : i ≤ 196608) :
    NodeEncloses (T.data.read i) i := by
  exact checked_stored_nodes_enclose T.checked i hi himax

end ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly
