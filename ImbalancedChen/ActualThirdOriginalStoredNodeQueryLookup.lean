import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.ActualThirdOriginalRationalQuery

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30.
Missing stored-reader lookup composition. Existing page/block assembly and
analytic node enclosure inductions are reused, not reimplemented. The new
structural invariant establishes equality of the checked stored lookup and
exact finite recurrence, including total-reader defaults beyond the table.
No concrete CheckedBlockTable is constructed by this module. -/
namespace ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredNodeCertificateSourceOnly OriginalU2CoupledRecurrenceSourceOnly

/-- The initialized prefix has 32769 entries, including index 32768.
Forty update blocks of 4096 give exactly the four original array lengths. -/
theorem original_stored_layout_length : 32769+40*4096=196609 := by norm_num

/-- Exact block/offset lookup; only legal slots and offsets are claimed. -/
theorem assembledRead_block_offset (blocks : ℕ → Block) (b k : ℕ)
    (hb : b < 40) (hk : k < 4096) :
    assembledRead blocks (32769+4096*b+k)=toOriginal ((blocks b).read k) := by
  have hpre : ¬ 32769+4096*b+k ≤ 32768 := by omega
  have hlast : 32769+4096*b+k ≤ 196608 := by omega
  have hdiv : (32769+4096*b+k-32769)/4096=b := by omega
  have hmod : (32769+4096*b+k-32769)%4096=k := by omega
  simp only [assembledRead,assembledRawRead,if_neg hpre,if_pos hlast,hdiv,hmod]

/-- The total reader's out-of-table branch is the original initializer,
not a claim that any out-of-range stored array entry has been certified. -/
theorem assembledRead_after_table (blocks : ℕ → Block) (i : ℕ) (hi : 196608 < i) :
    assembledRead blocks i=initialNode := by
  have hp : ¬ i ≤ 32768 := by omega
  have hm : ¬ i ≤ 196608 := by omega
  simp only [assembledRead,assembledRawRead,if_neg hp,if_neg hm]
  exact (show toOriginal rawInitial=integerInitial from rfl).trans integerInitial_eq_original

/-- The exact original update only reads earlier rows. This is arithmetic
congruence, not an inference from overlapping numerical enclosures. -/
theorem originalNodeUpdate_congr_prior (i : ℕ) (f g : ℕ → OriginalNode)
    (h : ∀ j, j < i → f j=g j) : originalNodeUpdate i f=originalNodeUpdate i g := by
  by_cases hi : i ≤ 32768
  · simp only [originalNodeUpdate,if_pos hi]
  · have he := delayed_nodes_earlier i (by omega : 32769 ≤ i)
    have hp := h (i-1) he.2.2
    have hj := h (delayedIndex i) he.1
    have hn := h (delayedIndex i+1) he.2.1
    simp only [originalNodeUpdate,if_neg hi,hp,hj,hn]

/-- Structural finite-state uniqueness. This new invariant does not repeat
literalNodeState_encloses or reprove any analytic recurrence/rounding result.
Every equation in hstep is an exact checked equality of all four integers. -/
theorem checked_reader_state_characterization (read : ℕ → OriginalNode)
    (hprefix : ∀ i, i ≤ 32768 → read i=initialNode)
    (hstep : ∀ i, 32769 ≤ i → i ≤ 196608 → read i=originalNodeUpdate i read)
    (k : ℕ) (hk : k ≤ 196608) :
    ∀ i, literalNodeState k i=if i ≤ k then read i else initialNode := by
  revert hk
  induction k with
  | zero =>
      intro _ i
      by_cases hi : i=0
      · subst i
        simp only [literalNodeState,if_pos (Nat.le_refl 0),hprefix 0 (by omega)]
        rfl
      · have hn : ¬ i ≤ 0 := by omega
        simp only [literalNodeState,if_neg hn]
        rfl
  | succ k ih =>
      intro hk
      have ih' := ih (by omega : k ≤ 196608)
      intro i
      by_cases he : i=k+1
      · subst i
        have hlocal : read (k+1)=originalNodeUpdate (k+1) read := by
          by_cases hp : k+1 ≤ 32768
          · rw [hprefix (k+1) hp]
            simp only [originalNodeUpdate,if_pos hp]
          · exact hstep (k+1) (by omega) hk
        have hc : originalNodeUpdate (k+1) (literalNodeState k)=
            originalNodeUpdate (k+1) read := by
          apply originalNodeUpdate_congr_prior
          intro j hj
          simpa only [if_pos (show j ≤ k by omega)] using ih' j
        simpa only [literalNodeState,if_pos (Nat.le_refl (k+1)),
          if_pos (show k+1=k+1 from rfl), ite_true] using hc.trans hlocal.symm
      · have hold : literalNodeState (k+1) i=literalNodeState k i := by
          simp only [literalNodeState,if_neg he]
        rw [hold,ih' i]
        by_cases hi : i ≤ k
        · rw [if_pos hi,if_pos (show i ≤ k+1 by omega)]
        · rw [if_neg hi,if_neg (show ¬ i ≤ k+1 by omega)]

/-- Extract exact local equations from all 40 checks for ONE immutable reader.
The finite block/page checking is a remaining certificate obligation. -/
theorem CheckedBlockTable.local_equations (T : CheckedBlockTable)
    (i : ℕ) (hi : 32769 ≤ i) (hmax : i ≤ 196608) :
    assembledRead T.blocks i=originalNodeUpdate i (assembledRead T.blocks) := by
  let b := (i-32769)/4096
  let k := (i-32769)%4096
  have hb : b < 40 := by dsimp [b]; omega
  have hk : k < 4096 := by dsimp [k]; omega
  have he : 32769+4096*b+k=i := by dsimp [b,k]; omega
  have hs := readCheckBlock_sound (T.checked ⟨b,hb⟩) hk
  simpa only [he] using hs

/-- Equality is justified by the EXACT checks, not by NodeEncloses. It allows
accepted queries to be reused without evaluating the 196608-step recursion. -/
theorem CheckedBlockTable.read_eq_original (T : CheckedBlockTable) :
    assembledRead T.blocks=originalFinalNodes := by
  have hp : ∀ i, i ≤ 32768 → assembledRead T.blocks i=initialNode := by
    intro i hi
    exact readCheckPrefix_sound (assembledRead_prefix_checked T.blocks) hi
  have hstate := checked_reader_state_characterization (assembledRead T.blocks)
    hp (CheckedBlockTable.local_equations T) 196608 (by omega)
  funext i
  have hs := hstate i
  change assembledRead T.blocks i=literalNodeState 196608 i
  by_cases hi : i ≤ 196608
  · simpa only [if_pos hi] using hs.symm
  · rw [assembledRead_after_table T.blocks i (by omega)]
    simpa only [if_neg hi] using hs.symm

/-- Literal original lower query with only the lookup function exposed.
All clamp, divmod, interpolation, final division and 2^48 scaling are unchanged. -/
def readQueryLo160 (read : ℕ → OriginalNode) (a b : ℤ) : ℤ :=
  (if a ≤ 2*b then 0 else if 12*b < a then (read 196608).Llo/12 else
    (let i := literalQueryIndex a b
     let r := a*16384%b
     let num := if r=0 then (read i).Llo else
       ((read i).Llo*(b-r)+(read (i+1)).Llo*r)/b
     num*b/a))*2^48

/-- The original ceiling curvature allowance remains queryError i. -/
def readQueryHi160 (read : ℕ → OriginalNode) (a b : ℤ) : ℤ :=
  (if a ≤ 2*b then 0 else if 12*b < a then -(-(read 196608).Hhi/12) else
    (let i := literalQueryIndex a b
     let r := a*16384%b
     let num := if r=0 then (read i).Lhi else
       -(-((read i).Lhi*(b-r)+(read (i+1)).Lhi*r)/b)+queryError i;
     -(-(num*b)/a)))*2^48

/-- These are definitional identities with the accepted exact integer query. -/
theorem readQuery_original (a b : ℤ) :
    readQueryLo160 originalFinalNodes a b=literalQueryLo160 a b ∧
    readQueryHi160 originalFinalNodes a b=literalQueryHi160 a b := by
  exact ⟨rfl,rfl⟩

theorem CheckedBlockTable.query_eq_original (T : CheckedBlockTable) (a b : ℤ) :
    readQueryLo160 (assembledRead T.blocks) a b=literalQueryLo160 a b ∧
    readQueryHi160 (assembledRead T.blocks) a b=literalQueryHi160 a b := by
  rw [CheckedBlockTable.read_eq_original T]
  exact readQuery_original a b

/-- Stored lookup query soundness obtained solely by exact composition with
accepted RationalQuery. This does not construct the all-40 checked table. -/
theorem CheckedBlockTable.compact_query_encloses (T : CheckedBlockTable)
    (a b : ℤ) (hb : 0 < b) (ha2 : 2*b ≤ a) (ha12 : a ≤ 12*b) :
    (readQueryLo160 (assembledRead T.blocks) a b:ℝ)/2^160 ≤
      actualExtendedThirdLowerFactor ((a:ℝ)/(b:ℝ)) ∧
    actualExtendedThirdLowerFactor ((a:ℝ)/(b:ℝ)) ≤
      (readQueryHi160 (assembledRead T.blocks) a b:ℝ)/2^160 := by
  have he := CheckedBlockTable.query_eq_original T a b
  rw [he.1,he.2]
  exact literal_compact_query_160bit_encloses a b hb ha2 ha12

end ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly
