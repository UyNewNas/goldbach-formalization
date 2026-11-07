import ImbalancedChen.P4ASymmetricRawOptionOuterAssembly
import ImbalancedChen.P4ASymmetricSixTentRange32Leaf
import ImbalancedChen.P4ASymmetricBRange32Leaf

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
Original below-mu B/six raw Option using the TRUE originalLn32 OLD, NEW
and mass trees. No equality to a unit-log cost or query is asserted. The
selector, crossing rejection, early/equal/chord order, boundary suppression,
raw outer min, single symmetric half and final UP are preserved.
-/
namespace ImbalancedChen.OriginalThirdP4ASymmetricRange32RawOptionDispatch
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites OriginalThirdP4ABalancedSymmetricLeaf
open OriginalThirdP4ASymmetricBLeaf OriginalThirdP4ASymmetricFiniteDispatch
open OriginalThirdP4ASymmetricRawOptionOuterAssembly
open OriginalThirdP4ASixTentRange32Moments OriginalThirdP4ASixTentRange32OldWeight
open P4ASymmetricSixTentRange32Leaf P4ASymmetricBRange32Leaf
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalThirdSymmetricJensenSourceOnly OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdCompactPartitionSourceOnly OriginalThirdSymmetricMassCeilSourceOnly
open P4AOriginalRange32MassCeil20261024zSourceOnly
open P4ASymmetricNewOnlyLeafSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)

def charge32 (x0 x1 z0 z1 high : ℤ) : ℤ :=
  up (high*(symmetricMass32 x0 x1 z0 z1).hi) P160

/-- This query uses NEW32.hi/P160. It is not the old storedGridNew query. -/
def newOut32 (table : CheckedBlockTable) (a b c d : ℚ) : ℤ :=
  readQueryHi160 (assembledRead table.blocks)
    (ordinaryNew32 (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))).hi P160

theorem newOut32_source_tree (table : CheckedBlockTable) (a b c d : ℚ) :
    newOut32 table a b c d = readQueryHi160 (assembledRead table.blocks)
      (sub (mul (sub (sub (ofReal thirdPrefixTheta)
        (ordinaryEx32 (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))))
        (ordinaryEy32 (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))))
        (ordinaryInvZ32 (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))))
        (ofReal 1)).hi P160 := by
  rfl

/-- Same integer-grid NEW32 call, bound by actual original sourceD/H/width
data; both originalLn32 divisors are kept in the gridNew32 operand. -/
theorem newOut32_grid_abi (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/(sourceD:ℚ)) (hb : b=(x1:ℚ)/(sourceD:ℚ))
    (hc : c=(z0:ℚ)/(sourceD:ℚ)) (hd : d=(z1:ℚ)/(sourceD:ℚ))
    (hx : sourceH≤x0) (hz : sourceH≤z0) (hxy : x0<x1) (hzz : z0<z1) :
    newOut32 table a b c d = readQueryHi160 (assembledRead table.blocks)
      (gridNew32 ![x0,x0,z0] ![x1,x1,z1]).hi P160 := by
  have ht := ordinaryNew32_grid_abi ![x0,x0,z0] ![x1,x1,z1]
    (![a,a,c]) (![b,b,d])
    (by intro i; fin_cases i; exact ha; exact ha; exact hc)
    (by intro i; fin_cases i; exact hb; exact hb; exact hd)
    (by intro i; fin_cases i; exact hx; exact hx; exact hz)
    (by intro i; fin_cases i; exact hxy; exact hxy; exact hzz)
  change readQueryHi160 _ (ordinaryNew32 _ _).hi _ = _
  have haVec : OriginalThirdBelowMuBRoundedSourceOnly.realBox (![a,a,c]) =
      symmetricLeft (a:ℝ) (c:ℝ) := by
    funext i
    fin_cases i <;> rfl
  have hbVec : OriginalThirdBelowMuBRoundedSourceOnly.realBox (![b,b,d]) =
      symmetricRight (b:ℝ) (d:ℝ) := by
    funext i
    fin_cases i <;> rfl
  rw [haVec,hbVec] at ht
  rw [ht]

/-- The actual NEW32 early branch, with original range32 guards, SAME reader
and original mass32/UP. No unit-log theorem or primitive query is assumed. -/
theorem original_newOnly32_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value (charge32 x0 x1 z0 z1 (newOut32 table a b c d)) := by
  have hl := symmetric_log32_enclosure_and_guard x0 x1 a b c d ha hb hg hmu
  have hn : Encloses
      (ordinaryNew32 (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ)))
      (newMean (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) :=
    ordinaryNew32_symmetric_encloses hl.1 hl.1 hl.2 hl.2
  have hq := (CheckedBlockTable.query_encloses_all table
    (ordinaryNew32 (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))).hi
    P160 P160_pos).2
  have hqR : actualExtendedThirdLowerFactor
      (value (ordinaryNew32 (symmetricLeft (a:ℝ) (c:ℝ))
        (symmetricRight (b:ℝ) (d:ℝ))).hi)≤value (newOut32 table a b c d) := by
    simpa only [newOut32,value,P160,Int.cast_pow,Int.cast_ofNat] using hq
  have hout := (monotone_actualExtendedThirdLowerFactor hn.2).trans hqR
  have hout0 := (actualExtendedThirdLowerFactor_nonneg _).trans hout
  have hm := (symmetric_mass32_encloses x0 x1 z0 z1 a b c d ha hb hc hd hg
    (symmetric_ratio_le_32 hg hmu)).2
  calc
    _≤prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)*value (newOut32 table a b c d) :=
      original_symmetric_new_only_leaf_upper hg hout
    _≤value (symmetricMass32 x0 x1 z0 z1).hi*value (newOut32 table a b c d) :=
      mul_le_mul_of_nonneg_right hm hout0
    _=value (newOut32 table a b c d)*value (symmetricMass32 x0 x1 z0 z1).hi := by ring
    _≤value (charge32 x0 x1 z0 z1 (newOut32 table a b c d)) := literal_product_UP_ge _ _

def rawChord32 (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Candidate → ℤ
  | .base => symmetricBMeanHigh32 table x0 x1 z0 z1 a b c d
  | .tent s k => symmetricMeanHigh32 table s k x0 x1 z0 z1 a b c d

def chordCost32 (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Candidate → ℤ
  | .base => symmetricBRange32Cost table x0 x1 z0 z1 a b c d
  | .tent s k => symmetricSixTentRange32Cost table s k x0 x1 z0 z1 a b c d

theorem charge_rawChord32 (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (p : Candidate) :
    charge32 x0 x1 z0 z1 (rawChord32 table x0 x1 z0 z1 a b c d p)=
      chordCost32 table x0 x1 z0 z1 a b c d p := by
  cases p <;> rfl

def rawCandidate32 (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (p : Candidate) : Option ℤ := by
  classical
  exact if candidateBadCoefficients p then none
    else if candidateResidual x1 p then
      if candidateLow x1 z1 p<2 ∧ 2<candidateHigh x0 z0 p then none
      else if candidateHigh x0 z0 p≤2 then some (newOut32 table a b c d)
      else if candidateLow x1 z1 p=candidateHigh x0 z0 p then
        some (max 0 (newOut32 table a b c d-
          readQueryLo160 (assembledRead table.blocks)
            (candidateLow x1 z1 p).num ((candidateLow x1 z1 p).den:ℤ)))
      else some (rawChord32 table x0 x1 z0 z1 a b c d p)
    else none

def chargedCandidate32 (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (p : Candidate) : Option ℤ := by
  classical
  exact if candidateBadCoefficients p then none
    else if candidateResidual x1 p then
      if candidateLow x1 z1 p<2 ∧ 2<candidateHigh x0 z0 p then none
      else if candidateHigh x0 z0 p≤2 then some (charge32 x0 x1 z0 z1 (newOut32 table a b c d))
      else if candidateLow x1 z1 p=candidateHigh x0 z0 p then
        some (charge32 x0 x1 z0 z1 (max 0 (newOut32 table a b c d-
          readQueryLo160 (assembledRead table.blocks)
            (candidateLow x1 z1 p).num ((candidateLow x1 z1 p).den:ℤ))))
      else some (chordCost32 table x0 x1 z0 z1 a b c d p)
    else none

theorem rawCandidate32_map (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (p : Candidate) :
    Option.map (charge32 x0 x1 z0 z1) (rawCandidate32 table x0 x1 z0 z1 a b c d p)=
      chargedCandidate32 table x0 x1 z0 z1 a b c d p := by
  classical
  unfold rawCandidate32 chargedCandidate32
  split_ifs <;> simp only [Option.map_none,Option.map_some,charge_rawChord32]

def rawMeanOption32 (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ :=
  match originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀ with
  | none => none
  | some p => rawCandidate32 table x0 x1 z0 z1 a b c d p

def chargedMeanOption32 (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ :=
  match originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀ with
  | none => none
  | some p => chargedCandidate32 table x0 x1 z0 z1 a b c d p

theorem rawMeanOption32_map (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) :
    Option.map (charge32 x0 x1 z0 z1) (rawMeanOption32 table x0 x1 z0 z1 a b c d)=
      chargedMeanOption32 table x0 x1 z0 z1 a b c d := by
  unfold rawMeanOption32 chargedMeanOption32
  cases originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀ with
  | none => rfl
  | some p => exact rawCandidate32_map table x0 x1 z0 z1 a b c d p

theorem selected_chord32_upper (table : CheckedBlockTable) (p : Candidate)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hs : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀=some p)
    (hr : candidateResidual x1 p) (hl : (2:ℚ)≤candidateLow x1 z1 p) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value (chordCost32 table x0 x1 z0 z1 a b c d p) := by
  cases p with
  | base =>
      exact original_symmetric_B_range32_stored_integer_upper table
        x0 x1 z0 z1 a b c d ha hb hc hd hg hmu hl
  | tent s k =>
      obtain ⟨hbranch,hroot⟩ := selected_tent_literal_guards s k x0 x1 z0 z1 hs
      exact original_symmetric_six_tent_range32_stored_integer_upper table s k
        x0 x1 z0 z1 a b c d ha hb hc hd hg hmu hbranch hroot hr hl

/-- Real raw source success supplies a leaf estimate with no caller ratio,
positive rounded-log endpoint, semantic query result or target leaf bound. -/
theorem rawCandidate32_success_integer_upper (table : CheckedBlockTable) (p : Candidate)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (j : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hs : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀=some p)
    (hj : rawCandidate32 table x0 x1 z0 z1 a b c d p=some j) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value (charge32 x0 x1 z0 z1 j) := by
  classical
  unfold rawCandidate32 at hj
  rw [if_neg (candidate_coefficients_pass p)] at hj
  by_cases hr : candidateResidual x1 p
  · rw [if_pos hr] at hj
    by_cases hx : candidateLow x1 z1 p<2 ∧ 2<candidateHigh x0 z0 p
    · rw [if_pos hx] at hj
      cases hj
    · rw [if_neg hx] at hj
      by_cases he : candidateHigh x0 z0 p≤2
      · rw [if_pos he] at hj
        have hjj := Option.some.inj hj
        rw [←hjj]
        exact original_newOnly32_integer_upper table x0 x1 z0 z1 a b c d ha hb hc hd hg hmu
      · rw [if_neg he] at hj
        have hspan := selected_candidate_span p x0 x1 z0 z1 a b c d
          ha hb hc hd hg hmu hs hr
        rw [if_neg (ne_of_lt hspan)] at hj
        have hl : (2:ℚ)≤candidateLow x1 z1 p := by
          by_contra hn
          exact hx ⟨lt_of_not_ge hn,lt_of_not_ge he⟩
        have hjj := Option.some.inj hj
        rw [←hjj,charge_rawChord32]
        exact selected_chord32_upper table p x0 x1 z0 z1 a b c d ha hb hc hd hg hmu hs hr hl
  · rw [if_neg hr] at hj
    cases hj

theorem original_rawMeanOption32_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (j : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hj : rawMeanOption32 table x0 x1 z0 z1 a b c d=some j) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value (charge32 x0 x1 z0 z1 j) := by
  cases hs : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀ with
  | none => simp only [rawMeanOption32,hs] at hj
  | some p =>
      exact rawCandidate32_success_integer_upper table p x0 x1 z0 z1 a b c d j
        ha hb hc hd hg hmu hs (by simpa only [rawMeanOption32,hs] using hj)

theorem rawCandidate32_crossing_none (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (p : Candidate)
    (hx : candidateLow x1 z1 p<2 ∧ 2<candidateHigh x0 z0 p) :
    rawCandidate32 table x0 x1 z0 z1 a b c d p=none := by
  classical
  unfold rawCandidate32
  rw [if_neg (candidate_coefficients_pass p)]
  by_cases hr : candidateResidual x1 p
  · rw [if_pos hr,if_pos hx]
  · rw [if_neg hr]

def rawBoxOption32 (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ := by
  classical
  exact if sourceFull x1 z1 then rawMeanOption32 table x0 x1 z0 z1 a b c d else none

def chargedBoxOption32 (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ := by
  classical
  exact if sourceFull x1 z1 then chargedMeanOption32 table x0 x1 z0 z1 a b c d else none

theorem rawBoxOption32_map (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) :
    Option.map (charge32 x0 x1 z0 z1) (rawBoxOption32 table x0 x1 z0 z1 a b c d)=
      chargedBoxOption32 table x0 x1 z0 z1 a b c d := by
  classical
  unfold rawBoxOption32 chargedBoxOption32
  by_cases hf : sourceFull x1 z1
  · rw [if_pos hf,if_pos hf]
    exact rawMeanOption32_map table x0 x1 z0 z1 a b c d
  · rw [if_neg hf,if_neg hf]
    rfl

theorem rawBoxOption32_boundary (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (hf : ¬sourceFull x1 z1) :
    rawBoxOption32 table x0 x1 z0 z1 a b c d=none := by
  classical
  exact if_neg hf

theorem charge32_mono (x0 x1 z0 z1 : ℤ)
    (hm : 0≤(symmetricMass32 x0 x1 z0 z1).hi) : Monotone (charge32 x0 x1 z0 z1) := by
  intro u v huv
  exact P0SymmetricOuterMinBridge.up_mono P160_pos
    (mul_le_mul_of_nonneg_right huv hm)

theorem charge32_min (x0 x1 z0 z1 u v : ℤ)
    (hm : 0≤(symmetricMass32 x0 x1 z0 z1).hi) :
    charge32 x0 x1 z0 z1 (min u v)=min (charge32 x0 x1 z0 z1 u) (charge32 x0 x1 z0 z1 v) := by
  rcases le_total u v with huv | hvu
  · rw [min_eq_left huv,min_eq_left (charge32_mono x0 x1 z0 z1 hm huv)]
  · rw [min_eq_right hvu,min_eq_right (charge32_mono x0 x1 z0 z1 hm hvu)]

def sourceBoxUpper32 (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (fallbackHigh : ℤ) : ℤ :=
  charge32 x0 x1 z0 z1
    (applyOptionalMean fallbackHigh (rawBoxOption32 table x0 x1 z0 z1 a b c d))

/-- Original raw min followed by one TRUE mass32/UP, with no false unit-log
mass identity and no boundary full-cell premise. -/
theorem sourceBoxUpper32_eq_charged_optional (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (fallbackHigh : ℤ)
    (hm : 0≤(symmetricMass32 x0 x1 z0 z1).hi) :
    sourceBoxUpper32 table x0 x1 z0 z1 a b c d fallbackHigh=
      applyOptionalMean (charge32 x0 x1 z0 z1 fallbackHigh)
        (chargedBoxOption32 table x0 x1 z0 z1 a b c d) := by
  rw [←rawBoxOption32_map]
  unfold sourceBoxUpper32
  cases ho : rawBoxOption32 table x0 x1 z0 z1 a b c d with
  | none => simp only [ho,Option.map_none,applyOptionalMean]
  | some j =>
      simpa only [ho,Option.map_some,applyOptionalMean] using
        charge32_min x0 x1 z0 z1 fallbackHigh j hm

theorem sourceBoxUpper32_boundary (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (fallbackHigh : ℤ) (hf : ¬sourceFull x1 z1) :
    sourceBoxUpper32 table x0 x1 z0 z1 a b c d fallbackHigh=
      charge32 x0 x1 z0 z1 fallbackHigh := by
  rw [sourceBoxUpper32,rawBoxOption32_boundary table x0 x1 z0 z1 a b c d hf]
  rfl

theorem mass32_hi_nonneg (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) : 0≤(symmetricMass32 x0 x1 z0 z1).hi := by
  have hm := (symmetric_mass32_encloses x0 x1 z0 z1 a b c d ha hb hc hd hg
    (symmetric_ratio_le_32 hg hmu)).2
  exact value_le_iff.mp (by
    simpa only [value_zero] using (symmetric_prism_mass_pos hg).le.trans hm)

/-- Geometry-bound exact outer identity: all range/log/mass guards are
internal. The sourceBoxUpper32 definition and boundary theorem stay general. -/
theorem sourceBoxUpper32_eq_charged_optional_of_geometry (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (fallbackHigh : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) :
    sourceBoxUpper32 table x0 x1 z0 z1 a b c d fallbackHigh=
      applyOptionalMean (charge32 x0 x1 z0 z1 fallbackHigh)
        (chargedBoxOption32 table x0 x1 z0 z1 a b c d) := by
  exact sourceBoxUpper32_eq_charged_optional table x0 x1 z0 z1 a b c d fallbackHigh
    (mass32_hi_nonneg x0 x1 z0 z1 a b c d ha hb hc hd hg hmu)

/-- Charged success is derived from the actual raw Option map, rather than
accepting a desired integer-cost identity from a caller. -/
theorem original_chargedMeanOption32_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (cost : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hcost : chargedMeanOption32 table x0 x1 z0 z1 a b c d=some cost) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value cost := by
  have hm := rawMeanOption32_map table x0 x1 z0 z1 a b c d
  rw [hcost] at hm
  cases hr : rawMeanOption32 table x0 x1 z0 z1 a b c d with
  | none => simp only [hr,Option.map_none] at hm
  | some j =>
      have he : charge32 x0 x1 z0 z1 j=cost := by
        exact Option.some.inj (by simpa only [hr,Option.map_some] using hm)
      rw [←he]
      exact original_rawMeanOption32_integer_upper table x0 x1 z0 z1 a b c d j
        ha hb hc hd hg hmu hr

end
end ImbalancedChen.OriginalThirdP4ASymmetricRange32RawOptionDispatch
