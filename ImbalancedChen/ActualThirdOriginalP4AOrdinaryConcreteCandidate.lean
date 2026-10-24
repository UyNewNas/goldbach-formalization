import ImbalancedChen.ActualThirdOriginalSixTentOrdinaryMassCeil
import ImbalancedChen.ActualThirdOriginalPositive256LogIntegerGuards

/-!
SOURCEONLY / UNCOMPILED / MAIN OPEN30.
The first import means the frozen 20261024w AllBranches-V2 draft.
This is a concrete original-grid ordinary xz/rise candidate. It is not
claimed to belong to the historical adaptive tree or saved cell stream.
Only the SAME-reader CheckedBlockTable is left as an input. All coordinates,
literal guards, endpoints, query outputs and candidate UP are fixed here.
-/
namespace ImbalancedChen.OriginalThirdP4AOrdinaryConcreteCandidateSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdSixTentOrdinaryMassCeilSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedOldWeightSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

def rawLo : Fin 3 → ℤ := ![8160*2^24,4800*2^24,1152*2^24]
def rawHi : Fin 3 → ℤ := ![8161*2^24,4801*2^24,1153*2^24]
def leafA : BoxPoint := ![(8160:ℝ)/48000,4800/48000,1152/48000]
def leafB : BoxPoint := ![(8161:ℝ)/48000,4801/48000,1153/48000]
def oldLow : ℚ := literalTentEndpoint .xz .rise rawHi (48000*2^24)
def oldHigh : ℚ := literalTentEndpoint .xz .rise rawLo (48000*2^24)

/-- These fields are constructed from one immutable reader. There are no
saved-output equalities or desired semantic inequalities among the inputs. -/
def queryFl (table : CheckedBlockTable) : ℤ :=
  readQueryLo160 (assembledRead table.blocks) oldLow.num (oldLow.den:ℤ)
def queryFh (table : CheckedBlockTable) : ℤ :=
  readQueryLo160 (assembledRead table.blocks) oldHigh.num (oldHigh.den:ℤ)
def queryOut (table : CheckedBlockTable) : ℤ :=
  readQueryHi160 (assembledRead table.blocks) (ordinaryNew leafA leafB).hi P160
def candidateHigh (table : CheckedBlockTable) : ℤ :=
  meanHigh (ordinaryTentWeight .xz .rise leafA leafB oldLow oldHigh).lo
    (ordinaryTentWeight .xz .rise leafA leafB oldLow oldHigh).hi
    (queryFl table) (queryFh table) (queryOut table)
def candidateUpper (table : CheckedBlockTable) : ℤ :=
  literalOrdinaryUpper rawLo rawHi (candidateHigh table)

theorem leafA_bind (i : Fin 3) :
    leafA i=(rawLo i:ℝ)/((48000*2^24:ℤ):ℝ) := by
  fin_cases i <;> norm_num [leafA,rawLo]

theorem leafB_bind (i : Fin 3) :
    leafB i=(rawHi i:ℝ)/((48000*2^24:ℤ):ℝ) := by
  fin_cases i <;> norm_num [leafB,rawHi]

theorem leaf_positive (i : Fin 3) : 0<leafA i := by
  fin_cases i <;> norm_num [leafA]

theorem leaf_width (i : Fin 3) : leafA i<leafB i := by
  fin_cases i <;> norm_num [leafA,leafB]

theorem leaf_ratio_one (i : Fin 2) :
    1≤leafB i.castSucc/leafA i.castSucc := by
  fin_cases i <;> norm_num [leafA,leafB]

theorem leaf_ratio_two (i : Fin 2) :
    leafB i.castSucc/leafA i.castSucc≤2 := by
  fin_cases i <;> norm_num [leafA,leafB]

/-- The first rounded log term already has lower endpoint >=1. No call
evaluates the 256-term interval log, and positivity is not assumed. -/
theorem leaf_log_positive (i : Fin 2) :
    0<(originalLnUnit (leafB i.castSucc/leafA i.castSucc)).lo := by
  have hfirst : (1:ℤ)≤
      (ofReal (1-1/(leafB i.castSucc/leafA i.castSucc))).lo := by
    change (1:ℤ)≤⌊(1-1/(leafB i.castSucc/leafA i.castSucc))*(P160:ℝ)⌋
    apply Int.le_floor.mpr
    fin_cases i <;> norm_num [leafA,leafB,P160]
  exact (by norm_num : (0:ℤ)<1).trans_le
    (hfirst.trans (originalLnUnit_lo_ge_first (leaf_ratio_one i) (leaf_ratio_two i)))

theorem leaf_ordinary : ¬(rawLo 0=rawLo 1 ∧ rawHi 0=rawHi 1) := by
  exact ordinary_raw_not_symmetric rawLo rawHi (48000*2^24) leafA leafB
    leafA_bind leafB_bind leaf_width (by norm_num [leafA,leafB])

/-- This concrete instance exercises the original terminal OLD query
branch. In particular the new all-branch supplier is actually necessary. -/
theorem old_endpoints_above_twelve : (12:ℚ)<oldLow ∧ (12:ℚ)<oldHigh := by
  norm_num [oldLow,oldHigh,literalTentEndpoint,rawLo,rawHi,
    literalTentX,literalTentY,literalTentZ]

theorem literal_queries_enclose (table : CheckedBlockTable) :
    value (queryFl table)≤actualExtendedThirdLowerFactor (oldLow:ℝ) ∧
    value (queryFh table)≤actualExtendedThirdLowerFactor (oldHigh:ℝ) ∧
    actualExtendedThirdLowerFactor (ordinaryNewQuery leafA leafB:ℝ)≤
      value (queryOut table) := by
  exact ordinary_three_stored_queries table leafA leafB oldLow oldHigh

/-- A genuine integral candidate with all cell-specific obligations proved.
No saved integer, kernel upper bound or conclusion-equivalent premise is
assumed. Selection among minorant candidates and the final box minimum are
separate obligations, as is membership in the historical adaptive tree. -/
theorem concrete_ordinary_candidate_upper (table : CheckedBlockTable) :
    (∫ t in compactRegion ∩ Icc leafA leafB, compactKernel t)≤
      value (candidateUpper table) := by
  have hlowQ : (2:ℚ)≤oldLow := by
    exact (by norm_num : (2:ℚ)≤12).trans old_endpoints_above_twelve.1.le
  have hlow : (2:ℝ)≤(oldLow:ℝ) := by exact_mod_cast hlowQ
  have hbranch : -50*(48000*2^24:ℤ)+256*
      (literalTentX .xz*rawHi 0+literalTentY .xz*rawHi 1+
        literalTentZ .xz*rawHi 2)≤0 := by
    norm_num [rawHi,literalTentX,literalTentY,literalTentZ]
  have hroot : (48000*2^24:ℤ)+literalTentX .xz*rawHi 0+
      literalTentY .xz*rawHi 1+literalTentZ .xz*rawHi 2≤2*481573208064 := by
    norm_num [rawHi,literalTentX,literalTentY,literalTentZ]
  have hres : (0:ℤ)<(48000*2^24:ℤ)+(literalTentX .xz-2)*rawHi 0+
      (literalTentY .xz-2)*rawHi 1 := by
    norm_num [rawHi,literalTentX,literalTentY]
  exact original_selected_tent_stored_integer_upper table .xz .rise rawLo rawHi
    (48000*2^24) 481573208064 leafA leafB oldLow oldHigh
    (queryFl table) (queryFh table) (queryOut table)
    rfl rfl leafA_bind leafB_bind leaf_positive leaf_width
    (by norm_num [leafA]) (by norm_num [leafA,leafB])
    (by norm_num [leafA,leafB]) (by norm_num [leafB,VariableEnvelope.mu])
    (by norm_num [leafB,thirdPrefixTheta]) hbranch hroot hres
    rfl rfl hlow leaf_ratio_two leaf_log_positive rfl rfl rfl

end
end ImbalancedChen.OriginalThirdP4AOrdinaryConcreteCandidateSourceOnly
