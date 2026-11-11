import ImbalancedChen.Certificates.P2HistoricalThirdSelector

/-!
P2 SOURCE ONLY / UNCOMPILED.
Complete ordinary below-mu optional-mean consumption for the historically
ordered selector. The originalMeanUpperTail, its exact boundary conventions,
same-reader queries, B/tent weights and all analytic suppliers are reused.
A rejected mean is paid by the full fallback, not discarded from a leaf list.
This is the existing P160/P112 backend, not a historical Q80 cost ABI proof.
-/
namespace ImbalancedChen.Certificates.P2HistoricalThirdMeanDispatch
noncomputable section

open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdSixTentOrdinaryMassCeilSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
open OriginalThirdP4AOrdinaryBCandidateSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly
open OriginalThirdBelowMuBRoundedSourceOnly (bLowQ bHighQ rawWeight cast_bLowQ cast_bHighQ)
open OriginalThirdP4AOrdinaryEarlyReturnSourceOnly
open OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly
open OriginalThirdP4ASixTentRange32Moments
open OriginalThirdP4AOrdinarySixTentRange32Leaf
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open P4AOriginalAnchorDecay20261024zSourceOnly
open P2OriginalThirdSecondDecay

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)
abbrev qPoint := P2OrdinaryIntegerGuard.rationalPoint

/-- The original coefficient rejection tests, before residual/tail dispatch. -/
def CoefficientsOK : Candidate → Prop
  | .base => ¬(0:ℤ)>256 ∧ ¬(0:ℤ)>256
  | .tent s .rise => literalTentX s≤2 ∧ literalTentY s≤2
  | .tent s .fall => -96*literalTentX s≤64 ∧ -96*literalTentY s≤64

instance (p : Candidate) : Decidable (CoefficientsOK p) := by
  cases p with
  | base => unfold CoefficientsOK; infer_instance
  | tent s k => cases k <;> unfold CoefficientsOK <;> infer_instance

/-- Literal candidates already have the right coefficient guards; no new
plane or post-selection replacement is introduced by this fact. -/
theorem coefficients_ok (p : Candidate) : CoefficientsOK p := by
  cases p with
  | base => exact ordinary_B_literal_coefficient_guards
  | tent s k => exact literal_coefficient_guards32 s k

def Residual (hi : Fin 3 → ℤ) : Candidate → Prop
  | .base => 0<153*D₀-256*hi 0-256*hi 1
  | .tent s k => sourceResidual32 s k hi

instance (hi : Fin 3 → ℤ) (p : Candidate) : Decidable (Residual hi p) := by
  cases p with
  | base => unfold Residual; infer_instance
  | tent s k => cases k <;> unfold Residual sourceResidual32 <;> infer_instance

/-- Only a common view of EXISTING tail operands, all on the same reader.
No interval, query, expectation or rounding operation is reimplemented. -/
structure MeanData where
  low : ℚ
  high : ℚ
  weight : IV
  fl : ℤ
  fh : ℤ
  out : ℤ

def meanData (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) : Candidate → MeanData :=
  let a := qPoint lo
  let b := qPoint hi
  fun p => match p with
  | .base =>
      { low := bLowQ b, high := bHighQ a,
        weight := rawWeight a b
          (originalLn32 (realBox b 0/realBox a 0))
          (originalLn32 (realBox b 1/realBox a 1)),
        fl := bStoredFl table b, fh := bStoredFh table a, out := bStoredOut table a b }
  | .tent s k =>
      let low := literalTentEndpoint s k hi D₀
      let high := literalTentEndpoint s k lo D₀
      { low := low, high := high,
        weight := ordinaryTentWeight s k (realBox a) (realBox b) low high,
        fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ),
        fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ),
        out := tentEarlyOut table (realBox a) (realBox b) }

theorem meanData_out (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (p : Candidate) :
    (meanData table lo hi p).out=candidateEarlyHigh table (qPoint lo) (qPoint hi) p := by
  cases p <;> rfl

theorem meanData_chord (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (p : Candidate) :
    meanHigh (meanData table lo hi p).weight.lo (meanData table lo hi p).weight.hi
      (meanData table lo hi p).fl (meanData table lo hi p).fh (meanData table lo hi p).out=
      candidateChordHigh table lo hi (qPoint lo) (qPoint hi) p := by
  cases p <;> rfl

/-- The selected candidate is checked ONCE, before the unchanged tail.
No other candidate is tried after rejection. Equality and both endpoints in
originalMeanUpperTail are retained even on inputs outside this theorem's scope. -/
def meanOption (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (p : Candidate) : Option ℤ :=
  if CoefficientsOK p ∧ Residual hi p then
    let d := meanData table lo hi p
    originalMeanUpperTail d.low d.high d.weight.lo d.weight.hi d.fl d.fh d.out
  else none

/-- Exact rejection characterization, reusing the existing tail's None rule. -/
theorem meanOption_none_iff (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (p : Candidate) :
    meanOption table lo hi p=none ↔
      ¬(CoefficientsOK p ∧ Residual hi p) ∨
        ((meanData table lo hi p).low<2 ∧ 2<(meanData table lo hi p).high) := by
  by_cases hp : CoefficientsOK p ∧ Residual hi p
  · simp only [meanOption,if_pos hp,originalMeanUpperTail_none_iff,hp,
      not_true_eq_false,false_or]
  · simp only [meanOption,if_neg hp,hp,not_false_eq_true,true_or]

/-- Original strict OLD span follows from the selected branch and residual,
including B. It rules out the equal branch only on checked positive cells. -/
theorem selected_meanData_span (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (p : Candidate) (hg : P2OrdinaryIntegerGuard.check lo hi=true)
    (hs : P2HistoricalThirdSelector.select lo hi=some p) (hr : Residual hi p) :
    (meanData table lo hi p).low<(meanData table lo hi p).high := by
  have g := P2OrdinaryIntegerGuard.checked_grid hg
  cases p with
  | base =>
      have hspan := below_mu_B_old_span (realBox (qPoint lo)) (realBox (qPoint hi))
        g.positive g.width g.xy g.mu
      have hspanQ : (bLowQ (qPoint hi):ℝ)<(bHighQ (qPoint lo):ℝ) := by
        simpa only [cast_bLowQ,cast_bHighQ] using hspan
      change bLowQ (qPoint hi)<bHighQ (qPoint lo)
      exact_mod_cast hspanQ
  | tent s k =>
      have ht := P2HistoricalThirdSelector.selected_tent_tests lo hi s k hs
      have hb := ht.1
      have hroot := ht.2
      dsimp [branchTest,deltaNumerator,rawSum] at hb
      dsimp [rootTest,rawSum] at hroot
      have hres := hr
      dsimp only [Residual,sourceResidual32] at hres
      have hguard := original_selected_tent_guard_bridge s k lo hi D₀ T₀
        (realBox (qPoint lo)) (realBox (qPoint hi)) rfl rfl
        (realBox_grid_binding lo (qPoint lo) g.lower)
        (realBox_grid_binding hi (qPoint hi) g.upper) hb hroot hres
      have hspan := literal_tent_endpoint_span s k lo hi D₀
        (realBox (qPoint lo)) (realBox (qPoint hi)) rfl
        (realBox_grid_binding lo (qPoint lo) g.lower)
        (realBox_grid_binding hi (qPoint hi) g.upper) g.positive g.width hguard.2.2
      change literalTentEndpoint s k hi D₀<literalTentEndpoint s k lo D₀
      exact_mod_cast hspan

theorem early_integral_upper (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (p : Candidate) (hg : P2OrdinaryIntegerGuard.check lo hi=true)
    (hh : (meanData table lo hi p).high≤2) :
    (∫ t in P2OrdinaryIntegerGuard.leaf lo hi,compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (candidateEarlyHigh table (qPoint lo) (qPoint hi) p)) := by
  have g := P2OrdinaryIntegerGuard.checked_grid hg
  cases p with
  | base =>
      exact ordinary_B_high_le_two_integer_upper table lo hi (qPoint lo) (qPoint hi)
        g.lower g.upper g.positive g.width g.cut g.xy g.yz g.mu g.full hh
  | tent s k =>
      exact (ordinary_tent_high_le_two_integer_upper table s k lo hi D₀
        (realBox (qPoint lo)) (realBox (qPoint hi)) rfl
        (realBox_grid_binding lo (qPoint lo) g.lower)
        (realBox_grid_binding hi (qPoint hi) g.upper)
        g.positive g.width g.cut g.xy g.yz g.mu g.full g.ratio g.logPositive hh).2

/-- Every returned mean has an actual integral supplier, not just arithmetic
nonnegativity. high=2 is early; low=2 and high>2 is chord; crossing is None. -/
theorem meanOption_some_integral_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (p : Candidate) (j : ℤ)
    (hg : P2OrdinaryIntegerGuard.check lo hi=true)
    (hs : P2HistoricalThirdSelector.select lo hi=some p)
    (hm : meanOption table lo hi p=some j) :
    (∫ t in P2OrdinaryIntegerGuard.leaf lo hi,compactKernel t)≤
      value (charge (candidateMassHi lo hi p) j) := by
  by_cases hp : CoefficientsOK p ∧ Residual hi p
  · have ht : originalMeanUpperTail (meanData table lo hi p).low
        (meanData table lo hi p).high (meanData table lo hi p).weight.lo
        (meanData table lo hi p).weight.hi (meanData table lo hi p).fl
        (meanData table lo hi p).fh (meanData table lo hi p).out=some j := by
      simpa only [meanOption,if_pos hp] using hm
    have hspan := selected_meanData_span table lo hi p hg hs hp.2
    rcases ordinary_old_span_dispatch_exhaustive _ _ hspan with hh | hc | ⟨hl,hstrict⟩
    · have he := high_le_two_returns_out (meanData table lo hi p).low
        (meanData table lo hi p).high (meanData table lo hi p).weight.lo
        (meanData table lo hi p).weight.hi (meanData table lo hi p).fl
        (meanData table lo hi p).fh (meanData table lo hi p).out hh
      have hj : j=candidateEarlyHigh table (qPoint lo) (qPoint hi) p :=
        (Option.some.inj (ht.symm.trans he)).trans (meanData_out table lo hi p)
      rw [hj]
      exact early_integral_upper table lo hi p hg hh
    · exact (crossing_no_charge _ _ _ _ _ _ _ j hc ht).elim
    · have he := strict_chord_tail (meanData table lo hi p).low
        (meanData table lo hi p).high (meanData table lo hi p).weight.lo
        (meanData table lo hi p).weight.hi (meanData table lo hi p).fl
        (meanData table lo hi p).fh (meanData table lo hi p).out hl hstrict
      have hj : j=candidateChordHigh table lo hi (qPoint lo) (qPoint hi) p :=
        (Option.some.inj (ht.symm.trans he)).trans (meanData_chord table lo hi p)
      have hu : P2HistoricalThirdSelector.ChordUsable hi p := by
        cases p with
        | base => exact hl
        | tent s k => exact ⟨hp.2,hl⟩
      have hch := P2HistoricalThirdSelector.selected_chord_integral_upper
        table lo hi p hg hs hu
      have hch' :
          (∫ t in P2OrdinaryIntegerGuard.leaf lo hi,compactKernel t)≤
          value (charge (candidateMassHi lo hi p)
            (candidateChordHigh table lo hi (qPoint lo) (qPoint hi) p)) := by
        cases p <;> exact hch
      rw [hj]
      exact hch'
  · simp only [meanOption,if_neg hp,reduceCtorEq] at hm

/-- All four fallback candidates are retained when the optional mean is
rejected. A successful early/chord mean enters before the SAME final mass UP. -/
def cellUpper (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (p : Candidate) : ℤ :=
  charge (candidateMassHi lo hi p)
    (applyOptionalMean (sourceFallbackHigh table (literalDecay table) lo hi)
      (meanOption table lo hi p))

theorem selected_cell_integral_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (p : Candidate)
    (hg : P2OrdinaryIntegerGuard.check lo hi=true)
    (hs : P2HistoricalThirdSelector.select lo hi=some p) :
    (∫ t in P2OrdinaryIntegerGuard.leaf lo hi,compactKernel t)≤
      value (cellUpper table lo hi p) := by
  have hf := P2OrdinaryIntegerGuard.check_integral_upper table lo hi p hg
  have g := P2OrdinaryIntegerGuard.checked_grid hg
  cases hm : meanOption table lo hi p with
  | none => simpa only [cellUpper,hm,applyOptionalMean] using hf
  | some j =>
      have hj := meanOption_some_integral_upper table lo hi p j hg hs hm
      rw [cellUpper,hm,applyOptionalMean,
        charge_min _ _ _ (candidate_mass_nonneg lo hi _ _ g p),value_min]
      exact le_min hf hj

/-- The historically selected ordinary estimator. The None selector case is
totalized by the base fallback; checked positive geometry proves it unreachable. -/
def ordinaryUpper (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) : ℤ :=
  match P2HistoricalThirdSelector.select lo hi with
  | none => P2OrdinaryIntegerGuard.integerUpper table lo hi .base
  | some p => cellUpper table lo hi p

/-- Complete ordinary optional-mean assembly, with no selected candidate,
residual success, mean success, real geometry or target bound premise. -/
theorem checked_ordinary_integral_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (hg : P2OrdinaryIntegerGuard.check lo hi=true) :
    (∫ t in P2OrdinaryIntegerGuard.leaf lo hi,compactKernel t)≤
      value (ordinaryUpper table lo hi) := by
  cases hs : P2HistoricalThirdSelector.select lo hi with
  | none =>
      exact (P2HistoricalThirdSelector.checked_select_ne_none hg hs).elim
  | some p =>
      simpa only [ordinaryUpper,hs] using
        selected_cell_integral_upper table lo hi p hg hs

end
end ImbalancedChen.Certificates.P2HistoricalThirdMeanDispatch
