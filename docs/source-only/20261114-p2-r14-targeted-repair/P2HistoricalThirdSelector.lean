import ImbalancedChen.Certificates.P2OrdinaryIntegerGuard

/-!
P2 SOURCE ONLY / UNCOMPILED.
Minimal selector adaptation to certify_extended_prefix.py at manuscript
3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e: tent order x,y,xy,xyz,xz,yz,
B LAST, integer-floored midpoint score, and first winner on a tie.
The existing sourcePair, rootTest, rangeLow, firstMax and analytic suppliers
are reused. This fixes a selector mismatch, NOT the remaining Q80/P160 ABI.
Only the selected strict-chord branch is consumed here; early/crossing and
complete historical charges/tree acceptance are not silently supplied.
-/
namespace ImbalancedChen.Certificates.P2HistoricalThirdSelector
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
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
open OriginalThirdP4ASixTentRange32Moments
open OriginalThirdP4AOrdinarySixTentRange32Leaf
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open P4AOriginalAnchorDecay20261024zSourceOnly
open P2OriginalThirdSecondDecay

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)

/-- Exact loop order of the historical prefix producer, before B is appended. -/
def historicalSums : List TentSum := [.x,.y,.xy,.xyz,.xz,.yz]

def rawCandidates (lo hi : Fin 3 → ℤ) : List Candidate :=
  historicalSums.flatMap (sourcePair lo hi D₀) ++ [.base]

/-- Finite integer decision; the root test itself is reused unchanged. -/
instance (lo hi : Fin 3 → ℤ) (p : Candidate) :
    Decidable (rootTest lo hi D₀ T₀ p) := by
  cases p with
  | base => unfold rootTest; infer_instance
  | tent s k => cases k <;> unfold rootTest <;> infer_instance

def candidates (lo hi : Fin 3 → ℤ) : List Candidate :=
  (rawCandidates lo hi).filter (fun p => decide (rootTest lo hi D₀ T₀ p))

/-- Python //2, including odd sums. No real midpoint replaces this integer. -/
def midpoint (lo hi : Fin 3 → ℤ) (i : Fin 3) : ℤ := (lo i+hi i)/2

/-- rangeLow at identical corners is the exact affine plane value, in
integer coordinate units. Its positive literal denominator is retained. -/
def midpointScore (lo hi : Fin 3 → ℤ) (p : Candidate) : ℚ :=
  rangeLow (midpoint lo hi) (midpoint lo hi) D₀ p

def select (lo hi : Fin 3 → ℤ) : Option Candidate :=
  firstMax (midpointScore lo hi) (candidates lo hi)

/-- The two raw lists have identical membership, with different order.
This adapter reuses the existing branch proof for the historical list. -/
theorem raw_mem_iff (lo hi : Fin 3 → ℤ) (p : Candidate) :
    p∈rawCandidates lo hi ↔ p∈sourceRaw lo hi D₀ := by
  simp only [rawCandidates,historicalSums,sourceRaw,sourceSums,
    List.flatMap_cons,List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil]
  tauto

theorem selected_tent_tests (lo hi : Fin 3 → ℤ) (s : TentSum) (k : TentSide)
    (h : select lo hi=some (.tent s k)) :
    branchTest lo hi D₀ s k ∧ rootTest lo hi D₀ T₀ (.tent s k) := by
  have hm := (firstMax_mem_max (midpointScore lo hi) (candidates lo hi) (.tent s k) h).1
  have hf := List.mem_filter.mp hm
  exact ⟨(tent_mem_sourceRaw_iff lo hi D₀ s k).mp
    ((raw_mem_iff lo hi (.tent s k)).mp hf.1),of_decide_eq_true hf.2⟩

/-- The producer changes the winner only at a STRICT improvement.
The existing generic firstMax proof supplies exact first-tie priority. -/
theorem selected_first_priority (lo hi : Fin 3 → ℤ) (p : Candidate)
    (h : select lo hi=some p) :
    ∃ before after,candidates lo hi=before++p::after ∧
      (∀ q∈before,midpointScore lo hi q<midpointScore lo hi p) ∧
      (∀ q∈after,midpointScore lo hi q≤midpointScore lo hi p) :=
  firstMax_priority (midpointScore lo hi) (candidates lo hi) p h

/-- Accepted ordinary geometry is strictly BELOW the producer's mu branch
switch, even though its upper x corner may equal mu. -/
theorem checked_below_mu {lo hi : Fin 3 → ℤ}
    (h : P2OrdinaryIntegerGuard.check lo hi=true) :
    128*lo 0<25*D₀ := by
  obtain ⟨_hH,hw,_hxy,_hzy,hm,_hfull,_hratio,_hassert⟩ :=
    P2OrdinaryIntegerGuard.check_sound h
  have hx := hw 0
  change 128*hi 0≤25*D₀ at hm
  omega

/-- The actual positive ordinary cell always retains B through the root
filter. Absence is not introduced merely by changing score or list order. -/
theorem checked_select_ne_none {lo hi : Fin 3 → ℤ}
    (h : P2OrdinaryIntegerGuard.check lo hi=true) : select lo hi≠none := by
  have hH := (P2OrdinaryIntegerGuard.check_sound h).1 2
  have hz : 0≤lo 2 := (by norm_num [sourceH] : (0:ℤ)≤sourceH).trans hH
  have hbRoot : rootTest lo hi D₀ T₀ .base := ordinary_B_literal_root lo hz
  have hbRaw : Candidate.base∈rawCandidates lo hi := by
    exact List.mem_append_right _ (by simp)
  have hb : Candidate.base∈candidates lo hi := by
    exact List.mem_filter.mpr ⟨hbRaw,by simpa only [decide_eq_true_eq] using hbRoot⟩
  intro hn
  have he := (firstMax_none_iff (midpointScore lo hi) (candidates lo hi)).mp hn
  rw [he] at hb
  exact List.not_mem_nil hb

/-- Original POST-selection strict-chord guards in rational/integer form.
A failed selected guard does not cause selection of a different plane. -/
def ChordUsable (hi : Fin 3 → ℤ) : Candidate → Prop
  | .base => (2:ℚ)≤OriginalThirdBelowMuBRoundedSourceOnly.bLowQ
      (P2OrdinaryIntegerGuard.rationalPoint hi)
  | .tent s k => sourceResidual32 s k hi ∧
      (2:ℚ)≤literalTentEndpoint s k hi D₀

instance (hi : Fin 3 → ℤ) (p : Candidate) : Decidable (ChordUsable hi p) := by
  cases p with
  | base => unfold ChordUsable; infer_instance
  | tent s k => cases k <;> unfold ChordUsable sourceResidual32 <;> infer_instance

/-- Selection, guards and checked integer geometry now supply the genuine
selected chord integral. No old range-sum selector identity is assumed. -/
theorem selected_chord_integral_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (p : Candidate)
    (hg : P2OrdinaryIntegerGuard.check lo hi=true)
    (hs : select lo hi=some p) (hu : ChordUsable hi p) :
    (∫ t in P2OrdinaryIntegerGuard.leaf lo hi,compactKernel t)≤
      value (candidateIntegerUpper table lo hi
        (P2OrdinaryIntegerGuard.rationalPoint lo)
        (P2OrdinaryIntegerGuard.rationalPoint hi) p) := by
  let a := P2OrdinaryIntegerGuard.rationalPoint lo
  let b := P2OrdinaryIntegerGuard.rationalPoint hi
  have g : OrdinaryGrid lo hi a b := P2OrdinaryIntegerGuard.checked_grid hg
  cases p with
  | base =>
      have huR : (2:ℝ)≤
          (OriginalThirdBelowMuBRoundedSourceOnly.bLowQ b:ℝ) := by exact_mod_cast hu
      have hlo : (2:ℝ)≤OriginalThirdBelowMuBCandidateSourceOnly.bOldLow (realBox b) := by
        simpa only [OriginalThirdBelowMuBRoundedSourceOnly.cast_bLowQ] using huR
      exact ordinary_B_stored_integer_upper_of_grid table lo hi a b
        g.lower g.upper g.positive g.width g.cut g.xy g.yz g.mu g.full hlo
  | tent s k =>
      have ht := selected_tent_tests lo hi s k hs
      have hbranch := ht.1
      have hroot := ht.2
      dsimp [branchTest,deltaNumerator,rawSum] at hbranch
      dsimp [rootTest,rawSum] at hroot
      have hres := hu.1
      dsimp only [sourceResidual32] at hres
      have hlo : (2:ℝ)≤(literalTentEndpoint s k hi D₀:ℝ) := by exact_mod_cast hu.2
      exact original_selected_tent_stored_integer_upper table s k lo hi D₀ T₀
        (realBox a) (realBox b) (literalTentEndpoint s k hi D₀)
        (literalTentEndpoint s k lo D₀) _ _ _ rfl rfl
        (realBox_grid_binding lo a g.lower) (realBox_grid_binding hi b g.upper)
        g.positive g.width g.cut g.xy g.yz g.mu g.full
        (by cases k <;> norm_num at hbranch ⊢ <;> exact hbranch)
        (by cases k <;> norm_num at hroot ⊢ <;> simpa only [add_assoc] using hroot)
        (by cases k <;> norm_num at hres ⊢ <;> exact hres)
        rfl rfl hlo g.ratio g.logPositive rfl rfl rfl

/-- Same historical-selected candidate, complete existing P160 fallback,
chord minimum BEFORE multiplication, and the original final mass UP. -/
def combinedUpper (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (p : Candidate) : ℤ :=
  charge (candidateMassHi lo hi p)
    (min (sourceFallbackHigh table (literalDecay table) lo hi)
      (candidateChordHigh table lo hi (P2OrdinaryIntegerGuard.rationalPoint lo)
        (P2OrdinaryIntegerGuard.rationalPoint hi) p))

theorem selected_combined_integral_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (p : Candidate)
    (hg : P2OrdinaryIntegerGuard.check lo hi=true)
    (hs : select lo hi=some p) (hu : ChordUsable hi p) :
    (∫ t in P2OrdinaryIntegerGuard.leaf lo hi,compactKernel t)≤
      value (combinedUpper table lo hi p) := by
  have g := P2OrdinaryIntegerGuard.checked_grid hg
  have hf := P2OrdinaryIntegerGuard.check_integral_upper table lo hi p hg
  have hj := selected_chord_integral_upper table lo hi p hg hs hu
  have hj' :
      (∫ t in P2OrdinaryIntegerGuard.leaf lo hi,compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (candidateChordHigh table lo hi (P2OrdinaryIntegerGuard.rationalPoint lo)
          (P2OrdinaryIntegerGuard.rationalPoint hi) p)) := by
    cases p <;> exact hj
  unfold combinedUpper
  rw [charge_min _ _ _ (candidate_mass_nonneg lo hi _ _ g p),value_min]
  exact le_min hf hj'

/-- A strict-chord consumer, not a replacement for the full producer.
Early/crossing/residual-failure cells remain explicit None for this API. -/
def checkedChordUpper (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) : Option ℤ :=
  if P2OrdinaryIntegerGuard.check lo hi=true then
    match select lo hi with
    | none => none
    | some p => if ChordUsable hi p then some (combinedUpper table lo hi p) else none
  else none

theorem checkedChordUpper_sound (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (n : ℤ) (h : checkedChordUpper table lo hi=some n) :
    (∫ t in P2OrdinaryIntegerGuard.leaf lo hi,compactKernel t)≤value n := by
  by_cases hg : P2OrdinaryIntegerGuard.check lo hi=true
  · simp only [checkedChordUpper,if_pos hg] at h
    cases hs : select lo hi with
    | none => simp only [hs,reduceCtorEq] at h
    | some p =>
        by_cases hu : ChordUsable hi p
        · have he : combinedUpper table lo hi p=n := by
            simpa only [hs,if_pos hu,Option.some.injEq] using h
          rw [← he]
          exact selected_combined_integral_upper table lo hi p hg hs hu
        · simp only [hs,if_neg hu,reduceCtorEq] at h
  · simp only [checkedChordUpper,if_neg hg,reduceCtorEq] at h

end
end ImbalancedChen.Certificates.P2HistoricalThirdSelector
