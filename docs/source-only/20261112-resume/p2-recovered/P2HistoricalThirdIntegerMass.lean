import ImbalancedChen.Certificates.P2HistoricalThirdMeanDispatch
import ImbalancedChen.P4ARange32ExecutableReaderABI

/-!
P2 SOURCE ONLY / UNCOMPILED.
Minimal mass ABI for the historically ordered ordinary estimator. Reuse the
existing integer positive256 log and full mass tree; only connect its output
to BOTH existing candidateMassHi branches and the actual integral consumer.
The mass program below contains no real logarithm or real floor. Its compilation
and execution are unverified. The full mean/fallback/reader cost remains
noncomputable; neither Q80 equality nor any concrete comparison is asserted.
-/
namespace ImbalancedChen.Certificates.P2HistoricalThirdIntegerMass

open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
open OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdP4ASixTentRange32Moments
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open P4AOriginalAnchorDecay20261024zSourceOnly
open P4ARange32ExecutableReaderABI

/-- Existing integer log, then (lx*ly)*V(4D dz/(z0*z1)); no new arithmetic. -/
def fullMass (lo hi : Fin 3 → ℤ) : IV :=
  P4ARange32IntegerOuterABI.mass integerLog32 lo hi

def massHi (lo hi : Fin 3 → ℤ) : ℤ := (fullMass lo hi).hi

/-- The existing one final UP, after multiplying by the complete mass.hi. -/
def massCharge (lo hi : Fin 3 → ℤ) (high : ℤ) : ℤ :=
  charge (massHi lo hi) high

/-- B uses the same full range-reduced log tree. Positivity pays only the
existing Real-rational to integer V dictionary for the z denominator. -/
theorem fullMass_eq_base (lo hi : Fin 3 → ℤ) (hl : 0<lo 2) (hu : 0<hi 2) :
    fullMass lo hi=
      OriginalThirdBelowMuBMassCeilSourceOnly.literalOrdinaryMass lo hi := by
  exact P4ARange32IntegerOuterABI.mass_eq_original integerLog32 lo hi
    (fun i => integerLog32_eq_original (lo i) (hi i)) hl hu

/-- The six tents use unit logs. On their existing two <=2 branches these
are EXACTLY the range32 outputs, including equality at 2. No approximation
or interval reassociation is used; the z-factor record is definitionally equal. -/
theorem fullMass_eq_tent (lo hi : Fin 3 → ℤ)
    (hx : (hi 0:ℝ)/(lo 0:ℝ)≤2) (hy : (hi 1:ℝ)/(lo 1:ℝ)≤2) :
    fullMass lo hi=
      OriginalThirdSixTentOrdinaryMassCeilSourceOnly.literalOrdinaryMass lo hi := by
  unfold fullMass P4ARange32IntegerOuterABI.mass
  rw [integerLog32_eq_original,integerLog32_eq_original,
    P4AOriginalSeedRange32InvariantSourceOnly.originalLn32_eq_originalLnUnit_of_le_two hx,
    P4AOriginalSeedRange32InvariantSourceOnly.originalLn32_eq_originalLnUnit_of_le_two hy]
  rfl

/-- Raw integer ratio checks and lower cutoffs supply both unit-log branches.
No real ratio, log positivity or sourceR premise is added to the checker. -/
theorem checked_raw_ratios {lo hi : Fin 3 → ℤ}
    (hg : P2OrdinaryIntegerGuard.check lo hi=true) :
    ∀ i : Fin 2,(hi i.castSucc:ℝ)/(lo i.castSucc:ℝ)≤2 := by
  obtain ⟨hH,_hw,_hxy,_hzy,_hm,_hf,hr,_ha⟩ :=
    P2OrdinaryIntegerGuard.check_sound hg
  intro i
  have hl : 0<lo i.castSucc :=
    lt_of_lt_of_le (by norm_num [sourceH]) (hH i.castSucc)
  have hlR : (0:ℝ)<(lo i.castSucc:ℝ) := by exact_mod_cast hl
  exact (div_le_iff₀ hlR).2 (by exact_mod_cast hr i)

/-- Every B/tent candidate now has one identical integer mass endpoint.
This does not assert identical Q80 historical costs or executable readers. -/
theorem massHi_eq_candidate {lo hi : Fin 3 → ℤ}
    (hg : P2OrdinaryIntegerGuard.check lo hi=true) (p : Candidate) :
    massHi lo hi=candidateMassHi lo hi p := by
  obtain ⟨hH,hw,_hxy,_hzy,_hm,_hf,_hr,_ha⟩ :=
    P2OrdinaryIntegerGuard.check_sound hg
  have hl : 0<lo 2 := lt_of_lt_of_le (by norm_num [sourceH]) (hH 2)
  have hu : 0<hi 2 := hl.trans (hw 2)
  cases p with
  | base =>
      exact congrArg IV.hi (fullMass_eq_base lo hi hl hu)
  | tent s k =>
      exact congrArg IV.hi (fullMass_eq_tent lo hi
        (checked_raw_ratios hg 0) (checked_raw_ratios hg 1))

theorem massCharge_eq_candidate {lo hi : Fin 3 → ℤ}
    (hg : P2OrdinaryIntegerGuard.check lo hi=true) (p : Candidate) (high : ℤ) :
    massCharge lo hi high=charge (candidateMassHi lo hi p) high := by
  unfold massCharge
  rw [massHi_eq_candidate hg p]

/-- Actual reciprocal-box mass enclosure is inherited from the existing B
supplier, with its normalization and factor4 unchanged. -/
theorem checked_mass_encloses {lo hi : Fin 3 → ℤ}
    (hg : P2OrdinaryIntegerGuard.check lo hi=true) :
    Encloses (fullMass lo hi)
      (4*boxMass (realBox (P2OrdinaryIntegerGuard.rationalPoint lo))
        (realBox (P2OrdinaryIntegerGuard.rationalPoint hi))) := by
  have g := P2OrdinaryIntegerGuard.checked_grid hg
  obtain ⟨hH,hw,_hxy,_hzy,_hm,_hf,_hr,_ha⟩ :=
    P2OrdinaryIntegerGuard.check_sound hg
  have hl : 0<lo 2 := lt_of_lt_of_le (by norm_num [sourceH]) (hH 2)
  rw [fullMass_eq_base lo hi hl (hl.trans (hw 2))]
  exact OriginalThirdBelowMuBMassCeilSourceOnly.literal_ordinary_mass_encloses
    lo hi _ _ (realBox_grid_binding lo _ g.lower)
    (realBox_grid_binding hi _ g.upper) g.positive g.width g.cut g.xy g.yz g.mu

theorem checked_massHi_nonneg {lo hi : Fin 3 → ℤ}
    (hg : P2OrdinaryIntegerGuard.check lo hi=true) : 0≤massHi lo hi := by
  rw [massHi_eq_candidate hg .base]
  exact candidate_mass_nonneg lo hi _ _ (P2OrdinaryIntegerGuard.checked_grid hg) .base

noncomputable section

/-- Only the mass program is replaced. Mean/fallback expressions, same-reader
queries, optional rejection, and min-before-UP are reused unchanged. -/
def cellUpper (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (p : Candidate) : ℤ :=
  massCharge lo hi
    (applyOptionalMean (sourceFallbackHigh table (literalDecay table) lo hi)
      (P2HistoricalThirdMeanDispatch.meanOption table lo hi p))

def ordinaryUpper (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) : ℤ :=
  match P2HistoricalThirdSelector.select lo hi with
  | none => massCharge lo hi (sourceFallbackHigh table (literalDecay table) lo hi)
  | some p => cellUpper table lo hi p

theorem cellUpper_eq_original (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (p : Candidate) (hg : P2OrdinaryIntegerGuard.check lo hi=true) :
    cellUpper table lo hi p=P2HistoricalThirdMeanDispatch.cellUpper table lo hi p := by
  exact massCharge_eq_candidate hg p _

/-- Includes the totalized None selector case; no winner-success premise. -/
theorem ordinaryUpper_eq_original (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (hg : P2OrdinaryIntegerGuard.check lo hi=true) :
    ordinaryUpper table lo hi=P2HistoricalThirdMeanDispatch.ordinaryUpper table lo hi := by
  cases hs : P2HistoricalThirdSelector.select lo hi with
  | none =>
      simpa only [ordinaryUpper,P2HistoricalThirdMeanDispatch.ordinaryUpper,hs,
        P2OrdinaryIntegerGuard.integerUpper] using massCharge_eq_candidate hg .base
          (sourceFallbackHigh table (literalDecay table) lo hi)
  | some p =>
      simpa only [ordinaryUpper,P2HistoricalThirdMeanDispatch.ordinaryUpper,hs] using
        cellUpper_eq_original table lo hi p hg

/-- The integer-mass expression bounds the genuine integral. No actual
integral supplier or real mass/log enclosure is a caller premise. -/
theorem checked_ordinary_integral_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (hg : P2OrdinaryIntegerGuard.check lo hi=true) :
    (∫ t in P2OrdinaryIntegerGuard.leaf lo hi,compactKernel t)≤
      value (ordinaryUpper table lo hi) := by
  rw [ordinaryUpper_eq_original table lo hi hg]
  exact P2HistoricalThirdMeanDispatch.checked_ordinary_integral_upper table lo hi hg

end
end ImbalancedChen.Certificates.P2HistoricalThirdIntegerMass
