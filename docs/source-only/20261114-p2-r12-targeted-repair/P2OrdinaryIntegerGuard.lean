import ImbalancedChen.Certificates.P2OriginalThirdSecondDecay
import ImbalancedChen.P4AOrdinarySixTentRange32Leaf
import ImbalancedChen.P4AOriginalSeedRange32Invariant

/-!
P2 SOURCE ONLY / UNCOMPILED.
Finite integer geometry checks supply the actual OrdinaryGrid, including
the original raw unit-log positivity, for the complete existing P160 fallback.
The existing geometry, log-positive and range-to-unit suppliers are reused.
No historical tree, guard acceptance, Q80 ABI or saved total is asserted.
-/
namespace ImbalancedChen.Certificates.P2OrdinaryIntegerGuard

open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
open OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdRoundedNewSourceOnly OriginalThirdClippedChordSourceOnly
open OriginalThirdPositiveLogSourceOnly
open OriginalThirdP4ASixTentRange32Moments
open OriginalThirdP4AOrdinarySixTentRange32Leaf
open P4AOriginalSeedRange32InvariantSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open P4AOriginalAnchorDecay20261024zSourceOnly
open P2OriginalThirdSecondDecay

/-- Coordinate dictionary at the unchanged original integer denominator. -/
abbrev rationalPoint (v : Fin 3 → ℤ) (i : Fin 3) : ℚ :=
  (v i:ℚ)/(sourceD:ℚ)

/-- Only integer geometry, ratio and source-assertion tests. In particular no
logarithm, analytic inequality, real integral or stored charge is a clause. -/
def Valid (lo hi : Fin 3 → ℤ) : Prop :=
  (∀ i,sourceH≤lo i) ∧
  (∀ i,lo i<hi i) ∧
  hi 1≤lo 0 ∧
  hi 2≤lo 1 ∧
  128*hi 0≤25*sourceD ∧
  hi 0+hi 1+3*hi 2≤(481573208064:ℤ) ∧
  (∀ i : Fin 2,hi i.castSucc≤2*lo i.castSucc) ∧
  hi 0+hi 1<sourceCapLower lo hi

instance (lo hi : Fin 3 → ℤ) : Decidable (Valid lo hi) := by
  unfold Valid
  infer_instance

/-- Constructive finite decision on all three coordinates, both ratios and
the original ca>x1+y1 assertion. No classical real predicate is decided. -/
def check (lo hi : Fin 3 → ℤ) : Bool := decide (Valid lo hi)

theorem check_sound {lo hi : Fin 3 → ℤ} (h : check lo hi=true) : Valid lo hi :=
  of_decide_eq_true h

theorem check_iff {lo hi : Fin 3 → ℤ} : check lo hi=true ↔ Valid lo hi := by
  simp only [check,decide_eq_true_eq]

/-- All real geometry and BOTH raw log-positive obligations follow from the
integer checker. No caller-supplied log bound or real coordinate premise. -/
theorem checked_grid {lo hi : Fin 3 → ℤ} (h : check lo hi=true) :
    OrdinaryGrid lo hi (rationalPoint lo) (rationalPoint hi) := by
  obtain ⟨hH,hwidth,hxy,hzy,hmu,hfull,hratioInt,_hassert⟩ := check_sound h
  obtain ⟨hpos,hwidthR,hcut,hxyR,hzyR,hmuR,hfullR⟩ :=
    ordinary_grid_geometry32 lo hi (rationalPoint lo) (rationalPoint hi)
      (fun _ => rfl) (fun _ => rfl) hH hwidth hxy hzy hmu hfull
  have hratio (i : Fin 2) :
      realBox (rationalPoint hi) i.castSucc/
        realBox (rationalPoint lo) i.castSucc≤2 := by
    have hlo : 0<lo i.castSucc :=
      lt_of_lt_of_le (by norm_num [sourceH]) (hH i.castSucc)
    have hloR : (0:ℝ)<(lo i.castSucc:ℝ) := by exact_mod_cast hlo
    change (rationalPoint hi i.castSucc:ℝ)/(rationalPoint lo i.castSucc:ℝ)≤2
    rw [grid_ratio_eq (lo i.castSucc) (hi i.castSucc)
      (rationalPoint lo i.castSucc) (rationalPoint hi i.castSucc) rfl rfl hlo.ne']
    exact (div_le_iff₀ hloR).2 (by exact_mod_cast hratioInt i)
  have hratioCast (i : Fin 2) :
      (rationalPoint hi i.castSucc:ℝ)/(rationalPoint lo i.castSucc:ℝ)≤2 := by
    simpa only [OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly.realBox,
      OriginalThirdBelowMuBRoundedSourceOnly.realBox] using hratio i
  have hlogs := original_stored_ordinary_log32_guards lo hi
    (rationalPoint lo) (rationalPoint hi) (fun _ => rfl) (fun _ => rfl)
    hpos hwidthR hxyR
    (by simpa only [OriginalThirdBelowMuBRoundedSourceOnly.realBox,
      VariableEnvelope.mu] using hmuR)
    (by linarith only [hratioCast 0]) (by linarith only [hratioCast 1])
  rw [originalLn32_eq_originalLnUnit_of_le_two (hratioCast 0),
    originalLn32_eq_originalLnUnit_of_le_two (hratioCast 1)] at hlogs
  refine ⟨(fun _ => rfl),(fun _ => rfl),hpos,hwidthR,hcut,hxyR,hzyR,hmuR,
    hfullR,hratio,?_⟩
  intro i
  fin_cases i
  · exact hlogs.1
  · exact hlogs.2

def leaf (lo hi : Fin 3 → ℤ) : Set BoxPoint :=
  compactRegion ∩ Icc (realBox (rationalPoint lo)) (realBox (rationalPoint hi))

theorem leaf_measurable (lo hi : Fin 3 → ℤ) : MeasurableSet (leaf lo hi) :=
  measurableSet_compactRegion.inter measurableSet_Icc

/-- Integrability is inherited from the genuine compact kernel, rather than
stored as a certificate premise. This also holds for a rejected/empty box. -/
theorem leaf_integrable (lo hi : Fin 3 → ℤ) :
    IntegrableOn compactKernel (leaf lo hi) :=
  integrableOn_compactKernel.mono_set inter_subset_left

noncomputable section

/-- Existing P160 pre-mean fallback charge, with all gate cases,
a candidate's full mass and final UP. No optional Jensen mean is used.
The geometry checker above does
not evaluate this cost, the reader table, or historical Q80 charges. -/
def integerUpper (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (p : Candidate) : ℤ :=
  charge (candidateMassHi lo hi p) (sourceFallbackHigh table (literalDecay table) lo hi)

/-- Finite integer acceptance to the actual leaf integral. Complete fallback
includes raw, clipped and both decay gates; the reader remains the same. -/
theorem check_integral_upper (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (p : Candidate) (h : check lo hi=true) :
    (∫ t in leaf lo hi,compactKernel t)≤value (integerUpper table lo hi p) := by
  have g := checked_grid h
  obtain ⟨_hH,_hwidth,_hxy,_hzy,_hmu,_hfull,_hratio,hassert⟩ := check_sound h
  exact original_source_fallback_integer_upper table lo hi
    (rationalPoint lo) (rationalPoint hi) g p hassert

/-- Rational enclosure at the EXISTING P160 scale. No historical Q80
rounding or equality of producer outputs is inferred from this dictionary. -/
theorem check_integral_upper_rational (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (p : Candidate) (h : check lo hi=true) :
    (∫ t in leaf lo hi,compactKernel t)≤
      (((integerUpper table lo hi p:ℤ):ℚ)/(2:ℚ)^160:ℝ) := by
  simpa only [value,P160,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,
    Rat.cast_ofNat,Int.cast_pow,Int.cast_ofNat] using check_integral_upper table lo hi p h

/-- The checked integer cell also supplies the real pointwise second-decay
bound whenever its unchanged original integer gate is active. -/
theorem check_second_decay_pointwise (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (h : check lo hi=true)
    (hgate : 4*hi 2≤oldLowerNumerator lo hi)
    {t : BoxPoint} (ht : t∈leaf lo hi) :
    0≤actualExtendedThirdLowerFactor
        (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) ∧
    actualExtendedThirdLowerFactor
        (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
      actualExtendedThirdLowerFactor (actualOldArgument t)≤
        value (secondDecayHigh table lo hi) :=
  second_decay_actual_pointwise table lo hi (rationalPoint lo) (rationalPoint hi)
    (checked_grid h) hgate ht.2

end
end ImbalancedChen.Certificates.P2OrdinaryIntegerGuard
