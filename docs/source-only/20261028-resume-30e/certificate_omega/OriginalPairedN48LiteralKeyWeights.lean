import ImbalancedChen.OriginalPairedN48CanonicalArrayProofProposals
import ImbalancedChen.OriginalPairedN48PreallocatedProducerIdentity
import ImbalancedChen.P2N48AllHighBandWeightedMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal directed weights(lo,hi,N) for original key (1,39,47,0,0).
The two untied blocks have m=1; the distinguished tied block has m=2,
r=0,s=1.  The original J(1), J(0), powers, moments, divisions and left
association are retained instead of replacing the token by a real formula.

The finite guard/floor terms below are UNEXECUTED proof proposals.  This
module consumes the independently frozen true-Z Fubini supplier to identify
its real expression with the same native parent's actual weighted integral.
-/

namespace ImbalancedChen.OriginalPairedN48LiteralKeyWeights

noncomputable section
open LiLiuPrereqBuchstab
open Certificates.P2DirectedLogRounding
open OriginalN48Q112LocalProduct
open OriginalPairedN48OmegaProducerAdapter
open OriginalPairedN48OmegaStepArithmetic
open OriginalPairedN48SmallLogSoundness
open OriginalPairedN48CanonicalArrays
open OriginalPairedN48DirectQuerySoundness
open OriginalPairedN48PreallocatedProducerIdentity
open OriginalPairedKeyUniformOmegaQuery
open OriginalPairedV2Q112ParentAttachment
open P2N48ActualSixteenCostRowAttachment
open P2N48MethodZeroQ112SwitchReduction

def keyXRatio : ℚ := 53280 / 52860
def keyURatio : ℚ := 36480 / 36137
def keyZRatio : ℚ := 20359 / 20016

/-- The logarithm range-reduction counter is zero for all three blocks. -/
theorem key_log_ratio_ranges :
    1 ≤ keyXRatio ∧ keyXRatio ≤ 2 ∧
      1 ≤ keyURatio ∧ keyURatio ≤ 2 ∧ 1 ≤ keyZRatio ∧ keyZRatio ≤ 2 := by
  norm_num [keyXRatio, keyURatio, keyZRatio]

theorem zero_log_correction_identity (L logTwo : Token) :
    sourceAdd L (sourceMul (rational 0) logTwo) = L := by
  cases L
  cases logTwo
  simp [sourceAdd, sourceMul, lowerProduct, upperProduct,
    rational, encode, Enclosure.point]

def positiveLogDivisor (q : ℚ) : Prop :=
  0 < (sourceSub (rational 1)
    (sourceMul (rational (logX q)) (rational (logX q)))).lo

instance (q : ℚ) : Decidable (positiveLogDivisor q) := by
  unfold positiveLogDivisor
  infer_instance

/-- Three fixed scalar arithmetic obligations, never executed here. -/
theorem key_log_divisors_proposal :
    positiveLogDivisor keyXRatio ∧ positiveLogDivisor keyURatio ∧
      positiveLogDivisor keyZRatio := by
  decide +kernel

def singletonBlock (q : ℚ) : Token :=
  sourceDiv (sourcePow (sourceSmallLog q) 1) (rational 1)

theorem singletonBlock_contains {q : ℚ} (hq : 1 ≤ q) (hd : positiveLogDivisor q) :
    (decode (singletonBlock q)).Contains (Real.log (q : ℝ)) := by
  have hL := sourceSmallLog_contains hq hd
  have h := sourceDiv_contains _ (rational 1)
    (rational_lower_pos (by norm_num : (1 : ℚ) ≤ 1))
    (sourcePow_contains (sourceSmallLog q) hL 1) (rational_contains 1)
  simpa only [singletonBlock, pow_one, Rat.cast_one, div_one] using h

def keyL : Token := sourceSmallLog keyZRatio
def keyEx : Token := rational (20016 / 20359)
def keyMom0 : Token := sourceSub (rational 1) keyEx
def keyMom1 : Token :=
  sourceSub (sourceMul (rational 1) keyMom0) (sourceMul keyEx (sourcePow keyL 1))

def keyMomentTerm : Token :=
  sourceMul (sourceMul (rational 1) (sourcePow keyL 0)) keyMom1

def keyMomentValue : Token := sourceAdd (rational 0) keyMomentTerm
def keyZPart : Token := sourceMul (rational (240000 / 20016)) keyMomentValue

def literalOriginalZToken : Token :=
  sourceMul
    (sourceMul (sourceMul (rational 1) (singletonBlock keyXRatio))
      (singletonBlock keyURatio)) keyZPart

def keyTrueMassExpression : ℝ :=
  Real.log (keyXRatio : ℝ) * Real.log (keyURatio : ℝ) * ((240000 : ℝ) / 20016) *
    (1 - (20016 : ℝ) / 20359 - ((20016 : ℝ) / 20359) * Real.log (keyZRatio : ℝ))

/-- Directed soundness of the ORIGINAL moment arithmetic.  The expression
still needs to be identified with the actual same-parent weighted integral. -/
theorem literalOriginalZToken_contains_expression :
    (decode literalOriginalZToken).Contains keyTrueMassExpression := by
  have hx := singletonBlock_contains key_log_ratio_ranges.1 key_log_divisors_proposal.1
  have hu := singletonBlock_contains key_log_ratio_ranges.2.2.1 key_log_divisors_proposal.2.1
  have hz := sourceSmallLog_contains key_log_ratio_ranges.2.2.2.2.1
    key_log_divisors_proposal.2.2
  have he := rational_contains (20016 / 20359)
  have hm0 := sourceSub_contains (rational 1) keyEx (rational_contains 1) he
  have hm1 := sourceSub_contains (sourceMul (rational 1) keyMom0)
    (sourceMul keyEx (sourcePow keyL 1))
    (sourceMul_contains _ _ (rational_contains 1) hm0)
    (sourceMul_contains _ _ he (sourcePow_contains keyL hz 1))
  have hterm := sourceMul_contains (sourceMul (rational 1) (sourcePow keyL 0)) keyMom1
    (sourceMul_contains _ _ (rational_contains 1) (sourcePow_contains keyL hz 0)) hm1
  have hval := sourceAdd_contains (rational 0) keyMomentTerm (rational_contains 0) hterm
  have hpart := sourceMul_contains (rational (240000 / 20016)) keyMomentValue
    (rational_contains (240000 / 20016)) hval
  have hprod := sourceMul_contains
    (sourceMul (sourceMul (rational 1) (singletonBlock keyXRatio)) (singletonBlock keyURatio))
    keyZPart
    (sourceMul_contains _ _ (sourceMul_contains _ _ (rational_contains 1) hx) hu) hpart
  convert hprod using 1
  <;> norm_num only [literalOriginalZToken, keyTrueMassExpression, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, pow_one, pow_zero,
    one_mul, zero_add]
  <;> ring

/-- The independent LOWER Fubini theorem supplies the integral identity;
it is not defined as the proposed token or assumed as a new hZ premise. -/
theorem same_parent_true_mass_expression : actualMass keySavedRow = keyTrueMassExpression := by
  have h := P2N48AllHighBandWeightedMass.original_keyRow_mass
    1014347 0 5945529223463611
  simpa only [actualMass, keySavedRow, P2N48OneActualTiedParentVolume.keyRow,
    keyTrueMassExpression, keyXRatio, keyURatio, keyZRatio,
    Rat.cast_div, Rat.cast_ofNat] using h

theorem literalOriginalZToken_contains_true_mass :
    (decode literalOriginalZToken).Contains (actualMass keySavedRow) := by
  rw [same_parent_true_mass_expression]
  exact literalOriginalZToken_contains_expression

def literalOriginalEndpoint : DirectedMethodZeroRow :=
  computedDirectedEndpoint (originalQueryToken canonicalSourceArrays) literalOriginalZToken

def originalFixedEndpoint : DirectedMethodZeroRow :=
  computedDirectedEndpoint ⟨originalFixedFields.queryMax, originalFixedFields.queryMax⟩
    literalOriginalZToken

/-- The endpoint's original producer field has been obtained by independent
preallocated/replacement control flow, then proved equal to the canonical
field.  This is an algorithm-field identity, not a recovered byte identity. -/
theorem original_fixed_endpoint_identity : originalFixedEndpoint = literalOriginalEndpoint := by
  unfold originalFixedEndpoint literalOriginalEndpoint originalQueryToken
  rw [original_fixed_query_numerator_identity]
  rfl

theorem original_preallocated_query_bound_proposal {v : Fin 4 → ℝ}
    (hv : v ∈ nativeBox keySavedRow) :
    buchstab (argument v) ≤ ((originalFixedFields.queryMax : ℤ) : ℝ) / (P : ℝ) := by
  rw [original_fixed_query_numerator_identity]
  exact OriginalPairedN48CanonicalArrayProofProposals.canonical_actual_query_proposal hv

/-- Both directed endpoints use the SAME true Z_B interval and the SAME
original query.  No separate coarse lower/upper mass proxies intervene. -/
theorem literal_original_same_parent_directions :
    ((literalOriginalEndpoint.switchBaselineLo : ℤ) : ℝ) / (replayP : ℝ) ≤
        P2N48SavedParentRowRecost.anchorK * P2N48SavedParentRowRecost.omegaCap *
          actualMass keySavedRow ∧
    P2N48SavedParentRowRecost.anchorK * uniformOmegaUpper (originalQueryToken canonicalSourceArrays) *
        actualMass keySavedRow ≤
      ((literalOriginalEndpoint.omegaCostHi : ℤ) : ℝ) / (replayP : ℝ) := by
  exact computed_endpoints_uniform_directions
    (originalQueryToken canonicalSourceArrays) literalOriginalZToken
    literalOriginalZToken_contains_true_mass le_rfl

/-- The original Python retains max(0,switch.l-cost.u), with P112 tokens. -/
def literalOriginalLower : ℤ :=
  max 0 (literalOriginalEndpoint.switchBaselineLo - literalOriginalEndpoint.omegaCostHi)

/-- This is the exact same-parent Q112/Q80 integer inequality at row1014347.
It has not been executed and no concrete numerator is asserted. -/
def literalOriginalFloorCheck : Bool :=
  decide ((keySavedRow.floorQ : ℤ) * replayP ≤ literalOriginalLower * replayQ)

/-- The stored row floor is strictly positive, so an accepted original
max-floor comparison supplies the existing unclamped endpoint receiver. -/
theorem literal_original_floor_check_sound
    (hcheck : literalOriginalFloorCheck = true) :
    finiteFloorCheck keySavedRow literalOriginalEndpoint = true := by
  have h := of_decide_eq_true
    (show decide ((keySavedRow.floorQ : ℤ) * replayP ≤ literalOriginalLower * replayQ) = true
      from hcheck)
  have hf : (0 : ℤ) < (keySavedRow.floorQ : ℤ) * replayP := by
    norm_num [keySavedRow, replayP]
  by_cases hd : 0 ≤ literalOriginalEndpoint.switchBaselineLo - literalOriginalEndpoint.omegaCostHi
  · rw [literalOriginalLower, max_eq_right hd] at h
    simpa only [finiteFloorCheck, decide_eq_true_eq] using h
  · rw [literalOriginalLower, max_eq_left (le_of_not_ge hd), zero_mul] at h
    linarith only [h, hf]

/-- UNEXECUTED original finite arithmetic proof proposal.  This is not a
claim that the 8192-array reduction or the row floor check has succeeded. -/
theorem literal_original_floor_proposal : literalOriginalFloorCheck = true := by
  decide +kernel

/-- Complete source-level linkage of this one key's actual directed cost
and its original P112/Q80 comparison.  Its finite proof terms have not run. -/
theorem literal_original_key_cost_floor_proposal :
    (((literalOriginalEndpoint.switchBaselineLo : ℤ) : ℝ) / (replayP : ℝ) ≤
      P2N48SavedParentRowRecost.anchorK * P2N48SavedParentRowRecost.omegaCap *
        actualMass keySavedRow) ∧
    (P2N48SavedParentRowRecost.anchorK * uniformOmegaUpper (originalQueryToken canonicalSourceArrays) *
      actualMass keySavedRow ≤
      ((literalOriginalEndpoint.omegaCostHi : ℤ) : ℝ) / (replayP : ℝ)) ∧
    finiteFloorCheck keySavedRow literalOriginalEndpoint = true :=
  ⟨literal_original_same_parent_directions.1, literal_original_same_parent_directions.2,
    literal_original_floor_check_sound literal_original_floor_proposal⟩

end
end ImbalancedChen.OriginalPairedN48LiteralKeyWeights
