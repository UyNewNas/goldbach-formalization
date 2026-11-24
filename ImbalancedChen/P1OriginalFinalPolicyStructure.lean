import ImbalancedChen.P4AOriginalFiniteAll22RawLedger
import ImbalancedChen.P4AOriginalFiniteFallbackCanonical

set_option autoImplicit false

/-!
RECONSTRUCTED P1 OUTPUT / SOURCE ONLY / NOT COMPILED OR KERNEL ACCEPTED.

The earlier local output file is unavailable. This file is a new, thin
export of existing proofs; it does not claim equality with the earlier
source hash or transfer any earlier compilation credit.

Every policy occurrence is the literal `RawLedger.finalPolicy`, with the
canonical bank and `NewFifthUnion.data`. The attached coefficient is the
existing `FiniteFallbackPolicy.rho` for that same policy. Integer majorants
quantify over all integers, including zero and negative arguments. The
selector exports retain their original regions, strict cubes, full and
selected squares, and tent inequalities. No density, tail, gain, numerical
price, or external distribution estimate is assumed or proved here.
-/

namespace ImbalancedChen.P1OriginalFinalPolicyStructure

noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteAll22RawLedger (finalPolicy)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalNewFifthUnion (data)
open P4AFallbackCanonicalBanks (bank)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
  (SecondRegion ThirdRegion secondMask thirdMask)
open VariableEnvelope

/-- The literal final policy retains every positive-parity branch. -/
theorem final_policy_even (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (p : List ℕ) :
    finalPolicy m r n e q a omega N true p = true := by
  unfold finalPolicy P4AOriginalFiniteFallbackPolicy.policy
    P4AOriginalFiniteFallbackPolicy.dispatch
  split
  · exact P4AOriginalFiniteFallbackOccurrence.positive
      (bank m) (data e q a) omega N p
  · exact P4AOriginalFiniteFallbackJointGain.lower_even
      (width r) n (data e q a) omega N p

/-- The existing physical coefficient uses the very same final policy. -/
theorem final_coefficient_is_same_policy (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (tau L : ℝ) :
    P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L =
      P4AUpperTaggedBetaAttachment.rho (finalPolicy m r n e q a omega N false)
        (fun _ => []) N N ((N : ℝ) ^ omega) (cutoff N) tau L := rfl

/-- The original first-exit rough majorant, specialized to the final policy. -/
theorem final_raw_integer_majorant (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (hz : cutoff N ≤ (N : ℝ)) (x : ℤ) :
    actualIntervalRoughIndicator N ((N : ℝ) ^ omega) (cutoff N) x ≤
      supportedDivisorSum
        (P4AUpperTaggedParityCompiler.«universe» N N ((N : ℝ) ^ omega) (cutoff N))
        (P4AUpperTaggedParityCompiler.raw (finalPolicy m r n e q a omega N false)
          N N ((N : ℝ) ^ omega) (cutoff N)) x.natAbs :=
  P4AUpperTaggedBetaAttachment.raw_rough_majorant
    (finalPolicy m r n e q a omega N false) N N ((N : ℝ) ^ omega) (cutoff N) hz x

/-- The raw coefficient keeps the original Möbius sign and actual support. -/
theorem final_raw_value (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N d : ℕ) :
    P4AUpperTaggedParityCompiler.raw (finalPolicy m r n e q a omega N false)
        N N ((N : ℝ) ^ omega) (cutoff N) d =
      if d ∈ P4AUpperTaggedParityCompiler.rawSupport
          (finalPolicy m r n e q a omega N false) N N ((N : ℝ) ^ omega) (cutoff N)
      then (ArithmeticFunction.moebius d : ℝ) else 0 :=
  P4AUpperTaggedParityCompiler.raw_value
    (finalPolicy m r n e q a omega N false) N N ((N : ℝ) ^ omega) (cutoff N) d

/-- The same attached coefficient majorizes the indicator at every integer. -/
theorem final_integer_majorant (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (tau L : ℝ)
    (hL : 1 < L) (hwL : (N : ℝ) ^ omega ≤ L)
    (hwz : (N : ℝ) ^ omega ≤ cutoff N) (hz : cutoff N ≤ (N : ℝ))
    (x : ℤ) :
    actualSmallRoughIndicator N (cutoff N) x ≤
      physicalDivisorSum (moduli N ((N : ℝ) ^ omega))
        (P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L)
        x.natAbs :=
  P4AUpperTaggedBetaAttachment.rho_majorant
    (finalPolicy m r n e q a omega N false) (fun _ => [])
    N N ((N : ℝ) ^ omega) (cutoff N) tau L hL hwL hwz hz x

/-- The integer majorant written with the literal strict sieve product. -/
theorem final_integer_sieve_majorant (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (tau L : ℝ)
    (hL : 1 < L) (hwL : (N : ℝ) ^ omega ≤ L)
    (hwz : (N : ℝ) ^ omega ≤ cutoff N) (hz : cutoff N ≤ (N : ℝ))
    (x : ℤ) :
    (if x.natAbs.Coprime (sieveProduct N (Nat.ceil (cutoff N))) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (moduli N ((N : ℝ) ^ omega))
        (P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L)
        x.natAbs := by
  have h := final_integer_majorant m r n e q a omega N tau L hL hwL hwz hz x
  rwa [actualSmallRoughIndicator_eq_sieveProduct_natAbs] at h

/-- Nonnegativity includes the divisor sum at zero and at negative integers. -/
theorem final_integer_divisorSum_nonneg (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (tau L : ℝ)
    (hL : 1 < L) (hwL : (N : ℝ) ^ omega ≤ L)
    (hwz : (N : ℝ) ^ omega ≤ cutoff N) (hz : cutoff N ≤ (N : ℝ))
    (x : ℤ) :
    0 ≤ physicalDivisorSum (moduli N ((N : ℝ) ^ omega))
      (P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L)
      x.natAbs :=
  P4AUpperTaggedBetaAttachment.rho_divisorSum_nonneg
    (finalPolicy m r n e q a omega N false) (fun _ => [])
    N N ((N : ℝ) ^ omega) (cutoff N) tau L hL hwL hwz hz x

theorem final_coefficient_abs_le_one (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (tau L : ℝ) (d : ℕ) :
    |P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L d| ≤ 1 :=
  P4AUpperTaggedBetaAttachment.rho_abs_le_one
    (finalPolicy m r n e q a omega N false) (fun _ => [])
    N N ((N : ℝ) ^ omega) (cutoff N) tau L d

/-- Reuse the support step in `FiniteFallbackPhysicalRange.data_physical_range`. -/
theorem final_nonzero_mem_moduli (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (tau L : ℝ) {d : ℕ}
    (hd : P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L d ≠ 0) :
    d ∈ moduli N ((N : ℝ) ^ omega) := by
  by_contra hnot
  exact hd (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hnot)

theorem final_modulus_squarefree (N : ℕ) (omega : ℝ) {d : ℕ}
    (hd : d ∈ moduli N ((N : ℝ) ^ omega)) : Squarefree d :=
  P4AUpperTaggedBetaAttachment.support_squarefree N N ((N : ℝ) ^ omega) (cutoff N) hd

theorem final_modulus_coprime_target (N : ℕ) (omega : ℝ) {d : ℕ}
    (hd : d ∈ moduli N ((N : ℝ) ^ omega)) : d.Coprime N :=
  P4AUpperTaggedBetaAttachment.support_coprime_target N N ((N : ℝ) ^ omega) (cutoff N) hd

/-- The second selector is the canonical bank used by `finalPolicy`. -/
theorem selected_second {m : ℕ} {t : Fin 2 → ℝ} {c : ℚ}
    (h : P4AOriginalFiniteFallbackBank.read m (bank m).second t = some c) :
    SecondRegion (t 0) (t 1) ∧ 3 * t 0 < v (t 0) ∧ v (t 0) < c ∧
      (c : ℝ) < 299 / 500 ∧ (1 / 2 : ℝ) < c ∧
      (∀ i, prefixSquareExpr t i < c) ∧
      (∀ i ∉ secondMask, selectedSquareExpr secondMask t i < c) ∧
      (c : ℝ) < v (t 1) :=
  P4AOriginalFiniteFallbackCanonical.selected_second h

/-- The third selector retains all original ancestor and selected-square guards. -/
theorem selected_third {m : ℕ} {t : Fin 3 → ℝ} {c : ℚ}
    (h : P4AOriginalFiniteFallbackBank.read m (bank m).third t = some c) :
    ThirdRegion (t 0) (t 1) (t 2) ∧ 3 * t 0 < v (t 0) ∧
      t 0 + t 1 + 3 * t 2 < v (t 0) ∧ v (t 0) < c ∧
      (c : ℝ) < 299 / 500 ∧ (1 / 2 : ℝ) < c ∧
      (∀ i, prefixSquareExpr t i < c) ∧
      (∀ i ∉ thirdMask, selectedSquareExpr thirdMask t i < c) ∧
      (c : ℝ) < v (t 1 + t 2) :=
  P4AOriginalFiniteFallbackCanonical.selected_third h

end
end ImbalancedChen.P1OriginalFinalPolicyStructure
