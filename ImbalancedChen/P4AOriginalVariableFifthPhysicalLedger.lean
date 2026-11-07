import ImbalancedChen.P1OriginalVariableFifthContinuation
import ImbalancedChen.P1OriginalVariableFourthSourceCoefficient
import ImbalancedChen.P4AHistoricalSameRhoAttachment
import ImbalancedChen.ActualFirstExitDensityProjection
import ImbalancedChen.P1CorrectedFifthCausalTupleDictionary
import ImbalancedChen.ActualUpperCountingInputs

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual original variable fourth/fifth policies share the firstStop/raw-Q3
parent.  This file identifies their literal fixed rough coefficients with the
finite causal saving, retains the signed small-prime attachment correction,
and gives the actual fifth rho a direct one-reserve causal upper ledger.
The fourth and fifth maxima supply h34 and h45; no density bound or saving
identity is a hypothesis.  All producer rows, including losing and overlapping
rows, remain the input of the original finite maxima.

The corrected selected stored-cap policy is a separate construction.  This
file does not substitute that policy for the variable fifth maximum: the
stored cap still needs a comparison with the actual variable fourth ancestor.
No analytic passage from the finite charge to its gated integral is asserted.
-/

namespace ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger

noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation

abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

def raw (R : Bool → List ℕ → Bool) (N cap : ℕ) (w z : ℝ) : ℝ :=
  reciprocalTotientDensity (fixedRoughSupport (R false) N cap w z)
    (fixedRoughCoefficient (R false) N cap w z)

def negative (R : Bool → List ℕ → Bool) (N cap : ℕ) (w z : ℝ) : ℝ :=
  p4aNegativeRoughMass (fixedRoughSupport (R false) N cap w z)
    (fixedRoughCoefficient (R false) N cap w z)

def physical (R : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : ℝ :=
  physicalDensitySum (actualSmallRoughModuli (R false) N cap w z)
    (actualSmallRoughRho (R false) N cap w z L)

def smallPlus (N cap : ℕ) (w L : ℝ) : ℝ :=
  reciprocalTotientDensity (actualSmallRosserSupport N cap w)
    (actualSmallRosserPlus N cap w L)

def smallMinus (N cap : ℕ) (w L : ℝ) : ℝ :=
  reciprocalTotientDensity (actualSmallRosserSupport N cap w)
    (actualSmallRosserMinus N cap w L)

theorem physical_eq_signed_raw (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) :
    physical R N cap w z L =
      raw R N cap w z * smallPlus N cap w L +
        negative R N cap w z * (smallPlus N cap w L - smallMinus N cap w L) := by
  rw [physical, actualSmallRoughRho_density_eq]
  exact p4a_signSensitiveDensity_eq_raw_add_negativeMass _ _ _ _

section OriginalRows

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (Label5 m))
  (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m))

theorem fourth_even (N : ℝ) (pre : List ℕ) :
    producerPolicy4 (e : ℝ) chi m omega N rows4 licensed4 true pre = true := by
  simp [producerPolicy4, policy4, fourthCappedUpperPolicy,
    thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
    HistoricalThirdCoarse.initialPolicy, frozenParityRosserPolicy,
    ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy]

theorem fifth_even (N : ℝ) (pre : List ℕ) :
    P1OriginalVariableFifthContinuation.policy5 e chi m omega N
      rows4 licensed4 J5 rows5 true pre = true := by
  simp [P1OriginalVariableFifthContinuation.policy5, fifthCappedUpperPolicy,
    thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
    HistoricalThirdCoarse.initialPolicy, frozenParityRosserPolicy,
    ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy]

/-- The first-exit coefficient is exactly the one attached to physical rho. -/
theorem fifth_fixedCoefficient_eq_firstExit
    (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    fixedRoughCoefficient
        (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
          rows4 licensed4 J5 rows5 false) N cap w z d =
      (firstExitRetainedCoefficient
        (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
          rows4 licensed4 J5 rows5) (roughPrimeUniverse N cap w z) d : ℝ) := by
  exact UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    _ (fifth_even e chi m omega rows4 licensed4 J5 rows5 (N : ℝ)) N cap w z d

/-- The two actual fixed raw densities have the genuine fifth saving as
their difference, without a selected-cap comparison premise. -/
theorem raw_fourth_sub_fifth_eq_saving
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    raw (producerPolicy4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4) N cap 0 z -
      raw (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5) N cap 0 z =
      P1OriginalVariableFifthContinuation.actualFifthSaving e chi m omega
        rows4 licensed4 J5 rows5 N cap z := by
  unfold raw
  rw [← UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      _ (fourth_even e chi m omega rows4 licensed4 (N : ℝ)) N cap 0 z,
    ← UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      _ (fifth_even e chi m omega rows4 licensed4 J5 rows5 (N : ℝ)) N cap 0 z]
  unfold producerPolicy4 policy4 P1OriginalVariableFifthContinuation.policy5
    P1OriginalVariableFifthContinuation.actualFifthSaving
  apply actualHistoricalFifthSaving_eq
  · intro state hstate
    exact producer_actual_h34 (e : ℝ) chi m omega N cap hN.le z
      rows4 licensed4 state hstate
  · intro frontier hfrontier candidate hcandidate
    exact P1OriginalVariableFifthContinuation.actual_h45
      e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 N cap hN z rfl
      frontier candidate hfrontier hcandidate

/-- Complete original-T3 tuple charge; both literal strict own-cube tests
are kept inside the residual. No admission test is added to this carrier. -/
def fifthTupleCharge (N cap : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ firstExitFrontierTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 z),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      P1CorrectedFifthCausalTupleDictionary.literalTupleDifference
        (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
        (P1OriginalVariableFifthContinuation.level5 e chi m omega (N : ℝ)
          rows4 licensed4 J5 rows5) N cap p

/-- The finite charge in the physical ledger is exactly the normalized
complete tuple charge; the same original row maxima occur in both terms. -/
theorem fifthSaving_normalized_eq_tupleCharge
    (N cap : ℕ) (z : ℝ) :
    P1OriginalVariableFifthContinuation.actualFifthSaving e chi m omega
        rows4 licensed4 J5 rows5 N cap z * Real.log (N : ℝ) / singularSeries N =
      fifthTupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap z := by
  exact P1CorrectedFifthCausalTupleDictionary.actualHistoricalFifthSaving_eq_literalTupleSum
    (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
    (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
    (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
    (P1OriginalVariableFifthContinuation.level5 e chi m omega (N : ℝ)
      rows4 licensed4 J5 rows5) N cap z

/-- Same physical weights and exact signed correction.  In particular, the
finite fifth charge is not attached to beta-plus without the negative mass. -/
theorem physical_fourth_sub_fifth_eq_saving
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z L : ℝ) :
    physical (producerPolicy4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
        N cap 0 z L -
      physical (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5) N cap 0 z L =
      P1OriginalVariableFifthContinuation.actualFifthSaving e chi m omega
          rows4 licensed4 J5 rows5 N cap z * smallPlus N cap 0 L +
        (negative (producerPolicy4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
            N cap 0 z -
          negative (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
            rows4 licensed4 J5 rows5) N cap 0 z) *
          (smallPlus N cap 0 L - smallMinus N cap 0 L) := by
  rw [physical_eq_signed_raw, physical_eq_signed_raw]
  have h := raw_fourth_sub_fifth_eq_saving e chi m omega rows4 licensed4
    J5 rows5 N cap hN z
  rw [← h]
  ring

/-- Exact normalized attachment of the complete finite prime charge.
The negative-mass correction uses these same two actual rough coefficients. -/
theorem normalized_physical_difference_eq_tupleCharge
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z L : ℝ) :
    (physical (producerPolicy4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
        N cap 0 z L -
      physical (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5) N cap 0 z L) *
        Real.log (N : ℝ) / singularSeries N =
      fifthTupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap z *
          smallPlus N cap 0 L +
        ((negative (producerPolicy4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
            N cap 0 z -
          negative (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
            rows4 licensed4 J5 rows5) N cap 0 z) *
          Real.log (N : ℝ) / singularSeries N) *
          (smallPlus N cap 0 L - smallMinus N cap 0 L) := by
  rw [physical_fourth_sub_fifth_eq_saving e chi m omega rows4 licensed4 J5 rows5
    N cap hN z L,
    ← fifthSaving_normalized_eq_tupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap z]
  simp only [div_eq_mul_inv]
  ring

/-- The coefficient in the actual all22 counting attachment is this same
variable fifth rho, with the same target, cutoffs, small weights and cap. -/
theorem counting_attachment_is_same_physical
    (nu r epsilon : ℝ) (cap : ℕ → ℕ) (N : ℕ) :
    physicalDensitySum
        (attachedUpperModuli nu r epsilon
          (fun N => P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
            rows4 licensed4 J5 rows5 false) cap N)
        (attachedUpperCoefficient nu r epsilon
          (fun N => P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
            rows4 licensed4 J5 rows5 false) cap N) =
      physical (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5) N (cap N)
        ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
        ((N : ℝ) ^ (nu * epsilon)) := rfl

/-- Exact three-stage ledger for the same original base and raw Q3.  Each
causal saving occurs once; the ordinary generic-D parent is never inserted. -/
theorem raw_fifth_eq_original_causal_ledger
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    raw (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5) N cap 0 z =
      firstExitRetainedPolynomial
          (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
        actualHistoricalFourthSaving
          (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
          (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
          (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4) N cap z -
        P1OriginalVariableFifthContinuation.actualFifthSaving e chi m omega
          rows4 licensed4 J5 rows5 N cap z := by
  have h4 := P1OriginalVariableFourthSourceCoefficient.original_policy_difference_eq_fourth_saving
    (e : ℝ) chi m omega N cap z rows4 licensed4 hN.le
  have h5 := raw_fourth_sub_fifth_eq_saving e chi m omega rows4 licensed4
    J5 rows5 N cap hN z
  have hd := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    _ (fourth_even e chi m omega rows4 licensed4 (N : ℝ)) N cap 0 z
  change _ = raw _ N cap 0 z at hd
  rw [hd] at h4
  linarith

end OriginalRows

/-- The reserve is uniform before either finite row table is chosen. It
bounds the literal fifth physical rho directly and uses one reserve. -/
theorem exists_original_fifth_physical_le_causal_ledger
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
            (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
            (J5 : Finset (Label5 m))
            (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)),
            let z := (N : ℝ) ^ (nu * r)
            physical (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
                rows4 licensed4 J5 rows5) N cap
                ((N : ℝ) ^ (nu * epsilon ^ 2)) z ((N : ℝ) ^ (nu * epsilon)) ≤
              firstExitRetainedPolynomial
                  (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
                  (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
                  (roughPrimeUniverse N cap 0 z) -
                actualHistoricalFourthSaving
                  (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
                  (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
                  (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4) N cap z -
                P1OriginalVariableFifthContinuation.actualFifthSaving e chi m omega
                  rows4 licensed4 J5 rows5 N cap z +
                eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
    N₀, hN₀, hsupply⟩ := exists_actualSmallRoughRho_density_le_full_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap e chi m omega rows4 licensed4 J5 rows5
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have h := hsupply N hN hEven cap hcap
    (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
      rows4 licensed4 J5 rows5 false)
  change physical _ N cap _ _ _ ≤ raw _ N cap 0 _ + _ at h
  rw [raw_fifth_eq_original_causal_ledger e chi m omega rows4 licensed4 J5 rows5
    N cap hN1 ((N : ℝ) ^ (nu * r))] at h
  exact h

/-- Normalized one-reserve bound with the complete finite tuple charge in
its manuscript normalization.  The fourth density remains the actual
original variable fourth coefficient, rather than a presumed integral. -/
theorem exists_original_fifth_physical_normalized_le_fourth_sub_tupleCharge
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
            (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
            (J5 : Finset (Label5 m))
            (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)),
            let z := (N : ℝ) ^ (nu * r)
            physical (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
                rows4 licensed4 J5 rows5) N cap
                ((N : ℝ) ^ (nu * epsilon ^ 2)) z ((N : ℝ) ^ (nu * epsilon)) *
                Real.log (N : ℝ) / singularSeries N ≤
              raw (producerPolicy4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
                  N cap 0 z * Real.log (N : ℝ) / singularSeries N -
                fifthTupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap z + eta := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
    N₀, hN₀, hsupply⟩ := exists_actualSmallRoughRho_density_le_full_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap e chi m omega rows4 licensed4 J5 rows5
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hS := singularSeries_pos N
  have h := hsupply N hN hEven cap hcap
    (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
      rows4 licensed4 J5 rows5 false)
  change physical _ N cap _ _ _ ≤ raw _ N cap 0 _ + _ at h
  have hsave := raw_fourth_sub_fifth_eq_saving e chi m omega rows4 licensed4
    J5 rows5 N cap hN1 ((N : ℝ) ^ (nu * r))
  have hraw :
      raw (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5) N cap 0 ((N : ℝ) ^ (nu * r)) =
      raw (producerPolicy4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
        N cap 0 ((N : ℝ) ^ (nu * r)) -
      P1OriginalVariableFifthContinuation.actualFifthSaving e chi m omega
        rows4 licensed4 J5 rows5 N cap ((N : ℝ) ^ (nu * r)) := by
    linarith
  rw [hraw] at h
  have hn := mul_le_mul_of_nonneg_right h (div_nonneg hlog.le hS.le)
  have hcharge := fifthSaving_normalized_eq_tupleCharge e chi m omega rows4 licensed4
    J5 rows5 N cap ((N : ℝ) ^ (nu * r))
  dsimp only
  calc
    _ = physical (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5) N cap ((N : ℝ) ^ (nu * epsilon ^ 2))
        ((N : ℝ) ^ (nu * r)) ((N : ℝ) ^ (nu * epsilon)) *
        (Real.log (N : ℝ) / singularSeries N) := by ring
    _ ≤ _ := hn
    _ = _ := by
      rw [← hcharge]
      field_simp [ne_of_gt hlog, ne_of_gt hS]
      <;> ring

end
end ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger
