import ImbalancedChen.P1CorrectedFifthStoredH45Check
import ImbalancedChen.P1OriginalVariableFourthSourceCoefficient
import ImbalancedChen.ActualFirstExitDensityProjection
import ImbalancedChen.ActualUpperCountingInputs

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The physical coefficient and counting attachment use exactly the corrected
ORIGINAL firstStop/raw-Q3 stored-fifth policy. Its full signed raw density
is the actual original variable-fourth density minus the actual corrected
charge, once the genuine finite rational h45 check is supplied. The common
universal small/rough reserve is then applied to THIS fifth coefficient.

Epsilon and the natural threshold precede every row, cap-table, mask and
licensing choice. No full-density mean, saving lower bound or integral
value is a premise. The adopted finite checks and original final theorem
remain OPEN. The empty-history unit and all signed rough terms survive.
-/

namespace ImbalancedChen.P1CorrectedFifthPhysicalTotalBridge

noncomputable section
open scoped Classical BigOperators
open P1CorrectedFifthDensityDictionary P1CorrectedFifthStoredH45Check

def originalFourthPolicy (D : HistoricalPrefixCapData) (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop) :
    Bool → List ℕ → Bool :=
  P1OriginalVariableFourthContinuation.producerPolicy4 (e : ℝ) chi D.m omega N
    rows4 licensed4

def correctedPolicy (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop) :
    Bool → List ℕ → Bool :=
  P1VariableFifthOriginalBaseQ3Bridge.correctedStoredPolicy5
    D J e chi omega N rows4 licensed4

def correctedRetain (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (N : ℕ) : List ℕ → Bool :=
  correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4 false

def fullRaw (R : Bool → List ℕ → Bool) (N cap : ℕ) (z : ℝ) : ℝ :=
  reciprocalTotientDensity (fixedRoughSupport (R false) N cap 0 z)
    (fixedRoughCoefficient (R false) N cap 0 z)

def physical (R : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : ℝ :=
  physicalDensitySum (actualSmallRoughModuli (R false) N cap w z)
    (actualSmallRoughRho (R false) N cap w z L)

theorem originalFourth_even
    (D : HistoricalPrefixCapData) (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (pre : List ℕ) : originalFourthPolicy D e chi omega N rows4 licensed4 true pre = true := by
  simp [originalFourthPolicy, P1OriginalVariableFourthContinuation.producerPolicy4,
    P1OriginalVariableFourthContinuation.policy4, fourthCappedUpperPolicy,
    thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
    HistoricalThirdCoarse.initialPolicy, frozenParityRosserPolicy,
    ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy]

theorem corrected_even
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (pre : List ℕ) : correctedPolicy D J e chi omega N rows4 licensed4 true pre = true := by
  unfold correctedPolicy P1VariableFifthOriginalBaseQ3Bridge.correctedStoredPolicy5
  apply fifthCappedUpperPolicy_even_retained
  intro history
  simp [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy]

theorem retained_eq_fullRaw (R : Bool → List ℕ → Bool)
    (heven : ∀ pre, R true pre = true) (N cap : ℕ) (z : ℝ) :
    firstExitRetainedPolynomial R (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z) = fullRaw R N cap z := by
  exact UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    R heven N cap 0 z

/-- Exact equality of the two ACTUAL full signed rough coefficients. The
finite checker, rather than a postulated policy comparison, supplies h45. -/
theorem fullRaw_fourth_sub_corrected_eq_charge
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows4 = true)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    fullRaw (originalFourthPolicy D e chi omega (N : ℝ) rows4 licensed4) N cap z -
      fullRaw (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4) N cap z =
      correctedStoredCharge D J e chi omega N cap z rows4 licensed4 := by
  have h := corrected_fourth_to_fifth_finite_density_identity
    D J e chi omega rows4 licensed4 howned hcheck N cap hN z
  have h4 := retained_eq_fullRaw
    (originalFourthPolicy D e chi omega (N : ℝ) rows4 licensed4)
    (originalFourth_even D e chi omega (N : ℝ) rows4 licensed4) N cap z
  have h5 := retained_eq_fullRaw
    (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4)
    (corrected_even D J e chi omega (N : ℝ) rows4 licensed4) N cap z
  change originalFourthRetained e chi D.m omega N cap z rows4 licensed4 = _ at h4
  change _ - firstExitRetainedPolynomial
    (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) = _ at h
  rw [h4, h5] at h
  exact h

/-- Original T3 minus its actual variable fourth charge minus corrected
fifth charge. No ordinary-parent ledger is substituted. -/
theorem corrected_fullRaw_eq_original_causal_total
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows4 = true)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    fullRaw (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4) N cap z =
      firstExitRetainedPolynomial (HistoricalThirdCoarse.policy (e : ℝ) chi D.m omega (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      actualHistoricalFourthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) D.m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi D.m omega (N : ℝ))
        (P1OriginalVariableFourthContinuation.producerLevel4
          (e : ℝ) chi D.m omega (N : ℝ) rows4 licensed4) N cap z -
      correctedStoredCharge D J e chi omega N cap z rows4 licensed4 := by
  have h4 := P1OriginalVariableFourthSourceCoefficient.original_policy_difference_eq_fourth_saving
    (e : ℝ) chi D.m omega N cap z rows4 licensed4 (by exact_mod_cast hN.le)
  have hd4 := retained_eq_fullRaw
    (originalFourthPolicy D e chi omega (N : ℝ) rows4 licensed4)
    (originalFourth_even D e chi omega (N : ℝ) rows4 licensed4) N cap z
  have h5 := fullRaw_fourth_sub_corrected_eq_charge D J e chi omega rows4 licensed4
    howned hcheck N cap hN z
  change _ - firstExitRetainedPolynomial
    (originalFourthPolicy D e chi omega (N : ℝ) rows4 licensed4)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) = _ at h4
  rw [hd4] at h4
  linarith

/-- Epsilon and N₀ are uniform before ANY corrected finite table or
producer/license choice. The bound concerns the physical fifth rho itself. -/
theorem exists_corrected_physical_normalized_le_fourth_sub_charge
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
            (e : ℚ) (chi omega : ℝ)
            (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
            (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop),
            P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega →
            storedH45Check D J e rows4 = true →
            let z := (N : ℝ) ^ (nu * r)
            physical (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4) N cap
                ((N : ℝ) ^ (nu * epsilon ^ 2)) z ((N : ℝ) ^ (nu * epsilon)) *
                Real.log (N : ℝ) / singularSeries N ≤
              fullRaw (originalFourthPolicy D e chi omega (N : ℝ) rows4 licensed4)
                  N cap z * Real.log (N : ℝ) / singularSeries N -
                correctedStoredCharge D J e chi omega N cap z rows4 licensed4 *
                  Real.log (N : ℝ) / singularSeries N + eta := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hsupply⟩ := exists_actualSmallRoughRho_density_le_full_reserve
    nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap D J e chi omega rows4 licensed4 howned hcheck
  have hNnat : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hS := singularSeries_pos N
  have h := hsupply N hN hEven cap hcap
    (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4 false)
  change physical _ N cap _ _ _ ≤ fullRaw _ N cap _ + _ at h
  have hsave := fullRaw_fourth_sub_corrected_eq_charge D J e chi omega rows4 licensed4
    howned hcheck N cap hNnat ((N : ℝ) ^ (nu * r))
  have hraw : fullRaw (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4)
      N cap ((N : ℝ) ^ (nu * r)) =
      fullRaw (originalFourthPolicy D e chi omega (N : ℝ) rows4 licensed4)
        N cap ((N : ℝ) ^ (nu * r)) -
      correctedStoredCharge D J e chi omega N cap ((N : ℝ) ^ (nu * r)) rows4 licensed4 := by
    linarith
  rw [hraw] at h
  have hn := mul_le_mul_of_nonneg_right h (div_nonneg hlog.le hS.le)
  dsimp only
  calc
    _ = physical (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4) N cap
        ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)) ((N : ℝ) ^ (nu * epsilon)) *
        (Real.log (N : ℝ) / singularSeries N) := by ring
    _ ≤ _ := hn
    _ = _ := by
      field_simp [ne_of_gt hlog, ne_of_gt hS]
      <;> ring

/-- The counting support is exactly the physical support of this same
corrected original fifth retention function. -/
theorem attached_moduli_eq_same_actual
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega nu r epsilon : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (cap : ℕ → ℕ) (N : ℕ) :
    attachedUpperModuli nu r epsilon
        (correctedRetain D J e chi omega rows4 licensed4) cap N =
      actualSmallRoughModuli
        (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4 false)
        N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)) := rfl

/-- Literal coefficient equality, including all negative rough mass and
the empty-history unit, before any counting estimate is applied. -/
theorem attached_coefficient_eq_same_rho
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega nu r epsilon : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (cap : ℕ → ℕ) (N d : ℕ) :
    attachedUpperCoefficient nu r epsilon
        (correctedRetain D J e chi omega rows4 licensed4) cap N d =
      actualSmallRoughRho
        (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4 false)
        N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
        ((N : ℝ) ^ (nu * epsilon)) d := rfl

theorem attached_physical_eq_same_physical
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega nu r epsilon : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (cap : ℕ → ℕ) (N : ℕ) :
    physicalDensitySum
        (attachedUpperModuli nu r epsilon
          (correctedRetain D J e chi omega rows4 licensed4) cap N)
        (attachedUpperCoefficient nu r epsilon
          (correctedRetain D J e chi omega rows4 licensed4) cap N) =
      physical (correctedPolicy D J e chi omega (N : ℝ) rows4 licensed4)
        N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
        ((N : ℝ) ^ (nu * epsilon)) := rfl

/-- The uniform reserve bound delivered directly for the very support and
coefficient passed to the counting theorem. -/
theorem exists_corrected_attached_normalized_le_fourth_sub_charge
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ → ℕ, (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) →
          ∀ (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
            (e : ℚ) (chi omega : ℝ)
            (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
            (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop),
            P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega →
            storedH45Check D J e rows4 = true →
            physicalDensitySum
                (attachedUpperModuli nu r epsilon
                  (correctedRetain D J e chi omega rows4 licensed4) cap N)
                (attachedUpperCoefficient nu r epsilon
                  (correctedRetain D J e chi omega rows4 licensed4) cap N) *
                Real.log (N : ℝ) / singularSeries N ≤
              fullRaw (originalFourthPolicy D e chi omega (N : ℝ) rows4 licensed4)
                  N (cap N) ((N : ℝ) ^ (nu * r)) * Real.log (N : ℝ) / singularSeries N -
                correctedStoredCharge D J e chi omega N (cap N)
                  ((N : ℝ) ^ (nu * r)) rows4 licensed4 *
                    Real.log (N : ℝ) / singularSeries N + eta := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ := exists_corrected_physical_normalized_le_fourth_sub_charge
    nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap D J e chi omega rows4 licensed4 howned hcheck
  rw [attached_physical_eq_same_physical]
  exact hbound N hN hEven (cap N) hcap D J e chi omega rows4 licensed4 howned hcheck

end
end ImbalancedChen.P1CorrectedFifthPhysicalTotalBridge
