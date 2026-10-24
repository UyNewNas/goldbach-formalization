import ImbalancedChen.P1OriginalCoarseFifthContinuationCells
import ImbalancedChen.ActualUpperPolicyFiniteBridge
import ImbalancedChen.PhysicalUpperWeightBridge

/-!
# The fixed physical coefficient of the original historical fifth policy

The policy uses the original coarse initial firstStop rule and raw activated
third level, followed by the real original fifth lookup. Unit local weights
fix its retained modulus support before an integer is evaluated. The same
coefficient supplies both the integer divisor evaluation and the signed
reciprocal-totient density; its small/rough attachment is identified as one
physical arithmetic function. No density estimate or telescope is asserted.
-/

namespace ImbalancedChen.P1OriginalHistoricalPhysicalCoefficient

noncomputable section

open scoped Classical BigOperators

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
  (J4 : Finset (Fin 4 → Fin (m + 1))) (cap4 : (Fin 4 → Fin (m + 1)) → ℚ)
  (J5 : Finset (Fin 5 → Fin (m + 1))) (cap5 : (Fin 5 → Fin (m + 1)) → ℚ)

/-- The literal original coarse base and activated raw third level are
kept; the fifth selector is the canonical original continuation lookup. -/
def finalPolicy (N : ℝ) : Bool → List ℕ → Bool :=
  fifthCappedUpperPolicy (HistoricalThirdCoarse.initialPolicy (e : ℝ) m N)
    (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega N)
    (P1OriginalCoarseFifthContinuation.level5 e chi m omega J4 cap4 J5 cap5 N)

local notation "P" => finalPolicy e chi m omega J4 cap4 J5 cap5

theorem finalPolicy_eq_original_policy5 (N : ℝ) :
    P N = P1OriginalCoarseFifthContinuation.policy5 e chi m omega J4 cap4 J5 cap5 N := by
  rfl

theorem finalPolicy_even (N : ℝ) (history : List ℕ) : P N true history = true := by
  simp [finalPolicy, fifthCappedUpperPolicy, thirdCappedUpperPolicy,
    firstExitDepthSplicePolicy, HistoricalThirdCoarse.initialPolicy,
    frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
    oddFirstExitPolicy]

/-- All original first/third tests are untouched through rank four. -/
theorem finalPolicy_through_four (N : ℝ) (positive : Bool) (history : List ℕ)
    (hlen : history.length ≤ 4) :
    P N positive history = HistoricalThirdCoarse.policy (e : ℝ) chi m omega N positive history := by
  simp only [finalPolicy, fifthCappedUpperPolicy, firstExitDepthSplicePolicy, if_pos hlen,
    HistoricalThirdCoarse.policy]

theorem finalPolicy_first_test (N : ℝ) (p : ℕ) :
    P N false [p] = true ↔
      ordinaryRosserPrefixAdmissible false (N ^ HistoricalThirdCoarse.initial (e : ℝ)) [p] ∧
        HistoricalThirdCoarse.firstStop (e : ℝ) m N [p] := by
  rw [finalPolicy_through_four e chi m omega J4 cap4 J5 cap5 N false [p] (by simp),
    HistoricalThirdCoarse.policy_through_two (e : ℝ) chi m omega N false [p] (by simp)]
  simp [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy]

/-- The new level is read at the actual fifth ancestor. Its inherited
fourth/third fallback remains the canonical original lookup's fallback. -/
theorem finalPolicy_after_four (N : ℝ) (positive : Bool) (history : List ℕ)
    (hlen : 4 < history.length) :
    P N positive history = ordinaryParityRosserPolicy false
      (P1OriginalCoarseFifthContinuation.level5 e chi m omega J4 cap4 J5 cap5 N
        (rosserAncestor 5 history)) positive history := by
  simp [finalPolicy, fifthCappedUpperPolicy, firstExitDepthSplicePolicy,
    Nat.not_le_of_gt hlen, frozenParityRosserPolicy, ancestorFrozenPolicy]

theorem finalPolicy_outside_fifth (N : ℝ) (positive : Bool) (history : List ℕ)
    (hlen : 4 < history.length)
    (hout5 : ∀ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
      primeHistoryLogCoordinates N 5 (rosserAncestor 5 history) ∉
        logPrimeMeshCell 0 (19 / 96) m j) :
    P N positive history = ordinaryParityRosserPolicy false
      (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 N (rosserAncestor 4 history))
      positive history := by
  rw [finalPolicy_after_four e chi m omega J4 cap4 J5 cap5 N positive history hlen,
    P1OriginalCoarseFifthContinuation.level5_outside e chi m omega J4 cap4 J5 cap5 N
      (rosserAncestor 5 history) hout5, rosserAncestor_four_five]

/-- Outside both continuation families an inactive original third ancestor
keeps exactly Theta-2e, with no replacement by a geometry-only ceiling. -/
theorem finalPolicy_original_Theta_fallback (N : ℝ) (positive : Bool) (history : List ℕ)
    (hlen : 4 < history.length)
    (hout5 : ∀ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
      primeHistoryLogCoordinates N 5 (rosserAncestor 5 history) ∉
        logPrimeMeshCell 0 (19 / 96) m j)
    (hout4 : ∀ j ∈ P1OriginalCoarseContinuation.selectedFourthCells e chi m omega J4,
      primeHistoryLogCoordinates N 4 (rosserAncestor 4 history) ∉
        logPrimeMeshCell 0 (19 / 96) m j)
    (hinactive : ¬HistoricalThirdCoarse.active omega N (rosserAncestor 3 history)) :
    P N positive history = ordinaryParityRosserPolicy false
      (N ^ ((299 / 500 : ℝ) - 2 * (e : ℝ))) positive history := by
  rw [finalPolicy_outside_fifth e chi m omega J4 cap4 J5 cap5 N positive history hlen hout5,
    P1OriginalCoarseContinuation.level4_outside e chi m omega J4 cap4 N
      (rosserAncestor 4 history) hout4,
    HistoricalThirdCoarse.frozenLevel, rosserAncestor_nested 3 4 (by omega : 3 ≤ 4),
    HistoricalThirdCoarse.rawLevel_inactive (e : ℝ) chi m omega N _ hinactive]
  simp [HistoricalThirdCoarse.initial, extendedDistributionCap]

/-- Unit local weights fix the support before any arithmetic evaluation. -/
def roughSupport (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  firstExitRetainedModuli (P (N : ℝ)) (roughPrimeUniverse N cap w z)

def roughCoefficientInt (N cap : ℕ) (w z : ℝ) (d : ℕ) : ℤ :=
  firstExitRetainedCoefficient (P (N : ℝ)) (roughPrimeUniverse N cap w z) d

def roughCoefficient (N cap : ℕ) (w z : ℝ) (d : ℕ) : ℝ :=
  (roughCoefficientInt e chi m omega J4 cap4 J5 cap5 N cap w z d : ℝ)

local notation "S" => roughSupport e chi m omega J4 cap4 J5 cap5
local notation "CInt" => roughCoefficientInt e chi m omega J4 cap4 J5 cap5
local notation "C" => roughCoefficient e chi m omega J4 cap4 J5 cap5

theorem roughSupport_eq_unit_leaf_products (N cap : ℕ) (w z : ℝ) :
    S N cap w z = ((firstExitRootLeaves (P (N : ℝ)) (fun _ => 1)
      (roughPrimeUniverse N cap w z)).map (fun leaf => leaf.selected.prod)).toFinset := by
  rfl

theorem roughCoefficientInt_lookup (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    CInt N cap w z d = if d ∈ S N cap w z then ArithmeticFunction.moebius d else 0 := by
  rfl

theorem roughSupport_eq_fixed (N cap : ℕ) (w z : ℝ) :
    S N cap w z = fixedRoughSupport (P (N : ℝ) false) N cap w z := by
  exact (UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (P (N : ℝ)) (finalPolicy_even e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap w z).symm

theorem roughCoefficient_eq_fixed (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    C N cap w z d = fixedRoughCoefficient (P (N : ℝ) false) N cap w z d := by
  exact (UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    (P (N : ℝ)) (finalPolicy_even e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap w z d).symm

theorem roughCoefficientInt_abs_le_one (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    |CInt N cap w z d| ≤ 1 := by
  exact firstExitRetainedCoefficient_abs_le_one _ _ d

theorem roughCoefficient_abs_le_one (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    |C N cap w z d| ≤ 1 := by
  change |(CInt N cap w z d : ℝ)| ≤ 1
  exact_mod_cast roughCoefficientInt_abs_le_one e chi m omega J4 cap4 J5 cap5 N cap w z d

theorem roughSupport_squarefree (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ S N cap w z) : Squarefree d := by
  exact firstExitRetainedModuli_squarefree _ _ (roughPrimeUniverse_nodup N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) hd

theorem roughSupport_coprime_target (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ S N cap w z) : d.Coprime N := by
  rw [roughSupport_eq_fixed] at hd
  exact fixedRoughSupport_coprime_target _ N cap w z hd

theorem roughSupport_roughPrimeSupportedAt (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ S N cap w z) : RoughPrimeSupportedAt w d := by
  rw [roughSupport_eq_fixed] at hd
  exact fixedRoughSupport_roughPrimeSupportedAt _ N cap w z hd

/-- Every local-weight evaluation uses this very fixed coefficient. -/
theorem polynomial_eq_rough_sum (N cap : ℕ) (w z : ℝ) (h : ℕ → ℝ) :
    firstExitRetainedPolynomial (P (N : ℝ)) h [] true 1 (roughPrimeUniverse N cap w z) =
      ∑ d ∈ S N cap w z, C N cap w z d * d.primeFactors.prod h := by
  exact firstExitRetainedPolynomial_eq_retainedModuli_sum _ h _
    (roughPrimeUniverse_nodup N cap w z) (fun _ hp => mem_roughPrimeUniverse_prime hp)

theorem integer_evaluation (N cap : ℕ) (w z : ℝ) (n : ℤ) :
    firstExitRetainedPolynomial (P (N : ℝ)) (integerDivisorIndicator n)
      [] true 1 (roughPrimeUniverse N cap w z) =
    physicalDivisorSum (S N cap w z) (C N cap w z) n.natAbs := by
  rw [polynomial_eq_rough_sum]
  unfold physicalDivisorSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [primeFactors_prod_integerDivisorIndicator
    (roughSupport_squarefree e chi m omega J4 cap4 J5 cap5 N cap w z hd) n]
  by_cases hdn : d ∣ n.natAbs <;> simp [hdn]

/-- The signed reciprocal-totient density uses the same actual support
and lookup as the integer divisor evaluation. -/
theorem reciprocal_totient_density (N cap : ℕ) (w z : ℝ) :
    firstExitRetainedPolynomial (P (N : ℝ)) (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap w z) =
    reciprocalTotientDensity (S N cap w z) (C N cap w z) := by
  rw [polynomial_eq_rough_sum]
  unfold reciprocalTotientDensity
  apply Finset.sum_congr rfl
  intro d hd
  rw [primeFactors_prod_reciprocalTotient
    (roughSupport_squarefree e chi m omega J4 cap4 J5 cap5 N cap w z hd)]
  ring

/-- One physical small/rough carrier, fixed independently of the test integer. -/
def physicalModuli (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  actualSmallRoughModuli (P (N : ℝ) false) N cap w z

def rho (N cap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  actualSmallRoughRho (P (N : ℝ) false) N cap w z L

local notation "Q" => physicalModuli e chi m omega J4 cap4 J5 cap5
local notation "Rho" => rho e chi m omega J4 cap4 J5 cap5

theorem physicalModuli_eq_actual_attachment (N cap : ℕ) (w z : ℝ) :
    Q N cap w z = smallRoughModuli (actualSmallRosserSupport N cap w) (S N cap w z) := by
  unfold physicalModuli actualSmallRoughModuli
  rw [← roughSupport_eq_fixed e chi m omega J4 cap4 J5 cap5 N cap w z]

theorem rho_eq_actual_attachment (N cap : ℕ) (w z L : ℝ) :
    Rho N cap w z L = smallRoughRho (actualSmallRosserSupport N cap w) (S N cap w z)
      (C N cap w z) (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) := by
  exact UpperPolicyFiniteBridge.actualSmallRoughRho_eq_firstExitAttachment (P (N : ℝ))
    (finalPolicy_even e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap w z L

theorem rho_abs_le_one (N cap : ℕ) (w z L : ℝ) (d : ℕ) : |Rho N cap w z L d| ≤ 1 := by
  exact actualSmallRoughRho_abs_le_one _ N cap w z L d

theorem physicalModuli_squarefree_coprime_target (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ Q N cap w z) : Squarefree d ∧ d.Coprime N := by
  exact ⟨actualSmallRoughModuli_squarefree _ N cap w z hd,
    actualSmallRoughModuli_coprime_target _ N cap w z hd⟩

/-- The physical integer evaluation keeps the signed lower/upper small
weight selected by this very rough coefficient. -/
theorem physical_integer_evaluation (N cap : ℕ) (w z L : ℝ) (n : ℤ) :
    physicalDivisorSum (Q N cap w z) (Rho N cap w z L) n.natAbs =
      signSensitiveAttachment (S N cap w z) (C N cap w z)
        (supportedDivisorSum (actualSmallRosserSupport N cap w)
          (actualSmallRosserMinus N cap w L) n.natAbs)
        (supportedDivisorSum (actualSmallRosserSupport N cap w)
          (actualSmallRosserPlus N cap w L) n.natAbs) n.natAbs := by
  rw [physicalModuli_eq_actual_attachment, rho_eq_actual_attachment]
  exact (signSensitiveAttachment_eq_smallRough_physicalDivisorSum
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => roughSupport_roughPrimeSupportedAt e chi m omega J4 cap4 J5 cap5 N cap w z hd)
    (C N cap w z) (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
    n.natAbs).symm

/-- The density is the signed factorization of exactly the same physical
coefficient and support used in the integer identity above. -/
theorem physical_reciprocal_totient_density (N cap : ℕ) (w z L : ℝ) :
    physicalDensitySum (Q N cap w z) (Rho N cap w z L) =
      signSensitiveReciprocalTotientDensity (S N cap w z) (C N cap w z)
        (reciprocalTotientDensity (actualSmallRosserSupport N cap w)
          (actualSmallRosserMinus N cap w L))
        (reciprocalTotientDensity (actualSmallRosserSupport N cap w)
          (actualSmallRosserPlus N cap w L)) := by
  rw [physicalModuli_eq_actual_attachment, rho_eq_actual_attachment]
  exact physicalDensitySum_smallRoughRho_eq_signSensitive
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => roughSupport_roughPrimeSupportedAt e chi m omega J4 cap4 J5 cap5 N cap w z hd)
    (C N cap w z) (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)

end

end ImbalancedChen.P1OriginalHistoricalPhysicalCoefficient
