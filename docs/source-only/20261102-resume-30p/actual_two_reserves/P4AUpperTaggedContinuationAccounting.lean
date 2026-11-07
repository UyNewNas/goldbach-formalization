import ImbalancedChen.P4ACommonPolicyTaggedCompiler

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

Exact sign-resolved accounting for the same literal O compiler rho.
Positive mixed changes are 0 -> 1 and attach beta-plus; negative mixed
changes are -1 -> 0 and contribute beta-minus, with its actual sign.
The full-to-presieved continuation correction is subtracted exactly.

The only asymptotic estimate consumed is the existing actual beta attachment
supplier. No raw endpoint, coefficient-error budget, continuation-smallness,
all22/full87 identity, or final reserve witness is an input or conclusion.
-/

namespace ImbalancedChen.P4AUpperTaggedContinuationAccounting

noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler

def positiveChangedMass (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) : ℝ :=
  ∑ d ∈ (universe N cap w z).filter (fun d =>
    changed keep tag N cap w z tau d ∧ 0 ≤ (ArithmeticFunction.moebius d : ℝ)),
    1 / (Nat.totient d : ℝ)

def negativeChangedMass (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) : ℝ :=
  ∑ d ∈ (universe N cap w z).filter (fun d =>
    changed keep tag N cap w z tau d ∧ ¬0 ≤ (ArithmeticFunction.moebius d : ℝ)),
    1 / (Nat.totient d : ℝ)

theorem changedMass_eq_positive_add_negative
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) :
    changedMass keep tag N cap w z tau =
      positiveChangedMass keep tag N cap w z tau +
        negativeChangedMass keep tag N cap w z tau := by
  unfold changedMass positiveChangedMass negativeChangedMass
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hc : changed keep tag N cap w z tau d <;>
    by_cases hs : 0 ≤ (ArithmeticFunction.moebius d : ℝ) <;> simp [hc, hs]

/-- The two slopes are exact, including a possibly negative beta-minus
density. An absolute compiler norm cannot replace this signed identity. -/
theorem signAttachedValue_change
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau lo hi : ℝ) {d : ℕ}
    (hd : d ∈ universe N cap w z) :
    signAttachedValue (coefficient keep tag N cap w z tau d) lo hi -
      signAttachedValue (raw keep N cap w z d) lo hi =
        if changed keep tag N cap w z tau d then
          if 0 ≤ (ArithmeticFunction.moebius d : ℝ) then hi else lo
        else 0 := by
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (P2LowerFiniteCellRounding.universe_squarefree N cap w z hd)
  rw [raw_value]
  by_cases hs : 0 ≤ (ArithmeticFunction.moebius d : ℝ)
  · have hm : (ArithmeticFunction.moebius d : ℝ) = 1 := by
      simpa only [abs_of_nonneg hs] using hmu
    by_cases hr : d ∈ rawSupport keep N cap w z
    · have ho := outer_of_raw keep tag N cap w z tau hr
      simp [coefficient, hd, hs, ho, hr, changed, hm, signAttachedValue]
    · by_cases ho : outer keep tag N cap w z tau d <;>
        simp [coefficient, hd, hs, ho, hr, changed, hm, signAttachedValue]
  · have hm : (ArithmeticFunction.moebius d : ℝ) = -1 := by
      rw [abs_of_nonpos (le_of_not_ge hs)] at hmu
      linarith only [hmu]
    by_cases hr : d ∈ rawSupport keep N cap w z
    · by_cases hi' : inner keep tag N cap w z tau d <;>
        simp [coefficient, hd, hs, hi', hr, changed, hm, signAttachedValue]
    · have hi' : ¬inner keep tag N cap w z tau d :=
        fun h => hr (h (self_mem_cell tag N cap w z tau hd))
      simp [coefficient, hd, hs, hi', hr, changed, hm, signAttachedValue]

/-- Exact physical compiler change. Small weights, rough carrier, and
the global compiled rho are precisely the O definitions. -/
theorem physical_compiler_change_eq_signed_changed_masses
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau level : ℝ) :
    physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
        (P4AUpperTaggedBetaAttachment.rho keep tag N cap w z tau level) -
      p4aReservePhysicalDensity keep N cap w z level =
        reciprocalTotientDensity (actualSmallRosserSupport N cap w)
            (actualSmallRosserPlus N cap w level) *
          positiveChangedMass keep tag N cap w z tau +
        reciprocalTotientDensity (actualSmallRosserSupport N cap w)
            (actualSmallRosserMinus N cap w level) *
          negativeChangedMass keep tag N cap w z tau := by
  rw [show p4aReservePhysicalDensity keep N cap w z level =
      physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
        (smallRoughRho (actualSmallRosserSupport N cap w) (universe N cap w z)
          (raw keep N cap w z) (actualSmallRosserMinus N cap w level)
          (actualSmallRosserPlus N cap w level)) from
    (P4AUpperTaggedBetaAttachment.raw_physical_density_on_universe keep N cap w z level).symm]
  unfold P4AUpperTaggedBetaAttachment.support P4AUpperTaggedBetaAttachment.rho
  rw [physicalDensitySum_smallRoughRho_eq_signSensitive
      (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
      (fun _ hm => P2LowerFiniteCellRounding.universe_rough N cap w z hm),
    physicalDensitySum_smallRoughRho_eq_signSensitive
      (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
      (fun _ hm => P2LowerFiniteCellRounding.universe_rough N cap w z hm),
    signSensitiveReciprocalTotientDensity_eq_sum_attached,
    signSensitiveReciprocalTotientDensity_eq_sum_attached,
    ← Finset.sum_sub_distrib]
  unfold positiveChangedMass negativeChangedMass
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← sub_div, signAttachedValue_change keep tag N cap w z tau _ _ hd]
  by_cases hc : changed keep tag N cap w z tau d <;>
    by_cases hs : 0 ≤ (ArithmeticFunction.moebius d : ℝ) <;>
      simp [hc, hs] <;> ring

/-- Finite exact ledger, BEFORE estimates. In particular the continuation
correction has a favorable minus sign for one complete upper policy. -/
theorem compiled_density_eq_full_plus_beta_and_changed_minus_correction
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau level : ℝ) (hwz : w ≤ z) :
    physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
      (P4AUpperTaggedBetaAttachment.rho keep tag N cap w z tau level) =
    p4aReserveRawDensity keep N cap 0 z +
      (p4aReservePhysicalDensity keep N cap w z level -
        actualSmallEulerProduct N cap w * p4aReserveRawDensity keep N cap w z) +
      reciprocalTotientDensity (actualSmallRosserSupport N cap w)
          (actualSmallRosserPlus N cap w level) *
        positiveChangedMass keep tag N cap w z tau +
      reciprocalTotientDensity (actualSmallRosserSupport N cap w)
          (actualSmallRosserMinus N cap w level) *
        negativeChangedMass keep tag N cap w z tau -
      p4aActualPresieveCorrection keep N cap w z := by
  have hp := p4a_fullRaw_eq_euler_presieved_add_correction keep N cap w z hwz
  have hc := physical_compiler_change_eq_signed_changed_masses keep tag N cap w z tau level
  linarith only [hp, hc]

/-- One pre-N beta choice supplies the actual attachment term in the
literal compiler ledger. The two signed changed masses remain unpaid and
visible; no target estimate has been moved into a hypothesis. -/
theorem exists_compiled_density_le_full_and_signed_changed_masses
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
        ∀ (keep : List ℕ → Bool) (tag : ℕ → List Bool) (tau : ℝ),
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (nu * r)
        let level := (N : ℝ) ^ (nu * epsilon)
        physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
          (P4AUpperTaggedBetaAttachment.rho keep tag N cap w z tau level) ≤
        p4aReserveRawDensity keep N cap 0 z +
          eta * (singularSeries N / Real.log (N : ℝ)) +
          reciprocalTotientDensity (actualSmallRosserSupport N cap w)
              (actualSmallRosserPlus N cap w level) *
            positiveChangedMass keep tag N cap w z tau +
          reciprocalTotientDensity (actualSmallRosserSupport N cap w)
              (actualSmallRosserMinus N cap w level) *
            negativeChangedMass keep tag N cap w z tau -
          p4aActualPresieveCorrection keep N cap w z := by
  obtain ⟨epsilon, he, he8, heMax, her, N0, hN0, hbeta⟩ :=
    exists_actualSmallRoughRho_density_error_le_target_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, he, he8, heMax, her, N0, hN0, ?_⟩
  intro N hN hEven cap hcap keep tag tau
  have hN2 : 2 ≤ N := hN0.trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwz : (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (N : ℝ) ^ (nu * r) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (mul_le_mul_of_nonneg_left her hnu.le)
  have hb := (hbeta N hN hEven cap hcap keep).2
  dsimp only at hb ⊢
  change p4aReservePhysicalDensity keep N cap _ _ _ -
      actualSmallEulerProduct N cap _ * p4aReserveRawDensity keep N cap _ _ ≤
    eta * singularSeries N / Real.log (N : ℝ) at hb
  rw [compiled_density_eq_full_plus_beta_and_changed_minus_correction keep tag
    N cap _ _ tau _ hwz]
  have hb' : p4aReservePhysicalDensity keep N cap _ _ _ -
      actualSmallEulerProduct N cap _ * p4aReserveRawDensity keep N cap _ _ ≤
    eta * (singularSeries N / Real.log (N : ℝ)) := by
    simpa only [mul_div_assoc] using hb
  linarith only [hb']

/-- Apply the finite identity to precisely O's held common policy and tag.
The same OriginalData occurs in every raw, compiled and continuation term. -/
theorem common_compiled_density_identity
    (data : P5OriginalCommonRefinedConstructor.OriginalData)
    (N cap : ℕ) (w z tau level : ℝ) (hwz : w ≤ z) :
    physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
      (P4ACommonPolicyTaggedCompiler.compiledRho data N cap w z tau level) =
    p4aReserveRawDensity (P4ACommonPolicyTaggedCompiler.heldRetain data N) N cap 0 z +
      (p4aReservePhysicalDensity (P4ACommonPolicyTaggedCompiler.heldRetain data N) N cap w z level -
        actualSmallEulerProduct N cap w *
          p4aReserveRawDensity (P4ACommonPolicyTaggedCompiler.heldRetain data N) N cap w z) +
      reciprocalTotientDensity (actualSmallRosserSupport N cap w)
          (actualSmallRosserPlus N cap w level) *
        positiveChangedMass (P4ACommonPolicyTaggedCompiler.heldRetain data N)
          (P4ACommonPolicyTaggedCompiler.historicalTag data N) N cap w z tau +
      reciprocalTotientDensity (actualSmallRosserSupport N cap w)
          (actualSmallRosserMinus N cap w level) *
        negativeChangedMass (P4ACommonPolicyTaggedCompiler.heldRetain data N)
          (P4ACommonPolicyTaggedCompiler.historicalTag data N) N cap w z tau -
      p4aActualPresieveCorrection (P4ACommonPolicyTaggedCompiler.heldRetain data N) N cap w z :=
  compiled_density_eq_full_plus_beta_and_changed_minus_correction
    (P4ACommonPolicyTaggedCompiler.heldRetain data N)
    (P4ACommonPolicyTaggedCompiler.historicalTag data N) N cap w z tau level hwz

end
end ImbalancedChen.P4AUpperTaggedContinuationAccounting
