import ImbalancedChen.ActualSmallRoughAttachment
import ImbalancedChen.ActualUpperPolicyFiniteBridge

/-!
SOURCEONLY / UNCOMPILED.
An exact signed-mass ledger for the literal physical attachment. The same
rough coefficient supplies both its signed and absolute masses. There is
no density bound, integral estimate, or K hypothesis in this module.
-/
namespace ImbalancedChen.P4ASameRhoSignedMassLedger

noncomputable section
open scoped BigOperators

def positiveMass (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  reciprocalTotientDensity S (fun d => max (c d) 0)

def negativeMass (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  reciprocalTotientDensity S (fun d => max (-c d) 0)

theorem positiveMass_nonneg (S : Finset ℕ) (c : ℕ → ℝ) :
    0 ≤ positiveMass S c := by
  unfold positiveMass reciprocalTotientDensity
  exact Finset.sum_nonneg (fun d _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg _))

theorem negativeMass_nonneg (S : Finset ℕ) (c : ℕ → ℝ) :
    0 ≤ negativeMass S c := by
  unfold negativeMass reciprocalTotientDensity
  exact Finset.sum_nonneg (fun d _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg _))

theorem signedMass_eq_positive_sub_negative (S : Finset ℕ) (c : ℕ → ℝ) :
    reciprocalTotientDensity S c = positiveMass S c - negativeMass S c := by
  unfold positiveMass negativeMass reciprocalTotientDensity
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hc : 0 ≤ c d
  · simp [max_eq_left hc, max_eq_right (neg_nonpos.mpr hc)]
  · have hn : c d ≤ 0 := (lt_of_not_ge hc).le
    simp [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]

theorem absoluteMass_eq_positive_add_negative (S : Finset ℕ) (c : ℕ → ℝ) :
    reciprocalTotientDensity S (fun d => |c d|) = positiveMass S c + negativeMass S c := by
  unfold positiveMass negativeMass reciprocalTotientDensity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hc : 0 ≤ c d
  · simp [max_eq_left hc, max_eq_right (neg_nonpos.mpr hc), abs_of_nonneg hc]
  · have hn : c d ≤ 0 := (lt_of_not_ge hc).le
    simp [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn), abs_of_nonpos hn]

/-- A positive rough coefficient takes the upper small weight; a negative
coefficient takes the lower one. The sign rule is derived pointwise. -/
theorem signSensitive_eq_positive_sub_negative
    (S : Finset ℕ) (c : ℕ → ℝ) (lo hi : ℝ) :
    signSensitiveReciprocalTotientDensity S c lo hi =
      hi * positiveMass S c - lo * negativeMass S c := by
  unfold signSensitiveReciprocalTotientDensity positiveMass negativeMass reciprocalTotientDensity
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hc : 0 ≤ c d
  · simp [hc, max_eq_left hc, max_eq_right (neg_nonpos.mpr hc), mul_comm]
  · have hn : c d ≤ 0 := (lt_of_not_ge hc).le
    simp [hc, max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)] <;> ring

/-- The midpoint/width form displays the entire absolute-mass charge.
No positivity of the signed rough main term is required. -/
theorem signSensitive_eq_midpoint_signed_add_width_absolute
    (S : Finset ℕ) (c : ℕ → ℝ) (lo hi : ℝ) :
    signSensitiveReciprocalTotientDensity S c lo hi =
      ((hi + lo) / 2) * reciprocalTotientDensity S c +
        ((hi - lo) / 2) * reciprocalTotientDensity S (fun d => |c d|) := by
  rw [signSensitive_eq_positive_sub_negative,
    signedMass_eq_positive_sub_negative, absoluteMass_eq_positive_add_negative]
  ring

/-- Exact error about any proposed Euler density, with both nonnegative
masses belonging to the same signed coefficient. -/
theorem signSensitive_sub_euler_eq
    (S : Finset ℕ) (c : ℕ → ℝ) (V lo hi : ℝ) :
    signSensitiveReciprocalTotientDensity S c lo hi -
        V * reciprocalTotientDensity S c =
      (hi - V) * positiveMass S c + (V - lo) * negativeMass S c := by
  rw [signSensitive_eq_positive_sub_negative, signedMass_eq_positive_sub_negative]
  ring

/-- Subtracting two events reverses the contribution of the second negative
mass. Both events keep their own original rough coefficient throughout. -/
theorem signSensitive_pair_sub_euler_eq
    (SA SB : Finset ℕ) (a b : ℕ → ℝ) (V lo hi : ℝ) :
    (signSensitiveReciprocalTotientDensity SA a lo hi -
        signSensitiveReciprocalTotientDensity SB b lo hi) -
      V * (reciprocalTotientDensity SA a - reciprocalTotientDensity SB b) =
      (hi - V) * (positiveMass SA a - positiveMass SB b) +
        (V - lo) * (negativeMass SA a - negativeMass SB b) := by
  have hA := signSensitive_sub_euler_eq SA a V lo hi
  have hB := signSensitive_sub_euler_eq SB b V lo hi
  calc
    _ = (signSensitiveReciprocalTotientDensity SA a lo hi -
          V * reciprocalTotientDensity SA a) -
        (signSensitiveReciprocalTotientDensity SB b lo hi -
          V * reciprocalTotientDensity SB b) := by ring
    _ = _ := by rw [hA, hB]; ring

/-- This exact identity is instantiated at the literal actualSmallRoughRho,
not at a newly chosen coefficient with the same density. -/
theorem actual_attachment_density_eq_midpoint_signed_add_width_absolute
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    let small := actualSmallRosserSupport N cap w
    let rough := fixedRoughSupport retainOdd N cap w z
    let c := fixedRoughCoefficient retainOdd N cap w z
    let lo := reciprocalTotientDensity small (actualSmallRosserMinus N cap w L)
    let hi := reciprocalTotientDensity small (actualSmallRosserPlus N cap w L)
    physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) =
      ((hi + lo) / 2) * reciprocalTotientDensity rough c +
        ((hi - lo) / 2) * reciprocalTotientDensity rough (fun d => |c d|) := by
  dsimp only
  unfold actualSmallRoughModuli actualSmallRoughRho
  rw [physicalDensitySum_smallRoughRho_eq_signSensitive
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hd)]
  exact signSensitive_eq_midpoint_signed_add_width_absolute _ _ _ _

/-- Paired physical events use the same small Rosser weights and cutoff.
Within each event its signed and absolute densities are computed from the
very coefficient that defines its physical rho. The second absolute mass
is subtracted; no comparison of the two absolute masses is implicit. -/
theorem actual_pair_attachment_density_eq_midpoint_ledger
    (old new : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    let small := actualSmallRosserSupport N cap w
    let oldRough := fixedRoughSupport old N cap w z
    let newRough := fixedRoughSupport new N cap w z
    let oldCoeff := fixedRoughCoefficient old N cap w z
    let newCoeff := fixedRoughCoefficient new N cap w z
    let lo := reciprocalTotientDensity small (actualSmallRosserMinus N cap w L)
    let hi := reciprocalTotientDensity small (actualSmallRosserPlus N cap w L)
    physicalDensitySum (actualSmallRoughModuli old N cap w z)
        (actualSmallRoughRho old N cap w z L) -
      physicalDensitySum (actualSmallRoughModuli new N cap w z)
        (actualSmallRoughRho new N cap w z L) =
      ((hi + lo) / 2) *
        (reciprocalTotientDensity oldRough oldCoeff -
          reciprocalTotientDensity newRough newCoeff) +
      ((hi - lo) / 2) *
        (reciprocalTotientDensity oldRough (fun d => |oldCoeff d|) -
          reciprocalTotientDensity newRough (fun d => |newCoeff d|)) := by
  dsimp only
  rw [actual_attachment_density_eq_midpoint_signed_add_width_absolute,
    actual_attachment_density_eq_midpoint_signed_add_width_absolute]
  ring

/-- The paired error relative to one proposed small Euler density. In the
old-minus-new difference, the new event's negative mass has the opposite
sign. Each side is still the density of its literal physical rho. -/
theorem actual_pair_attachment_sub_euler_eq
    (old new : List ℕ → Bool) (N cap : ℕ) (w z L V : ℝ) :
    let small := actualSmallRosserSupport N cap w
    let oldRough := fixedRoughSupport old N cap w z
    let newRough := fixedRoughSupport new N cap w z
    let oldCoeff := fixedRoughCoefficient old N cap w z
    let newCoeff := fixedRoughCoefficient new N cap w z
    let lo := reciprocalTotientDensity small (actualSmallRosserMinus N cap w L)
    let hi := reciprocalTotientDensity small (actualSmallRosserPlus N cap w L)
    (physicalDensitySum (actualSmallRoughModuli old N cap w z)
        (actualSmallRoughRho old N cap w z L) -
      physicalDensitySum (actualSmallRoughModuli new N cap w z)
        (actualSmallRoughRho new N cap w z L)) -
      V * (reciprocalTotientDensity oldRough oldCoeff -
        reciprocalTotientDensity newRough newCoeff) =
      (hi - V) * (positiveMass oldRough oldCoeff -
        positiveMass newRough newCoeff) +
      (V - lo) * (negativeMass oldRough oldCoeff -
        negativeMass newRough newCoeff) := by
  dsimp only
  unfold actualSmallRoughModuli actualSmallRoughRho
  rw [physicalDensitySum_smallRoughRho_eq_signSensitive
      (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
      (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt old N cap w z hd),
    physicalDensitySum_smallRoughRho_eq_signSensitive
      (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
      (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt new N cap w z hd)]
  exact signSensitive_pair_sub_euler_eq _ _ _ _ _ _ _

/-- The signed mass in the same physical attachment is exactly the
retained first-exit polynomial of the original even-retaining policy.
The width term retains its literal absolute coefficient mass. -/
theorem even_policy_attachment_density_eq_firstExit_midpoint_ledger
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z L : ℝ) :
    let small := actualSmallRosserSupport N cap w
    let rough := fixedRoughSupport (retained false) N cap w z
    let c := fixedRoughCoefficient (retained false) N cap w z
    let lo := reciprocalTotientDensity small (actualSmallRosserMinus N cap w L)
    let hi := reciprocalTotientDensity small (actualSmallRosserPlus N cap w L)
    physicalDensitySum (actualSmallRoughModuli (retained false) N cap w z)
        (actualSmallRoughRho (retained false) N cap w z L) =
      ((hi + lo) / 2) *
        firstExitRetainedPolynomial retained (fun p : ℕ => 1 / ((p : ℝ) - 1))
          [] true 1 (roughPrimeUniverse N cap w z) +
      ((hi - lo) / 2) * reciprocalTotientDensity rough (fun d => |c d|) := by
  dsimp only
  rw [actual_attachment_density_eq_midpoint_signed_add_width_absolute]
  rw [UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    retained heven N cap w z]

end
end ImbalancedChen.P4ASameRhoSignedMassLedger
