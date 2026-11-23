import ImbalancedChen.FixedRoughCoefficients
import ImbalancedChen.UpperCoefficientPerturbation
import Mathlib.Data.Finset.SymmDiff

/-!
SOURCEONLY / UNCOMPILED. Two actual retained policies at the identical
N, cap, w, z have the identical Möbius coefficient wherever both retain
the same modulus. Squarefreeness of each actual retained support makes
the absolute coefficient difference exactly the indicator of their
symmetric difference. Thus the literal compiler mass on the union is
the reciprocal-totient unit mass of changed retained moduli.
No estimate for that mass, compiler reserve or target bound is assumed.
-/

namespace ImbalancedChen.P4ARetainedSupportDifferenceMass

noncomputable section
open scoped BigOperators symmDiff

/-- The actual fixed coefficient is Möbius precisely on its retained support. -/
theorem coefficient_eq_moebius_indicator
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    fixedRoughCoefficient retainOdd N cap w z d =
      if d ∈ fixedRoughSupport retainOdd N cap w z then
        (ArithmeticFunction.moebius d : ℝ) else 0 := by
  classical
  unfold fixedRoughCoefficient oddFirstExitRetainedCoefficient
  change ((if d ∈ fixedRoughSupport retainOdd N cap w z then
    ArithmeticFunction.moebius d else 0 : ℤ) : ℝ) = _
  split_ifs <;> simp

/-- A retained modulus is squarefree, so its literal signed coefficient
has absolute value one. This is a theorem about the actual support. -/
theorem coefficient_abs_eq_one_of_mem
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd N cap w z) :
    |fixedRoughCoefficient retainOdd N cap w z d| = 1 := by
  rw [coefficient_eq_moebius_indicator, if_pos hd]
  exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
    (fixedRoughSupport_squarefree retainOdd N cap w z hd)

/-- Common retained moduli have exactly equal coefficients, including sign. -/
theorem coefficient_sub_eq_zero_on_intersection
    (retainOdd₁ retainOdd₂ : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd₁ N cap w z ∩
      fixedRoughSupport retainOdd₂ N cap w z) :
    fixedRoughCoefficient retainOdd₁ N cap w z d -
      fixedRoughCoefficient retainOdd₂ N cap w z d = 0 := by
  obtain ⟨h₁, h₂⟩ := Finset.mem_inter.mp hd
  simp only [coefficient_eq_moebius_indicator, if_pos h₁, if_pos h₂, sub_self]

/-- The compiler coefficient charge is exactly one on changed membership
and zero on common or absent moduli. No coefficient-error premise is used. -/
theorem abs_coefficient_sub_eq_symmDiff_indicator
    (retainOdd₁ retainOdd₂ : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    |fixedRoughCoefficient retainOdd₁ N cap w z d -
      fixedRoughCoefficient retainOdd₂ N cap w z d| =
        if d ∈ fixedRoughSupport retainOdd₁ N cap w z ∆
          fixedRoughSupport retainOdd₂ N cap w z then (1 : ℝ) else 0 := by
  classical
  by_cases h₁ : d ∈ fixedRoughSupport retainOdd₁ N cap w z <;>
    by_cases h₂ : d ∈ fixedRoughSupport retainOdd₂ N cap w z
  · simp [coefficient_eq_moebius_indicator, h₁, h₂, Finset.mem_symmDiff]
  · have hmu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (fixedRoughSupport_squarefree retainOdd₁ N cap w z h₁)
    simp [coefficient_eq_moebius_indicator, h₁, h₂, Finset.mem_symmDiff, hmu]
  · have hmu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (fixedRoughSupport_squarefree retainOdd₂ N cap w z h₂)
    simp [coefficient_eq_moebius_indicator, h₁, h₂, Finset.mem_symmDiff, hmu]
  · simp [coefficient_eq_moebius_indicator, h₁, h₂, Finset.mem_symmDiff]

/-- The literal compiler mass on the union carrier equals the exact unit
reciprocal-totient mass of the two retained supports' symmetric difference.
The shared support contributes zero before any majorization is performed. -/
theorem compilerMass_union_eq_symmDiff_unitMass
    (retainOdd₁ retainOdd₂ : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    reciprocalTotientDensity
      (fixedRoughSupport retainOdd₁ N cap w z ∪ fixedRoughSupport retainOdd₂ N cap w z)
      (fun d => |fixedRoughCoefficient retainOdd₁ N cap w z d -
        fixedRoughCoefficient retainOdd₂ N cap w z d|) =
      reciprocalTotientDensity
        (fixedRoughSupport retainOdd₁ N cap w z ∆ fixedRoughSupport retainOdd₂ N cap w z)
        (fun _ => 1) := by
  classical
  unfold reciprocalTotientDensity
  calc
    _ = ∑ d ∈ fixedRoughSupport retainOdd₁ N cap w z ∆
        fixedRoughSupport retainOdd₂ N cap w z,
        |fixedRoughCoefficient retainOdd₁ N cap w z d -
          fixedRoughCoefficient retainOdd₂ N cap w z d| / (Nat.totient d : ℝ) := by
      symm
      apply Finset.sum_subset Finset.symmDiff_subset_union
      intro d _hd hdnot
      rw [abs_coefficient_sub_eq_symmDiff_indicator, if_neg hdnot, zero_div]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [abs_coefficient_sub_eq_symmDiff_indicator, if_pos hd]

/-- A larger common carrier gives the same charge, since both coefficients
vanish off the union. This allows literal reuse in a compiler carrier. -/
theorem compilerMass_commonCarrier_eq_symmDiff_unitMass
    (retainOdd₁ retainOdd₂ : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (rough : Finset ℕ)
    (hrough : fixedRoughSupport retainOdd₁ N cap w z ∪
      fixedRoughSupport retainOdd₂ N cap w z ⊆ rough) :
    reciprocalTotientDensity rough
      (fun d => |fixedRoughCoefficient retainOdd₁ N cap w z d -
        fixedRoughCoefficient retainOdd₂ N cap w z d|) =
      reciprocalTotientDensity
        (fixedRoughSupport retainOdd₁ N cap w z ∆ fixedRoughSupport retainOdd₂ N cap w z)
        (fun _ => 1) := by
  classical
  rw [← compilerMass_union_eq_symmDiff_unitMass retainOdd₁ retainOdd₂ N cap w z]
  unfold reciprocalTotientDensity
  symm
  apply Finset.sum_subset hrough
  intro d _hd hdnot
  have hnot : d ∉ fixedRoughSupport retainOdd₁ N cap w z ∆
      fixedRoughSupport retainOdd₂ N cap w z := by
    intro hd
    exact hdnot (Finset.symmDiff_subset_union hd)
  rw [abs_coefficient_sub_eq_symmDiff_indicator, if_neg hnot, zero_div]

/-- The existing sign-attached compiler transport now charges exactly the
changed retained moduli. No signed cancellation is used to pay the error. -/
theorem abs_signAttached_density_sub_le_symmDiff_unitMass
    (retainOdd₁ retainOdd₂ : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    {lo hi M : ℝ} (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |signSensitiveReciprocalTotientDensity
        (fixedRoughSupport retainOdd₁ N cap w z ∪ fixedRoughSupport retainOdd₂ N cap w z)
        (fixedRoughCoefficient retainOdd₁ N cap w z) lo hi -
      signSensitiveReciprocalTotientDensity
        (fixedRoughSupport retainOdd₁ N cap w z ∪ fixedRoughSupport retainOdd₂ N cap w z)
        (fixedRoughCoefficient retainOdd₂ N cap w z) lo hi| ≤
      M * reciprocalTotientDensity
        (fixedRoughSupport retainOdd₁ N cap w z ∆ fixedRoughSupport retainOdd₂ N cap w z)
        (fun _ => 1) := by
  have h := abs_signSensitiveReciprocalTotientDensity_sub_le
    (fixedRoughSupport retainOdd₁ N cap w z ∪ fixedRoughSupport retainOdd₂ N cap w z)
    (fixedRoughCoefficient retainOdd₁ N cap w z)
    (fixedRoughCoefficient retainOdd₂ N cap w z) hlo hhi
  rwa [compilerMass_union_eq_symmDiff_unitMass] at h

/-- The same localization after literal attachment of the actual small
Rosser weights. The two small-density slope bounds remain explicit; the
rough mass is the exact changed-modulus mass, with no mass bound assumed. -/
theorem abs_actualAttached_density_sub_le_symmDiff_unitMass
    (retainOdd₁ retainOdd₂ : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    {M : ℝ}
    (hminus : |reciprocalTotientDensity (actualSmallRosserSupport N cap w)
      (actualSmallRosserMinus N cap w L)| ≤ M)
    (hplus : |reciprocalTotientDensity (actualSmallRosserSupport N cap w)
      (actualSmallRosserPlus N cap w L)| ≤ M) :
    let rough := fixedRoughSupport retainOdd₁ N cap w z ∪
      fixedRoughSupport retainOdd₂ N cap w z
    let small := actualSmallRosserSupport N cap w
    |physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough (fixedRoughCoefficient retainOdd₁ N cap w z)
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)) -
      physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough (fixedRoughCoefficient retainOdd₂ N cap w z)
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L))| ≤
      M * reciprocalTotientDensity
        (fixedRoughSupport retainOdd₁ N cap w z ∆ fixedRoughSupport retainOdd₂ N cap w z)
        (fun _ => 1) := by
  dsimp only
  have hrough : ∀ d ∈ fixedRoughSupport retainOdd₁ N cap w z ∪
      fixedRoughSupport retainOdd₂ N cap w z, RoughPrimeSupportedAt w d := by
    intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact fixedRoughSupport_roughPrimeSupportedAt retainOdd₁ N cap w z hd
    · exact fixedRoughSupport_roughPrimeSupportedAt retainOdd₂ N cap w z hd
  have h := abs_physicalDensitySum_smallRoughRho_sub_le
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    hrough (fixedRoughCoefficient retainOdd₁ N cap w z)
    (fixedRoughCoefficient retainOdd₂ N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) hminus hplus
  rwa [compilerMass_union_eq_symmDiff_unitMass] at h

end
end ImbalancedChen.P4ARetainedSupportDifferenceMass
