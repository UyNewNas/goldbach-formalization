import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.ActualUpperPolicyDensity

/-!
# P4B: paying a source-mass centre change on the original normalization

YELLOW / SOURCE-ONLY / UNCOMPILED. Companion to P4BCentreIdentity and
P4BActualOuterUpperAssembly; this draft imports production modules only.

The actual physical density has signed coefficients. Its nonnegativity is
proved below from the existing rough-density theorem and the nonnegative
small-weight attachment error. The resulting threshold is uniform in the
retention policy and enumeration cap. This uses 0 < epsilon < 1/8 and the
existing proved small-density supplier; no K bound or final upper-count
estimate is assumed to obtain nonnegativity.

Only after supplying that sign do we use a one-sided density cap to bound
the absolute source-centre shift. A separate two-sided scalar lemma makes
the alternative sign requirement explicit. Every normalization is the
original singularNormalization, with its exact source/density scale product.
-/

namespace ImbalancedChen.P4BSourceCentreScale

noncomputable section

open Filter Topology
open scoped BigOperators

/-- This finite Euler product is nonnegative on every actual prime carrier;
no claim that its individual signed divisor coefficients are nonnegative. -/
theorem actualSmallEulerProduct_nonneg (N cap : ℕ) (w : ℝ) :
    0 ≤ actualSmallEulerProduct N cap w := by
  unfold actualSmallEulerProduct
  apply Finset.prod_nonneg
  intro p hp
  exact sub_nonneg.mpr
    (reciprocalTotientPrimeWeight_mem_Icc (actualSmallPrimeFinset_prime N cap w p hp)).2

/-- Complete uniform sign supplier for the physical small/rough density.
The analytic threshold comes from the proved fundamental-lemma attachment
supplier, and is chosen before target, cap, policy and rough upper cutoff. -/
theorem exists_actualSmallRough_density_nonneg_threshold
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8) :
    ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ∀ N cap : ℕ, Even N → ∀ retainOdd : List ℕ → Bool, ∀ z : ℝ,
        0 ≤ physicalDensitySum
          (actualSmallRoughModuli retainOdd N cap (D ^ (epsilon ^ 2)) z)
          (actualSmallRoughRho retainOdd N cap (D ^ (epsilon ^ 2)) z (D ^ epsilon)) := by
  obtain ⟨C, K, hC, hK, hsupply⟩ := exists_actualSmallRoughRho_density_error
  obtain ⟨D₀, hD₀, hsupply⟩ := hsupply epsilon hepsilon hepsilon8
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD N cap hEven retainOdd z
  have herror := hsupply D hD N cap hEven retainOdd z
  dsimp only at herror
  have hbase : 0 ≤ actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
      reciprocalTotientDensity
        (fixedRoughSupport retainOdd N cap (D ^ (epsilon ^ 2)) z)
        (fixedRoughCoefficient retainOdd N cap (D ^ (epsilon ^ 2)) z) :=
    mul_nonneg (actualSmallEulerProduct_nonneg N cap _)
      (fixedRoughDensity_nonneg retainOdd N cap _ z)
  exact hbase.trans (sub_nonneg.mp herror.1)

/-- At D=N^nu the sign supplier applies to the literal attached coefficient
used in the outer assembly. No covering-cap or sharp-density premise occurs. -/
theorem eventually_attachedUpper_density_nonneg
    {nu epsilon : ℝ} (hnu : 0 < nu) (hepsilon : 0 < epsilon)
    (hepsilon8 : epsilon < 1 / 8) (r : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      0 ≤ physicalDensitySum (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) := by
  obtain ⟨D₀, hD₀, hsupply⟩ :=
    exists_actualSmallRough_density_nonneg_threshold epsilon hepsilon hepsilon8
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpower.eventually (eventually_ge_atTop D₀)] with N hN
  intro hEven
  have h := hsupply ((N : ℝ) ^ nu) hN N (cap N) hEven
    (retain N) ((N : ℝ) ^ (nu * r))
  simpa only [attachedUpperModuli, attachedUpperCoefficient,
    ← Real.rpow_mul (Nat.cast_nonneg N)] using h

/-- A legal positive outer source has nonnegative actual mass surplus. -/
theorem realSource_mass_le_outer_mass
    (b : ℝ) (N : ℕ) (T : ℝ) (S : Finset ℕ) (weight : ℕ → ℝ)
    (hsource : realHalfProductSource b N T ⊆ S)
    (houter : ∀ m ∈ S,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m) :
    ((realHalfProductSource b N T).card : ℝ) ≤ finiteSourceMass S weight := by
  classical
  have hsum : (∑ m ∈ realHalfProductSource b N T, (1 : ℝ)) ≤
      ∑ m ∈ S, weight m := by
    calc
      _ = ∑ m ∈ realHalfProductSource b N T,
          if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        simp only [if_pos hm]
      _ = ∑ m ∈ S,
          if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0 := by
        apply Finset.sum_subset hsource
        intro m hmS hmSource
        simp only [if_neg hmSource]
      _ ≤ _ := Finset.sum_le_sum houter
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, finiteSourceMass] using hsum

/-- Sign-safe payment of the absolute mass-centre shift. The single-sided
density cap is used only together with the separately supplied density sign. -/
theorem abs_surplus_mul_density_le_original_normalization
    {N : ℕ} (hN : 2 ≤ N) {surplus density delta K : ℝ}
    (hdelta : 0 ≤ delta) (hK : 0 ≤ K)
    (hsurplus0 : 0 ≤ surplus)
    (hsurplus : surplus ≤ delta * ((N : ℝ) / Real.log (N : ℝ)))
    (hdensity0 : 0 ≤ density)
    (hdensity : density ≤ (K + delta) * (singularSeries N / Real.log (N : ℝ))) :
    |surplus * density| ≤ delta * (K + delta) * singularNormalization N := by
  calc
    |surplus * density| = surplus * density :=
      abs_of_nonneg (mul_nonneg hsurplus0 hdensity0)
    _ ≤ surplus * ((K + delta) * (singularSeries N / Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hdensity hsurplus0
    _ ≤ (delta * ((N : ℝ) / Real.log (N : ℝ))) *
        ((K + delta) * (singularSeries N / Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_right hsurplus
        (mul_nonneg (add_nonneg hK hdelta) (densityScale_pos hN).le)
    _ = delta * (K + delta) * singularNormalization N := by
      rw [← sourceMassScale_mul_densityScale N]
      ring

/-- The alternative route requires a genuine two-sided density estimate,
and an absolute surplus estimate. An upper density cap alone is insufficient. -/
theorem abs_surplus_mul_density_le_of_two_sided
    {N : ℕ} (hN : 2 ≤ N) {surplus density delta K : ℝ}
    (hdelta : 0 ≤ delta)
    (hsurplus : |surplus| ≤ delta * ((N : ℝ) / Real.log (N : ℝ)))
    (hdensity : -((K + delta) * (singularSeries N / Real.log (N : ℝ))) ≤ density ∧
      density ≤ (K + delta) * (singularSeries N / Real.log (N : ℝ))) :
    |surplus * density| ≤ delta * (K + delta) * singularNormalization N := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hmassScale : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    (div_pos (lt_trans zero_lt_one hN1) (Real.log_pos hN1)).le
  calc
    |surplus * density| = |surplus| * |density| := abs_mul _ _
    _ ≤ (delta * ((N : ℝ) / Real.log (N : ℝ))) *
        ((K + delta) * (singularSeries N / Real.log (N : ℝ))) :=
      mul_le_mul hsurplus (abs_le.mpr hdensity) (abs_nonneg _)
        (mul_nonneg hdelta hmassScale)
    _ = delta * (K + delta) * singularNormalization N := by
      rw [← sourceMassScale_mul_densityScale N]
      ring

/-- One actual outer-source progression sum, centred at a freely chosen
source mass and at the density of the identical physical coefficient. -/
def outerErrorAtSourceMass
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ) (referenceMass : ℝ) : ℝ :=
  (∑ d ∈ Q, rho d * finiteCongruenceMass S weight N d) -
    referenceMass * physicalDensitySum Q rho

/-- With its own mass as centre, the exact outer error is the coprime
correction plus the signed primitive error used by the outer assembly. -/
theorem outerErrorAtSourceMass_eq_coprime_add_primitive
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ) :
    outerErrorAtSourceMass N S Q weight rho (finiteSourceMass S weight) =
      (∑ d ∈ Q, rho d *
        ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
          (Nat.totient d : ℝ))) +
      ∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d := by
  unfold outerErrorAtSourceMass physicalDensitySum finitePrimitiveDiscrepancy
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The signed mass-centre identity is established before absolute values. -/
theorem outerErrorAtSourceMass_change
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (originalMass outerMass : ℝ) :
    outerErrorAtSourceMass N S Q weight rho originalMass =
      outerErrorAtSourceMass N S Q weight rho outerMass +
        (outerMass - originalMass) * physicalDensitySum Q rho := by
  unfold outerErrorAtSourceMass
  ring

/-- The original-source centre retains the exact mass shift as a third
signed term. This is an identity, independent of distribution estimates. -/
theorem outerErrorAtSourceMass_eq_coprime_add_primitive_add_shift
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ) (originalMass : ℝ) :
    outerErrorAtSourceMass N S Q weight rho originalMass =
      (∑ d ∈ Q, rho d *
        ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
          (Nat.totient d : ℝ))) +
      (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d) +
      (finiteSourceMass S weight - originalMass) * physicalDensitySum Q rho := by
  rw [outerErrorAtSourceMass_change N S Q weight rho originalMass
    (finiteSourceMass S weight), outerErrorAtSourceMass_eq_coprime_add_primitive]

/-- The complete source-centre transport bound. All density and progression
expressions use this one Q and rho, with the original source card retained. -/
theorem abs_outerError_at_original_mass_le
    {b T : ℝ} {N : ℕ} (hN : 2 ≤ N) (S Q : Finset ℕ)
    (weight rho : ℕ → ℝ) {delta K : ℝ} (hdelta : 0 ≤ delta) (hK : 0 ≤ K)
    (hsource : realHalfProductSource b N T ⊆ S)
    (houter : ∀ m ∈ S,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m)
    (hsurplus : finiteSourceMass S weight ≤
      ((realHalfProductSource b N T).card : ℝ) +
        delta * ((N : ℝ) / Real.log (N : ℝ)))
    (hdensity0 : 0 ≤ physicalDensitySum Q rho)
    (hdensity : physicalDensitySum Q rho ≤
      (K + delta) * (singularSeries N / Real.log (N : ℝ))) :
    |outerErrorAtSourceMass N S Q weight rho
      ((realHalfProductSource b N T).card : ℝ)| ≤
      |outerErrorAtSourceMass N S Q weight rho (finiteSourceMass S weight)| +
        delta * (K + delta) * singularNormalization N := by
  have hsurplus0 := sub_nonneg.mpr
    (realSource_mass_le_outer_mass b N T S weight hsource houter)
  have hshift := abs_surplus_mul_density_le_original_normalization hN hdelta hK
    hsurplus0 (sub_le_iff_le_add.mpr (by linarith only [hsurplus])) hdensity0 hdensity
  rw [outerErrorAtSourceMass_change N S Q weight rho _ (finiteSourceMass S weight)]
  exact (abs_add_le _ _).trans (add_le_add_left hshift _)

/-- A common eventual threshold combines the proved actual-density sign
with the independent P4A density cap and the geometric outer mass surplus.
The conclusion pays precisely the centre shift on the original norm. -/
theorem eventually_actual_outer_centre_shift_le
    {b kappa nu r epsilon delta K : ℝ}
    (hnu : 0 < nu) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (hdelta : 0 ≤ delta) (hK : 0 ≤ K)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (S : ℕ → Finset ℕ) (weight : ℕ → ℕ → ℝ)
    (hgeometry : ∀ᶠ N : ℕ in atTop, Even N →
      realHalfProductSource b N (manuscriptHalfProductCutoff kappa N) ⊆ S N ∧
      (∀ m ∈ S N,
        (if m ∈ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)
          then (1 : ℝ) else 0) ≤ weight N m))
    (hsurplus : ∀ᶠ N : ℕ in atTop, Even N →
      finiteSourceMass (S N) (weight N) ≤
        ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
          delta * ((N : ℝ) / Real.log (N : ℝ)))
    (hdensity : ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) ≤
          (K + delta) * (singularSeries N / Real.log (N : ℝ))) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |(finiteSourceMass (S N) (weight N) -
          ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ)) *
        physicalDensitySum (attachedUpperModuli nu r epsilon retain cap N)
          (attachedUpperCoefficient nu r epsilon retain cap N)| ≤
        delta * (K + delta) * singularNormalization N := by
  filter_upwards [eventually_attachedUpper_density_nonneg hnu hepsilon hepsilon8
    r retain cap, hgeometry, hsurplus, hdensity, eventually_ge_atTop (2 : ℕ)]
      with N hdensity0N hgeometryN hsurplusN hdensityN hN
  intro hEven
  obtain ⟨hsource, houter⟩ := hgeometryN hEven
  apply abs_surplus_mul_density_le_original_normalization hN hdelta hK
  · exact sub_nonneg.mpr (realSource_mass_le_outer_mass b N _ (S N) (weight N)
      hsource houter)
  · have h := hsurplusN hEven
    linarith only [h]
  · exact hdensity0N hEven
  · exact hdensityN hEven

end

end ImbalancedChen.P4BSourceCentreScale
