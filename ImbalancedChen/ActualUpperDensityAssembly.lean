import ImbalancedChen.ActualFirstExitDensityProjection
import ImbalancedChen.UpperCoefficientPerturbation
import ImbalancedChen.CurrentNumericalTransfer

/-!
# Exact manuscript normalization and the upper-density assembly interface

The source mass is normalized by `N / log N`; the physical density is
normalized by `C_N / log N`.  Their product is exactly the manuscript's
`singularNormalization N`, with no factor two or ordering factorial.

The limit-to-density theorem below is conditional on an actual full-policy
integral limit and its certified upper bound.  It is not a proof that the
manuscript's historical policy or its boxed compiler meets those inputs.
The attachment precision is selected after an admissible precision interval
has been given, and before the common target threshold.  A separate finite
compiler theorem uses the literal absolute rough-coefficient difference.
Neither theorem depends on a lower Chen bound.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- Exact source/density scale conversion, including Lean's total division
conventions at the two small exceptional natural arguments. -/
theorem sourceMassScale_mul_densityScale (N : ℕ) :
    ((N : ℝ) / Real.log (N : ℝ)) *
        (singularSeries N / Real.log (N : ℝ)) = singularNormalization N := by
  simp only [singularNormalization, div_eq_mul_inv, inv_pow]
  ring

theorem densityScale_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < singularSeries N / Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  exact div_pos (singularSeries_pos N) (Real.log_pos hN1)

/-- The exact equivalence used at the handoff to the manuscript scale. -/
theorem density_le_manuscriptScale_iff_normalized {N : ℕ}
    (hN : 2 ≤ N) (density coefficient : ℝ) :
    density ≤ coefficient * (singularSeries N / Real.log (N : ℝ)) ↔
      density * Real.log (N : ℝ) / singularSeries N ≤ coefficient := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  rw [← mul_div_assoc, le_div_iff₀ (Real.log_pos hN1),
    div_le_iff₀ (singularSeries_pos N)]

/-- Exact normalized main-term identity for arbitrary source mass and the
displayed physical weight.  It is valid without a sign assumption on rho. -/
theorem same_rho_normalized_mainTerm (N : ℕ) (mass : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (mass * physicalDensitySum Q rho) / singularNormalization N =
      (mass * Real.log (N : ℝ) / (N : ℝ)) *
        (physicalDensitySum Q rho * Real.log (N : ℝ) / singularSeries N) := by
  simp only [singularNormalization, div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow]
  ring

/-- An actual full-policy integral bound with strict slack produces a
single admissible attachment precision and a common eventual K bound for
the same attached coefficient.  `sieveR` is an internal sieve exponent;
it is unrelated to the real imbalance parameter of `RealB`.

The universal small-precision input is essential when the policy depends
on that precision.  A bound at an unrelated, separately chosen precision
does not supply this theorem's hypothesis.  This handles raw attachment;
the manuscript's outer compiler still needs its own transport and budget. -/
theorem exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits
    (nu sieveR epsilonMax rawBound : ℝ)
    (hnu : 0 < nu) (hr : 0 < sieveR) (hepsilonMax : 0 < epsilonMax)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (integral : ℝ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * sieveR) ≤ (cap N : ℝ))
    (hIntegral : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR)))
          (fixedRoughCoefficient (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR))) *
          Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
        (𝓝 (integral epsilon)))
    (hCertificate : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      integral epsilon ≤ rawBound)
    (hgap : rawBound < currentK) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ sieveR ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (nu * sieveR)
        let L := (N : ℝ) ^ (nu * epsilon)
        physicalDensitySum (actualSmallRoughModuli (retainOdd epsilon N) N (cap N) w z)
            (actualSmallRoughRho (retainOdd epsilon N) N (cap N) w z L) ≤
          currentK * (singularSeries N / Real.log (N : ℝ)) := by
  let eta : ℝ := (currentK - rawBound) / 3
  have heta : 0 < eta := by dsimp [eta]; linarith
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonR,
      Nattach, hNattach, hAttach⟩ :=
    exists_actualSmallRoughRho_density_le_full_reserve nu sieveR eta epsilonMax
      hnu hr heta hepsilonMax
  have hRaw := (hIntegral epsilon hepsilon hepsilonMax').eventually
    (gt_mem_nhds (show integral epsilon < rawBound + eta by
      have hc := hCertificate epsilon hepsilon hepsilonMax'
      linarith))
  rw [Filter.eventually_inf_principal] at hRaw hcap
  obtain ⟨Nraw, hNraw⟩ := eventually_atTop.mp (hRaw.and hcap)
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonR,
    max Nattach Nraw, hNattach.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNa : Nattach ≤ N := (le_max_left _ _).trans hN
  have hNr : Nraw ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNattach.trans hNa
  have hEvenPos : 0 < N ∧ Even N := ⟨by omega, hEven⟩
  have hRN := (hNraw N hNr).1 hEvenPos
  have hCN := (hNraw N hNr).2 hEvenPos
  have hAN := hAttach N hNa hEven (cap N) hCN (retainOdd epsilon N)
  have hFull := (density_le_manuscriptScale_iff_normalized hN2
    (reciprocalTotientDensity
      (fixedRoughSupport (retainOdd epsilon N) N (cap N) 0 ((N : ℝ) ^ (nu * sieveR)))
      (fixedRoughCoefficient (retainOdd epsilon N) N (cap N) 0 ((N : ℝ) ^ (nu * sieveR))))
    (rawBound + eta)).mpr hRN.le
  have hcoeff : rawBound + 2 * eta ≤ currentK := by dsimp [eta]; linarith
  have hscale := (densityScale_pos hN2).le
  dsimp only at hAN ⊢
  calc
    physicalDensitySum
        (actualSmallRoughModuli (retainOdd epsilon N) N (cap N)
          ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * sieveR)))
        (actualSmallRoughRho (retainOdd epsilon N) N (cap N)
          ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * sieveR))
          ((N : ℝ) ^ (nu * epsilon))) ≤
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd epsilon N) N (cap N) 0 ((N : ℝ) ^ (nu * sieveR)))
          (fixedRoughCoefficient (retainOdd epsilon N) N (cap N) 0 ((N : ℝ) ^ (nu * sieveR))) +
          eta * singularSeries N / Real.log (N : ℝ) := hAN
    _ ≤ (rawBound + eta) * (singularSeries N / Real.log (N : ℝ)) +
        eta * singularSeries N / Real.log (N : ℝ) := add_le_add_right hFull _
    _ = (rawBound + 2 * eta) * (singularSeries N / Real.log (N : ℝ)) := by ring
    _ ≤ currentK * (singularSeries N / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff hscale

/-- The finite compiler reserve is charged to the literal reciprocal-
totient absolute coefficient difference, after attaching the same small
weights.  Thus this cannot combine a raw density with a different final
physical coefficient without paying for the change. -/
theorem compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget
    {N : ℕ} (hN : 2 ≤ N) {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ) (M rawBound compilerReserve : ℝ)
    (hminus : |reciprocalTotientDensity small betaMinus| ≤ M)
    (hplus : |reciprocalTotientDensity small betaPlus| ≤ M)
    (hraw : physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough raw betaMinus betaPlus) ≤
      rawBound * (singularSeries N / Real.log (N : ℝ)))
    (hcompiler : M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|) ≤
      compilerReserve * (singularSeries N / Real.log (N : ℝ)))
    (hbudget : rawBound + compilerReserve ≤ currentK) :
    physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough compiled betaMinus betaPlus) *
        Real.log (N : ℝ) / singularSeries N ≤ currentK := by
  apply (density_le_manuscriptScale_iff_normalized hN _ _).mp
  have herror := (abs_physicalDensitySum_smallRoughRho_sub_le hsmall hrough
    compiled raw betaMinus betaPlus hminus hplus).trans hcompiler
  have hupper := (le_abs_self
    (physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough compiled betaMinus betaPlus) -
      physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough raw betaMinus betaPlus))).trans herror
  have hcoeff := mul_le_mul_of_nonneg_right hbudget (densityScale_pos hN).le
  nlinarith

end

end ImbalancedChen
