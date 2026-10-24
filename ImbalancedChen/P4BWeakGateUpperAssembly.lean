import ImbalancedChen.P4BCutoffRounding

/-!
# Conditional actual upper assembly at the weak roughness wall

SOURCE ONLY / YELLOW / UNCOMPILED. The import above is the intended future
normal module name of the companion source-only cutoff-rounding draft.

One precision-indexed literal attached coefficient supplies all four inputs
of `eventually_RealB_le_currentK_log_of_same_rho_inputs`. Its majorant is
proved by the existing actual construction. Its coprime correction is zero
by the companion finite floor/ceiling buffer argument, which permits the
weak wall `nu*r ≤ (1-kappa)*b/(1+b)`, including equality.

P4A's density estimate and P3's exact signed distribution estimate remain
explicit conditional parameters. This module proves neither estimate and
does not replace the exact real-source error by a smooth-source error or
by a sum of absolute coefficient errors. The source-mass and endpoint
suppliers are reused through the existing same-rho assembly.
-/

namespace ImbalancedChen.P4BWeakGateUpperAssembly

noncomputable section
open Filter Topology

/-- Conditional actual upper bound at the weak roughness exponent wall.
The only remaining analytic parameters are `hdensity` for the displayed
actual coefficient and `hdistribution` for its exact signed error on the
literal manuscript source. The elementary coefficient and cap conditions
are displayed separately in the type. No P4A or P3 closure is claimed. -/
theorem eventually_RealB_le_currentK_log_of_actual_density_exact_distribution_weak_gate
    {b kappa nu r : ℝ} (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hnu : 0 < nu) (hsieve : nu * r < 1)
    (hwall : nu * r ≤ (1 - kappa) * (b / (1 + b)))
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ)
    (hepsilon : ∀ delta : ℝ, 0 < delta →
      0 < epsilon delta ∧ epsilon delta ≤ 1 ∧ (epsilon delta) ^ 2 ≤ r)
    (hcap : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (nu * r) ≤ (cap delta N : ℝ))
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N) ≤
          (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hdistribution : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N)| ≤
          delta * singularNormalization N) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  apply eventually_RealB_le_currentK_log_of_same_rho_inputs hb hb1 hkappa hsieve
    (fun delta => attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta))
    (fun delta => attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta))
  · intro delta hdelta
    obtain ⟨heps, hepsOne, hepsR⟩ := hepsilon delta hdelta
    filter_upwards [hcap delta hdelta, eventually_ge_atTop (2 : ℕ)] with N hcover hN
    intro _hEven n
    exact attachedUpperCoefficient_majorant hnu heps hepsOne hepsR
      (retain delta) (cap delta) hN hcover n
  · exact hdensity
  · intro delta hdelta
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    intro _hEven
    have hzero := P4BCutoffRounding.attached_coprimeCorrection_eq_zero_of_weak_wall
      hb hnu.le (hepsilon delta hdelta).2.2 hwall (retain delta) (cap delta) hN
    rw [hzero, abs_zero]
    apply mul_nonneg hdelta.le
    have hseries := (singularSeries_pos N).le
    unfold singularNormalization
    positivity
  · exact hdistribution

end
end ImbalancedChen.P4BWeakGateUpperAssembly
