import ImbalancedChen.P5OriginalU9StrictBranchSupplier

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Valid one-sided reduction for the unchanged original U9Envelope. The saved
lower Simpson number remains the same slope; it is never asserted to be
an upper endpoint or replaced by one. At 0<=k<=K0 its comparison with the
saved upper number makes a genuine J upper enclosure sufficient.

This adapter is not the quadrature proof. The new U9 midpoint modules
derive the actual analytic enclosures without hUpper; their remaining
exact comparison with the saved upper number is OPEN. Same-rho density,
strict source PP, actual common e/licence/cap/scope remain explicit below.
-/

namespace ImbalancedChen.P5OriginalCoefficientArithmetic

noncomputable section
open Filter
open P5OriginalU9RepeatedPP

/-- Comparison of the two stored rationals, not an integral certificate. -/
theorem originalU9_stored_lower_le_upper : lowerU9AtK0 ≤ savedU9 := by
  norm_num [lowerU9AtK0,savedU9]

/-- The original stored slope and original envelope are preserved. -/
theorem originalU9_envelope_of_upper_only
    (hUpper : currentChenUpsilon9HarmonicIntegral ≤ p5z_originalU9UpperIntegralEndpoint) :
    fixedProductDensityCoefficient*currentChenUpsilon9HarmonicIntegral ≤
      U9Envelope fixedProductDensityCoefficient := by
  have hK0 : 0 < K0 := by norm_num [K0]
  have hupper : K0*currentChenUpsilon9HarmonicIntegral ≤ savedU9 := by
    have hh := (le_div_iff₀ hK0).mp hUpper
    simpa only [mul_comm] using hh
  have hslope : lowerU9AtK0/K0 ≤ savedU9/K0 :=
    div_le_div_of_nonneg_right originalU9_stored_lower_le_upper hK0.le
  have hk0 : 0 ≤ fixedProductDensityCoefficient := by
    norm_num [fixedProductDensityCoefficient,currentK,allowedDensityDelta]
  have hk : fixedProductDensityCoefficient ≤ K0 :=
    allowedDensityDelta_below_original_anchors.2.le
  have hh := retained_cell_envelope currentChenUpsilon9HarmonicIntegral savedU9
    (lowerU9AtK0/K0) fixedProductDensityCoefficient hupper hslope hk0 hk
  simpa only [U9Envelope,mul_div_assoc] using hh

/-- Same original fixed e and physical rho as J's supplier. The repeated
branch PP payment is reused, and the independent lower J port is absent.
The remaining upper endpoint is an explicitly OPEN consumer port. -/
theorem original_h9_of_upper_only_strict_actual_rho
    (nu r e scopeNu : ℝ) (hnu : 0 < nu) (he : 0 < e) (he8 : e < 1/8)
    (heR : e^2 ≤ r) (hnur : nu*r < 1) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hUpper : currentChenUpsilon9HarmonicIntegral ≤ p5z_originalU9UpperIntegralEndpoint)
    (hlicensed : ∀ᶠ N : ℕ in atTop,Even N → Licensed N)
    (hcap : ∀ᶠ N : ℕ in atTop,Even N → Licensed N → (N:ℝ)^(nu*r) ≤ (cap N:ℝ))
    (hscope : ∀ᶠ N : ℕ in atTop,Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 → (d:ℝ) ≤ (N:ℝ)^scopeNu)
    (hdensity : ∀ᶠ N : ℕ in atTop,Even N → Licensed N →
      physicalDensitySum (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) ≤
          fixedProductDensityCoefficient*(singularSeries N/Real.log (N:ℝ)))
    (hstrict : ∀ j : Fin 3,∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Even N → Licensed N →
        |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (strictWeight j N)| ≤
            C*(N:ℝ)/Real.log (N:ℝ)^3) :
    ∀ delta : ℝ,0 < delta → ∀ᶠ N : ℕ in atTop,Even N →
      currentChenUpsilon9 N ≤
        (U9Envelope fixedProductDensityCoefficient+delta)*singularNormalization N := by
  have hk : 0 ≤ fixedProductDensityCoefficient := by
    norm_num [fixedProductDensityCoefficient,currentK,allowedDensityDelta]
  have hbranches := original_branch_PP_of_strict nu r e scopeNu hscopeNu
    retain cap Licensed hscope hstrict
  have hraw := p5z_eventually_u9_le_kJ_of_fixed_actual_rho
    fixedProductDensityCoefficient nu r e scopeNu hk hnu he he8 heR hnur hscopeNu
    retain cap Licensed hlicensed hcap hscope hdensity hbranches
  have hcoef := originalU9_envelope_of_upper_only hUpper
  intro delta hdelta
  filter_upwards [hraw delta hdelta] with N hN
  intro hEven
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (hN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add_right hcoef delta) hH)

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
