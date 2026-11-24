import ImbalancedChen.RealUpperCountingAssembly
import ImbalancedChen.EnlargedSelbergCap

/-!
# Proved geometric inputs for the actual attached upper coefficient

The majorant and coprime correction in the real counting assembly are
discharged for the literal small/rough coefficient. The sieve cutoff and
the manuscript product cutoff retain their exact natural rounding.
Only the actual density bound and signed distribution estimate remain
analytic premises of the final assembly below.
-/

namespace ImbalancedChen

noncomputable section
open Filter Topology

/-- A positive exponent gap pays the natural ceiling at the manuscript's
literal lower product cutoff `2 * N^(1-kappa)`. -/
theorem eventually_manuscript_sieve_gate
    {b kappa theta : ℝ} (hb : 0 < b) (htheta : 0 ≤ theta)
    (hgap : theta < (1 - kappa) * (b / (1 + b))) :
    ∀ᶠ N : ℕ in atTop,
      0 < manuscriptHalfProductCutoff kappa N ∧
        (Nat.ceil ((N : ℝ) ^ theta) : ℝ) ≤
          (manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b)) := by
  have halpha : 0 ≤ b / (1 + b) := div_nonneg hb.le (by linarith)
  filter_upwards [eventually_floor_rpow_add_one_le_rpow htheta hgap,
    eventually_ge_atTop (1 : ℕ)] with N hround hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hpow : 0 < (N : ℝ) ^ (1 - kappa) := Real.rpow_pos_of_pos hNpos _
  refine ⟨mul_pos (by norm_num) hpow, ?_⟩
  calc
    (Nat.ceil ((N : ℝ) ^ theta) : ℝ) ≤
        (Nat.floor ((N : ℝ) ^ theta) : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one ((N : ℝ) ^ theta)
    _ ≤ (N : ℝ) ^ ((1 - kappa) * (b / (1 + b))) := hround
    _ = ((N : ℝ) ^ (1 - kappa)) ^ (b / (1 + b)) :=
      Real.rpow_mul hNpos.le _ _
    _ ≤ (manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b)) := by
      apply Real.rpow_le_rpow hpow.le _ halpha
      change (N : ℝ) ^ (1 - kappa) ≤ 2 * (N : ℝ) ^ (1 - kappa)
      linarith

/-- The exact finite modulus set of the attached coefficient. -/
def attachedUpperModuli (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  actualSmallRoughModuli (retain N) N (cap N)
    ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))

/-- The same coefficient is used for the majorant, density and error. -/
def attachedUpperCoefficient (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N d : ℕ) : ℝ :=
  actualSmallRoughRho (retain N) N (cap N)
    ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
    ((N : ℝ) ^ (nu * epsilon)) d

theorem attachedUpperCoefficient_majorant
    {nu r epsilon : ℝ} (hnu : 0 < nu) (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon ≤ 1) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N : ℕ} (hN : 2 ≤ N) (hcap : (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (n : ℕ) :
    (if Nat.Coprime n (sieveProduct N (Nat.ceil ((N : ℝ) ^ (nu * r))))
      then (1 : ℝ) else 0) ≤
        physicalDivisorSum (attachedUpperModuli nu r epsilon retain cap N)
          (attachedUpperCoefficient nu r epsilon retain cap N) n := by
  have hNreal : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hepsSquare : epsilon ^ 2 ≤ epsilon := by nlinarith
  exact actualSmallRoughRho_sieveProduct_majorant (retain N) N (cap N) _ _ _
    (Real.one_lt_rpow hNreal (mul_pos hnu hepsilon))
    (Real.rpow_le_rpow_of_exponent_le hNreal.le
      (mul_le_mul_of_nonneg_left hepsSquare hnu.le))
    (Real.rpow_le_rpow_of_exponent_le hNreal.le
      (mul_le_mul_of_nonneg_left hepsilonR hnu.le)) hcap n

/-- No estimate is needed for this correction: it is exactly zero beyond
the proved roughness threshold, for every policy and enumeration cap. -/
theorem eventually_attachedUpper_coprimeCorrection_eq_zero
    {b kappa nu r epsilon : ℝ} (hb : 0 < b) (hnu : 0 < nu)
    (hr : 0 ≤ r) (hepsilonR : epsilon ^ 2 ≤ r)
    (hgap : nu * r < (1 - kappa) * (b / (1 + b)))
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa N)
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) = 0 := by
  filter_upwards [eventually_manuscript_sieve_gate hb (mul_nonneg hnu.le hr) hgap,
    eventually_ge_atTop (1 : ℕ)] with N hgate hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  apply realPhysicalCoprimeCorrection_eq_zero_of_gate _ _ hb hgate.1 hgate.2
  intro d hd _hactive
  exact actualSmallRoughModuli_dvd_sieveProduct_ceil (retain N) N (cap N) _ _
    (Real.rpow_le_rpow_of_exponent_le hNreal
      (mul_le_mul_of_nonneg_left hepsilonR hnu.le)) hd

/-- The actual construction discharges two of the four same-weight inputs.
This is still conditional on the actual density and signed distribution
estimates; it does not claim that either analytic input has been proved. -/
theorem eventually_RealB_le_currentK_log_of_actual_density_distribution
    {b kappa nu r : ℝ} (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hnu : 0 < nu) (hr : 0 < r) (hsieve : nu * r < 1)
    (hgap : nu * r < (1 - kappa) * (b / (1 + b)))
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ)
    (hepsilon : ∀ delta : ℝ, 0 < delta →
      0 < epsilon delta ∧ epsilon delta ≤ 1 ∧ (epsilon delta) ^ 2 ≤ r)
    (hcap : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (nu * r) ≤ (cap delta N : ℝ))
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
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
    filter_upwards [eventually_attachedUpper_coprimeCorrection_eq_zero hb hnu hr.le
      (hepsilon delta hdelta).2.2 hgap (retain delta) (cap delta)] with N hzero
    intro _hEven
    rw [hzero, abs_zero]
    apply mul_nonneg hdelta.le
    have hseries := (singularSeries_pos N).le
    unfold singularNormalization
    positivity
  · exact hdistribution

end
end ImbalancedChen
