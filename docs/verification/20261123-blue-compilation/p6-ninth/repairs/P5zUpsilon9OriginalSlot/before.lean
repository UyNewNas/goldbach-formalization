import ImbalancedChen.P5zUpsilon9GeneralDensityRoute
import ImbalancedChen.P5OriginalFixedDensitySupplierAssembly

/-!
# Actual original U9 supplier slot at the original fixed density coefficient

SOURCE ONLY / UNCOMPILED. The two U9 integral inequalities below are
INDEPENDENT P2 CERTIFICATE obligations; no numerical enclosure is asserted.
Their upper and lower endpoints are the exact original saved U9 endpoint
and independent Simpson lower slope from P5OriginalKFeedbackBudget.
-/

namespace ImbalancedChen.P5OriginalCoefficientArithmetic
noncomputable section
open Filter

/-- Independent P2 U9 upper integral endpoint, literally savedU9/K0. -/
def p5z_originalU9UpperIntegralEndpoint : ℝ := savedU9 / K0

/-- Independent P2 lower integral endpoint: the feedback slope uses the
original LOWER Simpson enclosure, not the saved upper endpoint divided by K0. -/
def p5z_originalU9LowerIntegralEndpoint : ℝ := lowerU9AtK0 / K0

theorem p5z_originalU9UpperIntegralEndpoint_exact :
    p5z_originalU9UpperIntegralEndpoint =
      ((3937512077512215599969887 : ℝ) / 1208925819614629174706176) /
        ((67619 : ℝ) / 10000) := by
  norm_num [p5z_originalU9UpperIntegralEndpoint, savedU9, K0]

theorem p5z_originalU9LowerIntegralEndpoint_exact :
    p5z_originalU9LowerIntegralEndpoint =
      ((16911485600294926597530591281091713 : ℝ) / 5192296858534827628530496329220096) /
        ((67619 : ℝ) / 10000) := by
  norm_num [p5z_originalU9LowerIntegralEndpoint, lowerU9AtK0, K0]

/-- The ORIGINAL independent upper/lower integral enclosures give precisely
the original affine U9 envelope at k=currentK+10^-8. No U9 mean is used. -/
theorem p5z_originalU9_envelope_of_integral_certificates
    (hUpper : currentChenUpsilon9HarmonicIntegral ≤ p5z_originalU9UpperIntegralEndpoint)
    (hLower : p5z_originalU9LowerIntegralEndpoint ≤ currentChenUpsilon9HarmonicIntegral) :
    fixedProductDensityCoefficient * currentChenUpsilon9HarmonicIntegral ≤
      U9Envelope fixedProductDensityCoefficient := by
  have hK0 : 0 < K0 := by norm_num [K0]
  have hupperK0 : K0 * currentChenUpsilon9HarmonicIntegral ≤ savedU9 := by
    have h := (le_div_iff₀ hK0).mp hUpper
    simpa only [mul_comm] using h
  have hfixed : fixedProductDensityCoefficient ≤ K0 :=
    allowedDensityDelta_below_original_anchors.2.le
  exact complete_switched_cost_envelope currentChenUpsilon9HarmonicIntegral
    savedU9 lowerU9AtK0 fixedProductDensityCoefficient hupperK0 hLower hfixed

/-- Exact h9 slot consumed by P5OriginalFixedDensitySupplierAssembly.
The density hypothesis is at the SAME original fixed k. Independent P2
integral certificates, actual policy scope and actual branch PP remain
explicit; no original U9 mean or source-mass estimate is assumed. -/
theorem p5z_original_h9_of_fixed_actual_rho
    (nu r e scopeNu : ℝ) (hnu : 0 < nu) (he : 0 < e) (he8 : e < 1 / 8)
    (heR : e ^ 2 ≤ r) (hnur : nu * r < 1) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hUpper : currentChenUpsilon9HarmonicIntegral ≤ p5z_originalU9UpperIntegralEndpoint)
    (hLower : p5z_originalU9LowerIntegralEndpoint ≤ currentChenUpsilon9HarmonicIntegral)
    (hlicensed : ∀ᶠ N : ℕ in atTop, Even N → Licensed N)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 → (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hdensity : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      physicalDensitySum (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) ≤
          fixedProductDensityCoefficient * (singularSeries N / Real.log (N : ℝ)))
    (hbranches : ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) (p5z_u9_orderedPhysicalWeight j N)| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤
        (U9Envelope fixedProductDensityCoefficient + delta) * singularNormalization N := by
  have hk : 0 ≤ fixedProductDensityCoefficient := by
    norm_num [fixedProductDensityCoefficient, currentK, allowedDensityDelta]
  have hraw := p5z_eventually_u9_le_kJ_of_fixed_actual_rho
    fixedProductDensityCoefficient nu r e scopeNu hk hnu he he8 heR hnur hscopeNu
    retain cap Licensed hlicensed hcap hscope hdensity hbranches
  have hcoefficient := p5z_originalU9_envelope_of_integral_certificates hUpper hLower
  intro delta hdelta
  filter_upwards [hraw delta hdelta] with N hN
  intro hEven
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (hN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add_right hcoefficient delta) hH)

/-- Joint full-policy version of the original h9 slot. The actual density
selection theorem is called with densityCap=the ORIGINAL fixed k, and
all PP/licence/scope hypotheses are instantiated at its SAME e witness.
The genuine full-policy limit/certificate and independent U9 integral
certificate remain open production obligations, rather than U9mean inputs. -/
theorem p5z_original_h9_of_actual_full_policy
    (nu r epsilonMax rawBound scopeNu : ℝ)
    (hnu : 0 < nu) (hr : 0 < r) (hnur : nu * r < 1)
    (hepsilonMax : 0 < epsilonMax) (hscopeNu : 0 ≤ scopeNu)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (integral : ℝ → ℝ) (Licensed : ℝ → ℕ → Prop)
    (hUpper : currentChenUpsilon9HarmonicIntegral ≤ p5z_originalU9UpperIntegralEndpoint)
    (hLower : p5z_originalU9LowerIntegralEndpoint ≤ currentChenUpsilon9HarmonicIntegral)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hIntegral : ∀ e : ℝ, 0 < e → e < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd e N) N (cap N) 0 ((N : ℝ) ^ (nu * r)))
          (fixedRoughCoefficient (retainOdd e N) N (cap N) 0 ((N : ℝ) ^ (nu * r))) *
            Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (nhds (integral e)))
    (hCertificate : ∀ e : ℝ, 0 < e → e < epsilonMax → integral e ≤ rawBound)
    (hgap : rawBound < fixedProductDensityCoefficient)
    (hlicensed : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∀ᶠ N : ℕ in atTop, Even N → Licensed e N)
    (hscope : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∀ᶠ N : ℕ in atTop, Even N → Licensed e N → ∀ d : ℕ,
        d ∈ attachedUpperModuli nu r e (retainOdd e) cap N →
        attachedUpperCoefficient nu r e (retainOdd e) cap N d ≠ 0 → (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hbranches : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
        |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e (retainOdd e) cap N)
          (attachedUpperCoefficient nu r e (retainOdd e) cap N) (p5z_u9_orderedPhysicalWeight j N)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤
        (U9Envelope fixedProductDensityCoefficient + delta) * singularNormalization N := by
  have hcapF : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) := by
    rw [Filter.eventually_inf_principal]
    filter_upwards [hcap] with N hN
    intro hposEven
    exact hN hposEven.2
  obtain ⟨e, he, he8, heMax, heR, N₀, hN₀, hdensity⟩ :=
    exists_actualSmallRoughRho_density_le_of_full_policy_limits
      nu r epsilonMax rawBound fixedProductDensityCoefficient hnu hr hepsilonMax
      retainOdd cap integral hcapF hIntegral hCertificate hgap
  have hcapFixed : ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) := by
    filter_upwards [hcap] with N hN
    exact fun hEven _ => hN hEven
  have hdensityFixed : ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
      physicalDensitySum (attachedUpperModuli nu r e (retainOdd e) cap N)
        (attachedUpperCoefficient nu r e (retainOdd e) cap N) ≤
          fixedProductDensityCoefficient * (singularSeries N / Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    exact fun hEven _ => hdensity N hN hEven
  exact p5z_original_h9_of_fixed_actual_rho nu r e scopeNu hnu he he8 heR hnur hscopeNu
    (retainOdd e) cap (Licensed e) hUpper hLower
    (hlicensed e he he8 heMax heR) hcapFixed (hscope e he he8 heMax heR)
    hdensityFixed (hbranches e he he8 heMax heR)

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
