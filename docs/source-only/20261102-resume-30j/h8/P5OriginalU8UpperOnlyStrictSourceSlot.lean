import ImbalancedChen.P5OriginalU8DiagonalSourcePayment

/-!
SOURCE ONLY / UNCOMPILED. Original h8 with two reduced ports:
(1) the q=p2 physical-source PP error has an internal arithmetic payment;
(2) the independent Simpson lower integral endpoint is not needed at the
fixed nonnegative k<K0. The original stored affine envelope is unchanged.
The actual J8 upper endpoint, full-policy density and strict PP remain OPEN.
-/

namespace ImbalancedChen.P5OriginalCoefficientArithmetic

noncomputable section
open Filter
open P5U8SharpKSource P5OriginalU8DiagonalSourcePayment

/-- This compares stored rational numbers only; it is not a certificate
for either endpoint of the actual integral. -/
theorem originalU8_stored_lower_le_upper : lowerU8AtK0 ≤ savedU8 := by
  norm_num [lowerU8AtK0, savedU8]

/-- Nonnegative k lets one scale the proved upper integral inequality.
The resulting k*savedU8/K0 majorant lies below the UNCHANGED original
envelope because its stored slope is at most savedU8/K0. No claim about
the true lower endpoint and no replacement of the stored slope occurs. -/
theorem originalU8_envelope_of_upper_only
    (hUpper : currentChenUpsilon8HarmonicIntegral ≤ p5z_originalU8UpperIntegralEndpoint) :
    fixedProductDensityCoefficient * currentChenUpsilon8HarmonicIntegral ≤
      U8Envelope fixedProductDensityCoefficient := by
  have hK0 : 0 < K0 := by norm_num [K0]
  have hUpper' : K0 * currentChenUpsilon8HarmonicIntegral ≤ savedU8 := by
    have h := (le_div_iff₀ hK0).mp hUpper
    simpa only [mul_comm] using h
  have hslope : lowerU8AtK0 / K0 ≤ savedU8 / K0 :=
    div_le_div_of_nonneg_right originalU8_stored_lower_le_upper hK0.le
  have hk0 : 0 ≤ fixedProductDensityCoefficient := by
    norm_num [fixedProductDensityCoefficient, currentK, allowedDensityDelta]
  have hk : fixedProductDensityCoefficient ≤ K0 :=
    allowedDensityDelta_below_original_anchors.2.le
  have h := retained_cell_envelope currentChenUpsilon8HarmonicIntegral savedU8
    (lowerU8AtK0 / K0) fixedProductDensityCoefficient hUpper' hslope hk0 hk
  simpa only [U8Envelope, mul_div_assoc] using h

/-- Original h8 on its exact fixed density, now requiring analytic PP only
for strict p1<p2<q source labels. All full-policy limits, the geometric
licence, active scope and J8 upper endpoint remain visible original ports.
This theorem does not assert any of those outstanding suppliers. -/
theorem original_h8_of_upper_only_actual_full_policy_strict_source
    (nu r epsilonMax rawBound scopeNu : ℝ) (hnu : 0 < nu) (hr : 0 < r) (hnur : nu * r < 1)
    (hepsilonMax : 0 < epsilonMax) (hscopeNu : 0 ≤ scopeNu)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (integral : ℝ → ℝ) (Licensed : ℝ → ℕ → Prop)
    (hUpper : currentChenUpsilon8HarmonicIntegral ≤ p5z_originalU8UpperIntegralEndpoint)
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
    (hPPstrict : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
        |p5z_labelledDistributionError (strictTriples N) product (fun _ => 1) N
          (attachedUpperModuli nu r e (retainOdd e) cap N)
          (attachedUpperCoefficient nu r e (retainOdd e) cap N)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N → currentChenUpsilon8 N ≤
      (U8Envelope fixedProductDensityCoefficient + delta) * singularNormalization N := by
  have hcapF : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) := by
    rw [Filter.eventually_inf_principal]
    filter_upwards [hcap] with N hN
    exact fun hposEven => hN hposEven.2
  obtain ⟨e, he, he8, heMax, heR, N₀, _hN₀, hdensity⟩ :=
    exists_actualSmallRoughRho_density_le_of_full_policy_limits nu r epsilonMax rawBound
      fixedProductDensityCoefficient hnu hr hepsilonMax retainOdd cap integral
      hcapF hIntegral hCertificate hgap
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
  have hk : 0 ≤ fixedProductDensityCoefficient := by
    norm_num [fixedProductDensityCoefficient, currentK, allowedDensityDelta]
  have hphysical := actual_physicalPP_of_strict_source nu r e scopeNu hscopeNu
    (retainOdd e) cap (Licensed e) (hscope e he he8 heMax heR)
    (hPPstrict e he he8 heMax heR)
  have hraw := p5z_eventually_u8_le_kJ_of_fixed_actual_rho fixedProductDensityCoefficient
    nu r e scopeNu hk hnu he he8 heR hnur hscopeNu (retainOdd e) cap (Licensed e)
    (hlicensed e he he8 heMax heR) hcapFixed (hscope e he he8 heMax heR)
    hdensityFixed hphysical
  have hcoef := originalU8_envelope_of_upper_only hUpper
  intro delta hdelta
  filter_upwards [hraw delta hdelta] with N hN
  intro hEven
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (hN hEven).trans (mul_le_mul_of_nonneg_right (add_le_add_right hcoef delta) hH)

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
