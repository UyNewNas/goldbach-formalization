import ImbalancedChen.P5U7OriginalArithmeticMeanUpper
import ImbalancedChen.P5zUpsilon7OriginalSlot

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The former original-source-mass obligation of the actual-rho U7 route is
discharged by the proved literal arithmetic source mean. The receiver
prime estimate still has its real same-coefficient density and signed
rank-three PLUS rank-four distribution prerequisites. The original h7
slot additionally keeps both original integral endpoint certificates and
the actual policy/licensing obligations explicit.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators
open Classical
open P5U7OriginalPhysicalPP

/-- The original actual-rho seventh mean now has NO source-mass or mean
premise. Every physical coefficient in the density and combined signed PP
expression is the same attached coefficient at the same fixed e. -/
theorem p5z_eventually_original_u7_le_kJ_of_fixed_actual_rho
    (k nu r e scopeNu : ℝ) (hk : 0 ≤ k)
    (hnu : 0 < nu) (he : 0 < e) (he8 : e < 1 / 8) (heR : e ^ 2 ≤ r)
    (hnur : nu * r < 1) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hlicensed : ∀ᶠ N : ℕ in atTop, Even N → Licensed N)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 →
        (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hdensity : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      physicalDensitySum (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) ≤
      k * (singularSeries N / Real.log (N : ℝ)))
    (hPP : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (weight3 N) +
        Part3.primeProductSignedError 4 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (weight4 N)| ≤
        C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon7 N ≤
        (k * p5U7OriginalOmegaIntegral 1 + epsilon) * singularNormalization N := by
  have hmass : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      ((p5U7ArithmeticThree N).card : ℝ) + ((p5U7ArithmeticFour N).card : ℝ) ≤
        (p5U7OriginalOmegaIntegral 1 + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro eta heta
    filter_upwards [p5U7Original_eventually_arithmetic_mass_le_integral eta heta]
      with N hN
    exact fun _ => hN
  exact p5z_eventually_u7_le_kJ_of_fixed_actual_rho
    (p5U7OriginalOmegaIntegral 1) k nu r e scopeNu
    (p5U7OriginalOmegaIntegral_nonneg (by norm_num)) hk
    hnu he he8 heR hnur hscopeNu retain cap Licensed hmass
    hlicensed hcap hscope hdensity hPP

end

end ImbalancedChen

namespace ImbalancedChen.P5OriginalCoefficientArithmetic

noncomputable section

open Filter
open P5U7OriginalPhysicalPP

/-- Source-supplied original h7 slot. The original upper and lower Omega
endpoint certificates remain independent inputs. Actual policy limits,
strict density gap, same-e licensing and physical PP also remain explicit;
the former hmass input has been proved and substituted. -/
theorem p5z_original_h7_of_actual_full_policy_source_supplied
    (nu r epsilonMax rawBound scopeNu : ℝ)
    (hnu : 0 < nu) (hr : 0 < r) (hnur : nu * r < 1)
    (hepsilonMax : 0 < epsilonMax) (hscopeNu : 0 ≤ scopeNu)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (integral : ℝ → ℝ) (Licensed : ℝ → ℕ → Prop)
    (hUpper : p5z_originalU7LiteralJ ≤ p5z_originalU7UpperIntegralEndpoint)
    (hLower : p5z_originalU7LowerIntegralEndpoint ≤ p5z_originalU7LiteralJ)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N →
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
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
        attachedUpperCoefficient nu r e (retainOdd e) cap N d ≠ 0 →
          (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hPP : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
        |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e (retainOdd e) cap N)
            (attachedUpperCoefficient nu r e (retainOdd e) cap N) (weight3 N) +
          Part3.primeProductSignedError 4 N N (attachedUpperModuli nu r e (retainOdd e) cap N)
            (attachedUpperCoefficient nu r e (retainOdd e) cap N) (weight4 N)| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon7 N ≤
        (U7Envelope fixedProductDensityCoefficient + delta) * singularNormalization N := by
  have hmass : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      ((p5U7ArithmeticThree N).card : ℝ) + ((p5U7ArithmeticFour N).card : ℝ) ≤
        (p5z_originalU7LiteralJ + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro eta heta
    filter_upwards [p5U7Original_eventually_arithmetic_mass_le_integral eta heta]
      with N hN
    intro _
    simpa only [p5z_originalU7LiteralJ] using hN
  exact p5z_original_h7_of_actual_full_policy nu r epsilonMax rawBound scopeNu
    hnu hr hnur hepsilonMax hscopeNu retainOdd cap integral Licensed
    hUpper hLower hmass hcap hIntegral hCertificate hgap hlicensed hscope hPP

end

end ImbalancedChen.P5OriginalCoefficientArithmetic
