import ImbalancedChen.P5zPositiveFamilyEventual
import ImbalancedChen.P5zUpsilon9SourceMass
import ImbalancedChen.P5zUpsilon9SmallPrimeBudget
import ImbalancedChen.CurrentChenP5U9OrderedPhysicalPP

/-!
# Original U9 route: actual source and endpoint payments discharged

SOURCE ONLY / UNCOMPILED. Imports are frozen source-only candidates and
actual source suppliers. No earlier candidate is modified by this module.

The final conditional original U9 mean retains only locally licensed
same-rho majorant, currentK density, THREE actual physical PP suppliers,
primitive coprime correction, and a geometric sublinear cutoff bound.
The source mass and small-prime loss are proved suppliers; actual unit
fibres are discharged by the preceding eventual bridge's actual supplier.
-/

namespace ImbalancedChen

noncomputable section

open Filter

/-- Three actual branch PP estimates imply the one original signed source
estimate. Every branch uses the same delta, Q and rho; constants and
thresholds are combined only after exact signed physical decomposition.
No absolute-value sum over physical moduli is introduced. -/
theorem p5z_u9_whole_PP_supplier_of_ordered_branches
    (Q : ℝ → ℕ → Finset ℕ) (rho : ℝ → ℕ → ℕ → ℝ)
    (Licensed : ℝ → ℕ → Prop)
    (hbranches : ∀ delta : ℝ, 0 < delta → ∀ j : Fin 3,
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
        Even N → Licensed delta N →
          |Part3.primeProductSignedError 3 N N (Q delta N) (rho delta N)
            (p5z_u9_orderedPhysicalWeight j N)| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ delta : ℝ, 0 < delta → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, Even N → Licensed delta N →
        |p5z_labelledDistributionError (p5z_u9_switchedLabels N) p5z_u9_product
          (fun _ => 1) N (Q delta N) (rho delta N)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
  intro delta hdelta
  obtain ⟨C₀, hC₀, h₀⟩ := hbranches delta hdelta (0 : Fin 3)
  obtain ⟨C₁, hC₁, h₁⟩ := hbranches delta hdelta (1 : Fin 3)
  obtain ⟨C₂, hC₂, h₂⟩ := hbranches delta hdelta (2 : Fin 3)
  refine ⟨C₀ + C₁ + C₂, by linarith only [hC₀, hC₁, hC₂], ?_⟩
  filter_upwards [h₀, h₁, h₂] with N h₀N h₁N h₂N
  intro hEven hL
  have h0 := h₀N hEven hL
  have h1 := h₁N hEven hL
  have h2 := h₂N hEven hL
  rw [p5z_u9_orderedPhysicalPP_decomposition]
  calc
    _ ≤ |Part3.primeProductSignedError 3 N N (Q delta N) (rho delta N)
          (p5z_u9_orderedPhysicalWeight 0 N)| +
        |Part3.primeProductSignedError 3 N N (Q delta N) (rho delta N)
          (p5z_u9_orderedPhysicalWeight 1 N)| +
        |Part3.primeProductSignedError 3 N N (Q delta N) (rho delta N)
          (p5z_u9_orderedPhysicalWeight 2 N)| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ C₀ * (N : ℝ) / Real.log (N : ℝ) ^ 3 +
        C₁ * (N : ℝ) / Real.log (N : ℝ) ^ 3 +
        C₂ * (N : ℝ) / Real.log (N : ℝ) ^ 3 :=
      add_le_add (add_le_add h0 h1) h2
    _ = (C₀ + C₁ + C₂) * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by ring

/-- Conditional ORIGINAL ninth mean at currentK times its literal
harmonic integral, with source-mass, small-prime and unit analytic premises
removed completely. The explicit remaining inputs are at one precision
family Q(delta),rho(delta), one local licence and actual branch coefficients.

This does not assert the still-open same-rho density or PP suppliers. The
cutoff premise is merely geometric size z(delta,N)<=N^theta with theta<1;
it is not a hypothesis bounding any weighted source or final U9 mean. -/
theorem p5z_eventually_original_u9_currentK_of_same_rho_branch_inputs
    (Q : ℝ → ℕ → Finset ℕ) (rho : ℝ → ℕ → ℕ → ℝ)
    (z : ℝ → ℕ → ℕ) (Licensed : ℝ → ℕ → Prop)
    (theta : ℝ) (htheta : theta < 1)
    (hlicensed : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ N : ℕ in atTop, Even N → Licensed delta N)
    (hmajor : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N → ∀ n : ℕ,
        (if Nat.Coprime n (sieveProduct N (z delta N)) then (1 : ℝ) else 0) ≤
          physicalDivisorSum (Q delta N) (rho delta N) n)
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N →
        physicalDensitySum (Q delta N) (rho delta N) ≤
          (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hbranches : ∀ delta : ℝ, 0 < delta → ∀ j : Fin 3,
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
        Even N → Licensed delta N →
          |Part3.primeProductSignedError 3 N N (Q delta N) (rho delta N)
            (p5z_u9_orderedPhysicalWeight j N)| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ 3)
    (hcop : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N →
        |p5z_labelledCoprimeCorrection (p5z_u9_switchedLabels N) p5z_u9_product
          (fun _ => 1) (Q delta N) (rho delta N)| ≤ delta * singularNormalization N)
    (hcap : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N → (z delta N : ℝ) ≤ (N : ℝ) ^ theta) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤
        (currentK * currentChenUpsilon9HarmonicIntegral + eta) * singularNormalization N := by
  have hmass : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N → ((p5z_u9_switchedLabels N).card : ℝ) ≤
        (currentChenUpsilon9HarmonicIntegral + delta) * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro delta hdelta
    filter_upwards [p5z_eventually_u9_switchedLabels_mass_le_harmonicIntegral delta hdelta]
      with N hN
    intro _hEven _hL
    exact hN
  have hPP := p5z_u9_whole_PP_supplier_of_ordered_branches Q rho Licensed hbranches
  have hsmall := p5z_u9_labelledSmallPrime_supplier_of_cutoff_bound
    z Licensed theta htheta hcap
  exact p5z_eventually_u9_upper_of_same_rho_label_suppliers Q rho z Licensed
    currentChenUpsilon9HarmonicIntegral p5z_u9_HarmonicIntegral_nonneg
    hlicensed hmajor hdensity hmass hPP hcop hsmall

end

end ImbalancedChen
