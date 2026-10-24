import ImbalancedChen.P5zElevenErrorTransport
import ImbalancedChen.P5zPositiveFamilyBudget
import ImbalancedChen.P5zUpsilon9SwitchedMultiplicity
import ImbalancedChen.CurrentChenUpsilon9UnitBudget

/-!
# Eventual U* at one common precision and one common physical coefficient

SOURCE ONLY / UNCOMPILED. Imports P5z* refer to preceding source-only
candidates, not files claimed to be installed in the actual source tree.

The local licence is a predicate whose eventual validity is supplied
explicitly. Every estimate is used at that SAME licence, delta, Q and rho.
The PP input is the actual signed source discrepancy with explicit log^3
saving; its normalized payment is proved here. The analytic suppliers are
conditional and remain OPEN. Neither U* nor a whole U9 mean is an input.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators

variable {α : Type*}

/-- General positive-family U* from independent source/error estimates.
A single numerical delta is chosen first, then the same indexed physical
weight is used for every supplier. This includes J=0 without dividing by J.
The local licence is not inferred from arbitrary nonnegative weights. -/
theorem p5z_eventually_positive_family_upper_of_same_rho
    (S : ℕ → Finset α) (f : ℕ → α → ℕ) (W : ℕ → α → ℝ)
    (Q : ℝ → ℕ → Finset ℕ) (rho : ℝ → ℕ → ℕ → ℝ)
    (z : ℝ → ℕ → ℕ) (Licensed : ℝ → ℕ → Prop)
    (J : ℝ) (hJ : 0 ≤ J)
    (hW : ∀ᶠ N : ℕ in atTop, Even N → ∀ t ∈ S N, 0 ≤ W N t)
    (hSN : ∀ᶠ N : ℕ in atTop, Even N → ∀ t ∈ S N, f N t ≤ N)
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
    (hmass : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N → p5z_labelledMass (S N) (W N) ≤
        (J + delta) * ((N : ℝ) / Real.log (N : ℝ)))
    (hPP : ∀ delta : ℝ, 0 < delta → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, Even N → Licensed delta N →
        |p5z_labelledDistributionError (S N) (f N) (W N) N (Q delta N) (rho delta N)| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3)
    (hcop : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N →
        |p5z_labelledCoprimeCorrection (S N) (f N) (W N) (Q delta N) (rho delta N)| ≤
          delta * singularNormalization N)
    (hsmall : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N →
        p5z_labelledSmallPrimeMass (S N) (f N) (W N) N (z delta N) ≤
          delta * singularNormalization N) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledPrimeMass (S N) (f N) (W N) N ≤
        (currentK * J + eta) * singularNormalization N := by
  intro eta heta
  obtain ⟨delta, hdelta, _hdeltaOne, hbudget⟩ :=
    p5z_positive_family_budget_exists hJ heta
  obtain ⟨C, _hC, hPPraw⟩ := hPP delta hdelta
  have hPPpaid := p5z_eventually_logCube_le_singularNormalization C delta hdelta
  filter_upwards [hW, hSN, hlicensed delta hdelta, hmajor delta hdelta,
    hdensity delta hdelta, hmass delta hdelta, hPPraw, hPPpaid,
    hcop delta hdelta, hsmall delta hdelta, eventually_ge_atTop (2 : ℕ)]
    with N hWN hSNN hlicensedN hmajorN hdensityN hmassN hPPrawN hPPpaidN
      hcopN hsmallN hN
  intro hEven
  have hL := hlicensedN hEven
  have hPPN := (hPPrawN hEven hL).trans hPPpaidN
  exact p5z_labelled_positive_family_currentK_upper
    (S N) (f N) (W N) N (z delta N) (Q delta N) (rho delta N)
    J delta eta hN hJ hdelta.le hbudget (hWN hEven) (hSNN hEven)
    (hmajorN hEven hL) (hmassN hEven hL) (hdensityN hEven hL)
    (hcopN hEven hL) hPPN (hsmallN hEven hL)

/-- Actual ninth-family specialization. All source-side supplier
hypotheses are printed on the ORIGINAL literal triple labels. Exact
finite multiplicity transport connects them to the product weight.

The actual unit-fibre budget is already proved and is discharged in the
proof, so it is not reintroduced as an analytic premise. The source mass,
currentK density, PP, coprime correction and small-prime suppliers remain
open requirements for the same locally licensed rho(delta). -/
theorem p5z_eventually_u9_upper_of_same_rho_label_suppliers
    (Q : ℝ → ℕ → Finset ℕ) (rho : ℝ → ℕ → ℕ → ℝ)
    (z : ℝ → ℕ → ℕ) (Licensed : ℝ → ℕ → Prop)
    (J : ℝ) (hJ : 0 ≤ J)
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
    (hmass : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N → ((p5z_u9_switchedLabels N).card : ℝ) ≤
        (J + delta) * ((N : ℝ) / Real.log (N : ℝ)))
    (hPP : ∀ delta : ℝ, 0 < delta → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, Even N → Licensed delta N →
        |p5z_labelledDistributionError (p5z_u9_switchedLabels N) p5z_u9_product
          (fun _ => 1) N (Q delta N) (rho delta N)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3)
    (hcop : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N →
        |p5z_labelledCoprimeCorrection (p5z_u9_switchedLabels N) p5z_u9_product
          (fun _ => 1) (Q delta N) (rho delta N)| ≤ delta * singularNormalization N)
    (hsmall : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N →
        p5z_labelledSmallPrimeMass (p5z_u9_switchedLabels N) p5z_u9_product
          (fun _ => 1) N (z delta N) ≤ delta * singularNormalization N) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤ (currentK * J + eta) * singularNormalization N := by
  have hW : ∀ᶠ N : ℕ in atTop, Even N →
      ∀ m ∈ Finset.range N, 0 ≤ p5z_u9_switchedWeight N m :=
    Filter.Eventually.of_forall (fun N _ m _ => p5z_u9_switchedWeight_nonneg N m)
  have hSN : ∀ᶠ N : ℕ in atTop, Even N →
      ∀ m ∈ Finset.range N, id m ≤ N :=
    Filter.Eventually.of_forall (fun _ _ _ hm => (Finset.mem_range.mp hm).le)
  have hmassWeight : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N →
        p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) ≤
          (J + delta) * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro delta hdelta
    filter_upwards [hmass delta hdelta] with N hN
    intro hEven hL
    simpa only [p5z_u9_switchedMass_eq_card] using hN hEven hL
  have hPPWeight : ∀ delta : ℝ, 0 < delta → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, Even N → Licensed delta N →
        |p5z_labelledDistributionError (Finset.range N) id (p5z_u9_switchedWeight N)
          N (Q delta N) (rho delta N)| ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
    intro delta hdelta
    obtain ⟨C, hC, hbound⟩ := hPP delta hdelta
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with N hN
    intro hEven hL
    simpa only [p5z_u9_switched_distribution_eq_labels] using hN hEven hL
  have hcopWeight : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N →
        |p5z_labelledCoprimeCorrection (Finset.range N) id (p5z_u9_switchedWeight N)
          (Q delta N) (rho delta N)| ≤ delta * singularNormalization N := by
    intro delta hdelta
    filter_upwards [hcop delta hdelta] with N hN
    intro hEven hL
    simpa only [p5z_u9_switched_correction_eq_labels] using hN hEven hL
  have hsmallWeight : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N →
        p5z_labelledSmallPrimeMass (Finset.range N) id (p5z_u9_switchedWeight N)
          N (z delta N) ≤ delta * singularNormalization N := by
    intro delta hdelta
    filter_upwards [hsmall delta hdelta] with N hN
    intro hEven hL
    simpa only [p5z_u9_switched_smallPrimeMass_eq_labels] using hN hEven hL
  have hprime := p5z_eventually_positive_family_upper_of_same_rho
    (fun N => Finset.range N) (fun _ => id) p5z_u9_switchedWeight Q rho z Licensed
    J hJ hW hSN hlicensed hmajor hdensity hmassWeight hPPWeight hcopWeight hsmallWeight
  intro eta heta
  have hhalf : 0 < eta / 2 := half_pos heta
  filter_upwards [hprime (eta / 2) hhalf,
    eventually_currentChenUpsilon9_unitFibres_le_singularNormalization (eta / 2) hhalf]
    with N hprimeN hunitN
  intro hEven
  rw [p5z_u9_eq_switchedWeight_primeMass_add_units]
  have hp := hprimeN hEven
  nlinarith only [hp, hunitN]

end

end ImbalancedChen
