import ImbalancedChen.P5zUpsilon9ActualRawRoute

/-! SOURCE ONLY / UNCOMPILED. A genuine variable-density extension is needed
because density<=k for k>currentK does NOT imply density<=currentK. All actual
source/correction/endpoint suppliers are kept; no U9 mean is a premise. -/

namespace ImbalancedChen
noncomputable section
open Filter
open scoped BigOperators
open Classical

/-- Fixed same-rho U9 route at arbitrary nonnegative density coefficient k.
All source masses and endpoint errors are actual proved suppliers. -/
theorem p5z_eventually_u9_le_kJ_of_same_rho
    (k : ℝ) (hk : 0 ≤ k) (Q : ℕ → Finset ℕ) (rho : ℕ → ℕ → ℝ)
    (z : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hlicensed : ∀ᶠ N : ℕ in atTop, Even N → Licensed N)
    (hmajor : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N (z N)) then (1 : ℝ) else 0) ≤
        physicalDivisorSum (Q N) (rho N) n)
    (hdensity : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      physicalDensitySum (Q N) (rho N) ≤ k * (singularSeries N / Real.log (N : ℝ)))
    (hbranches : ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Even N → Licensed N →
        |Part3.primeProductSignedError 3 N N (Q N) (rho N)
          (p5z_u9_orderedPhysicalWeight j N)| ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ 3)
    (hcop : ∀ tau : ℝ, 0 < tau → ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |p5z_labelledCoprimeCorrection (p5z_u9_switchedLabels N) p5z_u9_product
        (fun _ => 1) (Q N) (rho N)| ≤ tau * singularNormalization N)
    (hsmall : ∀ tau : ℝ, 0 < tau → ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      p5z_labelledSmallPrimeMass (p5z_u9_switchedLabels N) p5z_u9_product
        (fun _ => 1) N (z N) ≤ tau * singularNormalization N) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N → currentChenUpsilon9 N ≤
      (k * currentChenUpsilon9HarmonicIntegral + eta) * singularNormalization N := by
  intro eta heta
  let tau := eta / (k + 4)
  have htau : 0 < tau := div_pos heta (by linarith only [hk])
  have hbudget : (k + 4) * tau = eta := by
    dsimp [tau]
    field_simp [show k + 4 ≠ 0 by linarith only [hk]] <;> ring
  have hPP := p5z_u9_whole_PP_supplier_of_ordered_branches
    (fun _ => Q) (fun _ => rho) (fun _ => Licensed) (fun _ _ => hbranches)
  obtain ⟨C, _hC, hPPraw⟩ := hPP tau htau
  filter_upwards [hlicensed, hmajor, hdensity, hPPraw,
    p5z_eventually_logCube_le_singularNormalization C tau htau,
    hcop tau htau, hsmall tau htau,
    p5z_eventually_u9_switchedWeight_mass_le_harmonicIntegral tau htau,
    eventually_currentChenUpsilon9_unitFibres_le_singularNormalization tau htau,
    eventually_ge_atTop (2 : ℕ)]
    with N hLN hmajorN hdensityN hPPrawN hPPpaidN hcopN hsmallN hmassN hunitN hN
  intro hEven
  have hL := hLN hEven
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hmass0 : 0 ≤ p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) :=
    Finset.sum_nonneg (fun m _ => p5z_u9_switchedWeight_nonneg N m)
  have hmain : p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) *
      physicalDensitySum (Q N) (rho N) ≤
      (k * (currentChenUpsilon9HarmonicIntegral + tau)) * singularNormalization N := by
    calc
      _ ≤ p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) *
          (k * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left (hdensityN hEven hL) hmass0
      _ ≤ ((currentChenUpsilon9HarmonicIntegral + tau) *
          ((N : ℝ) / Real.log (N : ℝ))) * (k * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hmassN (mul_nonneg hk (densityScale_pos hN).le)
      _ = (k * (currentChenUpsilon9HarmonicIntegral + tau)) * singularNormalization N := by
        rw [← sourceMassScale_mul_densityScale N]
        ring
  have hPPN := (le_abs_self _).trans ((hPPrawN hEven hL).trans hPPpaidN)
  have hcopUpper := (le_abs_self _).trans (hcopN hEven hL)
  have hsmallUpper := hsmallN hEven hL
  have hfinite := p5z_u9_le_same_rho_main_add_errors N (z N) (Q N) (rho N) (hmajorN hEven hL)
  rw [p5z_u9_switched_correction_eq_labels, p5z_u9_switched_distribution_eq_labels,
    p5z_u9_switched_smallPrimeMass_eq_labels] at hfinite
  have hbudgetH := congrArg (fun x : ℝ => x * singularNormalization N) hbudget
  nlinarith only [hfinite, hmain, hPPN, hcopUpper, hsmallUpper, hunitN, hbudgetH]

/-- Actual raw construction at the SAME k as the density input. The active
support is exact; actual majorant, one-bound and correction are discharged. -/
theorem p5z_eventually_u9_le_kJ_of_fixed_actual_rho
    (k nu r e scopeNu : ℝ) (hk : 0 ≤ k) (hnu : 0 < nu) (he : 0 < e)
    (he8 : e < 1 / 8) (heR : e ^ 2 ≤ r) (hnur : nu * r < 1) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hlicensed : ∀ᶠ N : ℕ in atTop, Even N → Licensed N)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 → (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hdensity : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      physicalDensitySum (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) ≤ k * (singularSeries N / Real.log (N : ℝ)))
    (hbranches : ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) (p5z_u9_orderedPhysicalWeight j N)| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N → currentChenUpsilon9 N ≤
      (k * currentChenUpsilon9HarmonicIntegral + eta) * singularNormalization N := by
  let R := attachedUpperCoefficient nu r e retain cap
  let A := fun N => p5z_activeModuli (attachedUpperModuli nu r e retain cap N) (R N)
  let Z := fun N : ℕ => Nat.ceil ((N : ℝ) ^ (nu * r))
  have hrho (N d : ℕ) : |R N d| ≤ 1 :=
    actualSmallRoughRho_abs_le_one (retain N) N (cap N) _ _ _ d
  have hmajor : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N (Z N)) then (1 : ℝ) else 0) ≤
        physicalDivisorSum (A N) (R N) n := by
    filter_upwards [hcap, eventually_ge_atTop (2 : ℕ)] with N hcapN hN
    intro hEven hL n
    dsimp only [A]
    rw [p5z_active_physicalDivisorSum]
    exact attachedUpperCoefficient_majorant hnu he (by linarith only [he8]) heR
      retain cap hN (hcapN hEven hL) n
  have hdensityA : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      physicalDensitySum (A N) (R N) ≤ k * (singularSeries N / Real.log (N : ℝ)) := by
    filter_upwards [hdensity] with N hN
    intro hEven hL
    dsimp only [A]
    rw [p5z_active_physicalDensitySum]
    exact hN hEven hL
  have hbranchesA : ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError 3 N N (A N) (R N) (p5z_u9_orderedPhysicalWeight j N)| ≤
        C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
    intro j
    obtain ⟨C, hC, hbound⟩ := hbranches j
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with N hN
    intro hEven hL
    dsimp only [A]
    rw [p5z_active_primeProductSignedError]
    exact hN hEven hL
  have hcop : ∀ tau : ℝ, 0 < tau → ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |p5z_labelledCoprimeCorrection (p5z_u9_switchedLabels N) p5z_u9_product
        (fun _ => 1) (A N) (R N)| ≤ tau * singularNormalization N := by
    intro tau htau
    filter_upwards [hscope, eventually_p5z_u9_productWeight_correction_of_real_modulus_scope
      scopeNu hscopeNu tau htau] with N hscopeN hpaidN
    intro hEven hL
    rw [← p5z_u9_switched_correction_eq_labels]
    apply hpaidN (A N) (R N) _ (fun d _ => hrho N d)
    intro d hd
    obtain ⟨hdD, hdne⟩ := Finset.mem_filter.mp hd
    have hsq := actualSmallRoughModuli_squarefree (retain N) N (cap N) _ _ hdD
    exact ⟨Nat.one_le_iff_ne_zero.mpr hsq.ne_zero, hscopeN hEven hL d hdD hdne⟩
  have hsmall : ∀ tau : ℝ, 0 < tau → ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      p5z_labelledSmallPrimeMass (p5z_u9_switchedLabels N) p5z_u9_product
        (fun _ => 1) N (Z N) ≤ tau * singularNormalization N := by
    intro tau htau
    filter_upwards [p5z_eventually_u9_smallPrimeMass_le_ceil_rpow (nu * r) hnur tau htau]
      with N hN
    intro _ _
    rw [← p5z_u9_switched_smallPrimeMass_eq_labels]
    exact hN
  exact p5z_eventually_u9_le_kJ_of_same_rho k hk A R Z Licensed
    hlicensed hmajor hdensityA hbranchesA hcop hsmall

end
end ImbalancedChen

