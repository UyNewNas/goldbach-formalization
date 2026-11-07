import ImbalancedChen.P5zUpsilon9OriginalRoute
import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.CurrentChenP5U9CoprimeCorrection

/-!
# U9 with one literal actual small/rough coefficient

SOURCE ONLY / UNCOMPILED. This leaf changes no frozen predecessor.
The actual raw rho is one-bounded by a PROVED actual API using unique
small/rough factorization. That fact is not transferred to compiled rho.
Only nonzero physical coefficients enter the active modulus scope. Exact
finite identities show that this removes no main/error/majorant term.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators
open Classical

def p5z_activeModuli (D : Finset ℕ) (rho : ℕ → ℝ) : Finset ℕ :=
  D.filter (fun d => rho d ≠ 0)

/-- Erasing only zero coefficients is an exact signed finite identity. -/
theorem p5z_active_sum_rho_mul (D : Finset ℕ) (rho G : ℕ → ℝ) :
    (∑ d ∈ p5z_activeModuli D rho, rho d * G d) = ∑ d ∈ D, rho d * G d := by
  unfold p5z_activeModuli
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : rho d = 0 <;> simp [h]

theorem p5z_active_physicalDivisorSum (D : Finset ℕ) (rho : ℕ → ℝ) (n : ℕ) :
    physicalDivisorSum (p5z_activeModuli D rho) rho n = physicalDivisorSum D rho n := by
  simpa only [physicalDivisorSum, mul_ite, mul_one, mul_zero] using
    p5z_active_sum_rho_mul D rho (fun d => if d ∣ n then 1 else 0)

theorem p5z_active_physicalDensitySum (D : Finset ℕ) (rho : ℕ → ℝ) :
    physicalDensitySum (p5z_activeModuli D rho) rho = physicalDensitySum D rho := by
  simpa only [physicalDensitySum, div_eq_mul_inv] using
    p5z_active_sum_rho_mul D rho (fun d => (Nat.totient d : ℝ)⁻¹)

theorem p5z_active_primeProductSignedError (k P N : ℕ) (D : Finset ℕ)
    (rho : ℕ → ℝ) (W : (Fin k → Fin (P + 1)) → ℝ) :
    Part3.primeProductSignedError k P N (p5z_activeModuli D rho) rho W =
      Part3.primeProductSignedError k P N D rho W := by
  unfold Part3.primeProductSignedError
  exact p5z_active_sum_rho_mul D rho _

/-- The actual raw coefficient now supplies majorant, small-prime,
source-mass, unit, coefficient size and primitive correction itself.
The remaining analytic inputs are the literal same-rho density and the
three actual physical PP estimates, under one explicit local licence.

The displayed physical carrier can include zero coefficients above its
level; the scope hypothesis correctly concerns only nonzero coefficients.
The cutoff is the SAME ceil(N^(nu*r)) used by the proved actual majorant. -/
theorem p5z_eventually_u9_currentK_of_fixed_actual_rho
    (nu r e scopeNu : ℝ) (hnu : 0 < nu) (he : 0 < e) (he8 : e < 1 / 8)
    (heR : e ^ 2 ≤ r) (hnur : nu * r < 1) (hscopeNu : 0 ≤ scopeNu)
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
          currentK * (singularSeries N / Real.log (N : ℝ)))
    (hbranches : ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Even N → Licensed N →
        |Part3.primeProductSignedError 3 N N
          (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N)
          (p5z_u9_orderedPhysicalWeight j N)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤
        (currentK * currentChenUpsilon9HarmonicIntegral + eta) * singularNormalization N := by
  let R := attachedUpperCoefficient nu r e retain cap
  let A := fun N => p5z_activeModuli (attachedUpperModuli nu r e retain cap N) (R N)
  let Q := fun _delta : ℝ => A
  let rho := fun _delta : ℝ => R
  let z := fun (_delta : ℝ) (N : ℕ) => Nat.ceil ((N : ℝ) ^ (nu * r))
  let Lic := fun (_delta : ℝ) (N : ℕ) => Licensed N
  have hrho (N d : ℕ) : |R N d| ≤ 1 := by
    exact actualSmallRoughRho_abs_le_one (retain N) N (cap N) _ _ _ d
  have hlic : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Lic delta N := fun _ _ => hlicensed
  have hmajor : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Lic delta N → ∀ n : ℕ,
        (if Nat.Coprime n (sieveProduct N (z delta N)) then (1 : ℝ) else 0) ≤
          physicalDivisorSum (Q delta N) (rho delta N) n := by
    intro delta hdelta
    filter_upwards [hcap, eventually_ge_atTop (2 : ℕ)] with N hcapN hN
    intro hEven hL n
    dsimp only [Q, A, rho]
    rw [p5z_active_physicalDivisorSum]
    exact attachedUpperCoefficient_majorant hnu he (by linarith only [he8]) heR
      retain cap hN (hcapN hEven hL) n
  have hdensityPaid : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Lic delta N → physicalDensitySum (Q delta N) (rho delta N) ≤
        (currentK + delta) * (singularSeries N / Real.log (N : ℝ)) := by
    intro delta hdelta
    filter_upwards [hdensity, eventually_ge_atTop (2 : ℕ)] with N hdN hN
    intro hEven hL
    dsimp only [Q, A, rho]
    rw [p5z_active_physicalDensitySum]
    exact (hdN hEven hL).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hdelta]) (densityScale_pos hN).le)
  have hbranchPaid : ∀ delta : ℝ, 0 < delta → ∀ j : Fin 3,
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Lic delta N →
        |Part3.primeProductSignedError 3 N N (Q delta N) (rho delta N)
          (p5z_u9_orderedPhysicalWeight j N)| ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
    intro delta hdelta j
    obtain ⟨C, hC, hbound⟩ := hbranches j
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with N hN
    intro hEven hL
    dsimp only [Q, A, rho]
    rw [p5z_active_primeProductSignedError]
    exact hN hEven hL
  have hPP := p5z_u9_whole_PP_supplier_of_ordered_branches Q rho Lic hbranchPaid
  have hmass : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Lic delta N → ((p5z_u9_switchedLabels N).card : ℝ) ≤
        (currentChenUpsilon9HarmonicIntegral + delta) * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro delta hdelta
    filter_upwards [p5z_eventually_u9_switchedLabels_mass_le_harmonicIntegral delta hdelta]
      with N hN
    exact fun _ _ => hN
  have hcop : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Lic delta N →
        |p5z_labelledCoprimeCorrection (p5z_u9_switchedLabels N) p5z_u9_product
          (fun _ => 1) (Q delta N) (rho delta N)| ≤ delta * singularNormalization N := by
    intro delta hdelta
    filter_upwards [hscope,
      eventually_p5z_u9_productWeight_correction_of_real_modulus_scope
        scopeNu hscopeNu delta hdelta] with N hscopeN hpaidN
    intro hEven hL
    rw [← p5z_u9_switched_correction_eq_labels]
    apply hpaidN (A N) (R N) _ (fun d _ => hrho N d)
    intro d hd
    obtain ⟨hdD, hdne⟩ := Finset.mem_filter.mp hd
    have hsq := actualSmallRoughModuli_squarefree (retain N) N (cap N) _ _ hdD
    exact ⟨Nat.one_le_iff_ne_zero.mpr hsq.ne_zero, hscopeN hEven hL d hdD hdne⟩
  have hsmall : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Lic delta N →
        p5z_labelledSmallPrimeMass (p5z_u9_switchedLabels N) p5z_u9_product
          (fun _ => 1) N (z delta N) ≤ delta * singularNormalization N := by
    intro delta hdelta
    filter_upwards [p5z_eventually_u9_smallPrimeMass_le_ceil_rpow (nu * r) hnur delta hdelta]
      with N hN
    intro _hEven _hL
    rw [← p5z_u9_switched_smallPrimeMass_eq_labels]
    exact hN
  exact p5z_eventually_u9_upper_of_same_rho_label_suppliers Q rho z Lic
    currentChenUpsilon9HarmonicIntegral p5z_u9_HarmonicIntegral_nonneg
    hlic hmajor hdensityPaid hmass hPP hcop hsmall

/-- Joint full-policy specialization: select the actual attachment
precision ONCE using the actual integral/certificate density theorem.
The PP and support suppliers are then instantiated at THAT same precision,
not at independently existing rho witnesses. The full-policy limit and
certificate are genuine remaining analytic/numerical obligations. -/
theorem p5z_eventually_u9_currentK_of_actual_full_policy
    (nu r epsilonMax rawBound scopeNu : ℝ)
    (hnu : 0 < nu) (hr : 0 < r) (hnur : nu * r < 1)
    (hepsilonMax : 0 < epsilonMax) (hscopeNu : 0 ≤ scopeNu)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (integral : ℝ → ℝ) (Licensed : ℝ → ℕ → Prop)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hIntegral : ∀ e : ℝ, 0 < e → e < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd e N) N (cap N) 0 ((N : ℝ) ^ (nu * r)))
          (fixedRoughCoefficient (retainOdd e N) N (cap N) 0 ((N : ℝ) ^ (nu * r))) *
            Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
        (nhds (integral e)))
    (hCertificate : ∀ e : ℝ, 0 < e → e < epsilonMax → integral e ≤ rawBound)
    (hgap : rawBound < currentK)
    (hlicensed : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∀ᶠ N : ℕ in atTop, Even N → Licensed e N)
    (hscope : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∀ᶠ N : ℕ in atTop, Even N → Licensed e N → ∀ d : ℕ,
        d ∈ attachedUpperModuli nu r e (retainOdd e) cap N →
        attachedUpperCoefficient nu r e (retainOdd e) cap N d ≠ 0 →
          (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hbranches : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
        Even N → Licensed e N →
          |Part3.primeProductSignedError 3 N N
            (attachedUpperModuli nu r e (retainOdd e) cap N)
            (attachedUpperCoefficient nu r e (retainOdd e) cap N)
            (p5z_u9_orderedPhysicalWeight j N)| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤
        (currentK * currentChenUpsilon9HarmonicIntegral + eta) * singularNormalization N := by
  have hcapFiltered : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) := by
    rw [Filter.eventually_inf_principal]
    filter_upwards [hcap] with N hN
    intro hposEven
    exact hN hposEven.2
  obtain ⟨e, he, he8, heMax, heR, N₀, hN₀, hdensity⟩ :=
    exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits
      nu r epsilonMax rawBound hnu hr hepsilonMax retainOdd cap integral
      hcapFiltered hIntegral hCertificate hgap
  have hcapFixed : ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) := by
    filter_upwards [hcap] with N hN
    exact fun hEven _ => hN hEven
  have hdensityFixed : ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
      physicalDensitySum (attachedUpperModuli nu r e (retainOdd e) cap N)
        (attachedUpperCoefficient nu r e (retainOdd e) cap N) ≤
          currentK * (singularSeries N / Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    intro hEven _hL
    exact hdensity N hN hEven
  exact p5z_eventually_u9_currentK_of_fixed_actual_rho
    nu r e scopeNu hnu he he8 heR hnur hscopeNu (retainOdd e) cap (Licensed e)
    (hlicensed e he he8 heMax heR) hcapFixed (hscope e he he8 heMax heR)
    hdensityFixed (hbranches e he he8 heMax heR)
end

end ImbalancedChen


