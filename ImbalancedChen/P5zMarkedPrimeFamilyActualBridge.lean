import ImbalancedChen.P5zMarkedPrimeFamilyCorrections
import ImbalancedChen.P5zUpsilon9ActualRawRoute

/-! SOURCE ONLY / UNCOMPILED. General section-7.4 U* for one literal raw
same-policy coefficient, now with marked-family correction and small-prime
suppliers discharged. Normal source mass J>=0 is the legitimate remaining
source premise; U* itself is never an input. The tuple ambient type depends
on N, so the proof uses the finite theorem separately at each N. -/
namespace ImbalancedChen
noncomputable section
open Filter
open scoped BigOperators
open Classical

/-- Arbitrary fixed-rank marked positive-family U* at one actual rho.
Prime slots may repeat; all tuple labels remain. J=0 and B=0 are included
without division by either parameter. -/
theorem p5z_eventually_markedFamily_upper_of_actual_rho
    (rank : ℕ) (hrank : 1 ≤ rank)
    (S : (N : ℕ) → Finset (Fin rank → Fin (N + 1)))
    (W : (N : ℕ) → (Fin rank → Fin (N + 1)) → ℝ)
    (hS : ∀ N, S N ⊆ Part3.labelledPrimeTuples rank N)
    (B J a : ℝ) (hB : 0 ≤ B) (hJ : 0 ≤ J) (ha : 0 < a)
    (hW : ∀ N, ∀ t ∈ S N, 0 ≤ W N t ∧ W N t ≤ B)
    (hsourceCap : ∀ N, ∀ t ∈ S N, Part3.labelledProduct t ≤ N)
    (hrough : ∀ᶠ N : ℕ in atTop, Even N → ∀ t ∈ S N, ∀ i,
      (N : ℝ) ^ a ≤ ((t i).val : ℝ))
    (hmass : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledMass (S N) (W N) ≤ (J + eta) * ((N : ℝ) / Real.log (N : ℝ)))
    (nu r e scopeNu : ℝ) (hnu : 0 < nu) (he : 0 < e) (he8 : e < 1 / 8)
    (heR : e ^ 2 ≤ r) (hnur : nu * r < 1) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hlicensed : ∀ᶠ N : ℕ in atTop, Even N → Licensed N)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 → (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hdensity : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      physicalDensitySum (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) ≤
          currentK * (singularSeries N / Real.log (N : ℝ)))
    (hPP : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError rank N N (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) (p5z_markedPhysicalWeight (S N) (W N))| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledPrimeMass (S N) Part3.labelledProduct (W N) N ≤
        (currentK * J + eta) * singularNormalization N := by
  intro eta heta
  have hK : 0 ≤ currentK := by norm_num [currentK]
  let tau := eta / (currentK + 3)
  have htau : 0 < tau := div_pos heta (by linarith only [hK])
  have hbudget : (currentK + 3) * tau = eta := by
    dsimp [tau]
    field_simp [show currentK + 3 ≠ 0 by linarith only [hK]] <;> ring
  let R := attachedUpperCoefficient nu r e retain cap
  let A := fun N => p5z_activeModuli (attachedUpperModuli nu r e retain cap N) (R N)
  let Z := fun N : ℕ => Nat.ceil ((N : ℝ) ^ (nu * r))
  obtain ⟨C, _hC, hPPraw⟩ := hPP
  have hcorrection := p5z_eventually_marked_correction_le S W hS
    (fun N t ht => (hW N t ht).1) a scopeNu 1 J ha hscopeNu (by norm_num) hJ hrough hmass tau htau
  have hsmall := p5z_eventually_marked_smallPrimeMass_le_ceil S W hS B hB
    (fun N t ht => (hW N t ht).2) hsourceCap (nu * r) hnur tau htau
  filter_upwards [hlicensed, hcap, hscope, hdensity, hPPraw,
    p5z_eventually_logCube_le_singularNormalization C tau htau,
    hcorrection, hsmall, hmass tau htau, eventually_ge_atTop (2 : ℕ)]
    with N hLN hcapN hscopeN hdN hPPN hPPpaidN hcopN hsmallN hmassN hN
  intro hEven
  have hL := hLN hEven
  have hrho (d : ℕ) : |R N d| ≤ 1 :=
    actualSmallRoughRho_abs_le_one (retain N) N (cap N) _ _ _ d
  have hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N (Z N)) then (1 : ℝ) else 0) ≤
        physicalDivisorSum (A N) (R N) n := by
    intro n
    dsimp only [A]
    rw [p5z_active_physicalDivisorSum]
    exact attachedUpperCoefficient_majorant hnu he (by linarith only [he8]) heR
      retain cap hN (hcapN hEven hL) n
  have hD : A N ⊆ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ scopeNu)) := by
    intro d hd
    obtain ⟨hdD, hdne⟩ := Finset.mem_filter.mp hd
    have hsq := actualSmallRoughModuli_squarefree (retain N) N (cap N) _ _ hdD
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hsq.ne_zero,
      Nat.le_floor (hscopeN hEven hL d hdD hdne)⟩
  have hc := hcopN hEven (A N) (Nat.floor ((N : ℝ) ^ scopeNu)) (R N) hD
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) (fun d _ => hrho d)
  have hp : |p5z_labelledDistributionError (S N) Part3.labelledProduct (W N)
      N (A N) (R N)| ≤ tau * singularNormalization N := by
    have hraw : |p5z_labelledDistributionError (S N) Part3.labelledProduct (W N)
        N (A N) (R N)| ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
      rw [p5z_markedDistribution_eq_physicalPP (S N) (hS N) (W N)]
      dsimp only [A]
      rw [p5z_active_primeProductSignedError]
      exact hPPN hEven hL
    exact hraw.trans hPPpaidN
  have hdensityA : physicalDensitySum (A N) (R N) ≤
      currentK * (singularSeries N / Real.log (N : ℝ)) := by
    dsimp only [A]
    rw [p5z_active_physicalDensitySum]
    exact hdN hEven hL
  have hmass0 : 0 ≤ p5z_labelledMass (S N) (W N) :=
    Finset.sum_nonneg (fun t ht => (hW N t ht).1)
  have hmain : p5z_labelledMass (S N) (W N) * physicalDensitySum (A N) (R N) ≤
      (currentK * (J + tau)) * singularNormalization N := by
    calc
      _ ≤ p5z_labelledMass (S N) (W N) *
          (currentK * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hdensityA hmass0
      _ ≤ ((J + tau) * ((N : ℝ) / Real.log (N : ℝ))) *
          (currentK * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right (hmassN hEven) (mul_nonneg hK (densityScale_pos hN).le)
      _ = (currentK * (J + tau)) * singularNormalization N := by
        rw [← sourceMassScale_mul_densityScale N]
        ring
  have hfinite := p5z_labelledPrimeMass_le_main_add_errors (S N) Part3.labelledProduct (W N)
    N (Z N) (A N) (R N) (fun t ht => (hW N t ht).1) (hsourceCap N) hmajor
  have hcUpper := (le_abs_self _).trans hc
  have hpUpper := (le_abs_self _).trans hp
  change p5z_labelledSmallPrimeMass (S N) Part3.labelledProduct (W N) N (Z N) ≤
    tau * singularNormalization N at hsmallN
  have hbudgetH := congrArg (fun x : ℝ => x * singularNormalization N) hbudget
  nlinarith only [hfinite, hmain, hcUpper, hpUpper, hsmallN, hbudgetH]

end
end ImbalancedChen

