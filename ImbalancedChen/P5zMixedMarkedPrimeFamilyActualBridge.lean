import ImbalancedChen.P5zMarkedPrimeFamilyVariableDensity

/-! SOURCE ONLY / UNCOMPILED. Two marked ranks, ONE normal source mass J,
ONE actual rho. The leading coefficient is k*J, including J=0. Separate
branch mass bounds are derived only to pay corrections; no J3/J4 exist. -/
namespace ImbalancedChen
noncomputable section
open Filter
open scoped BigOperators
open Classical

/-- A mixed-rank positive-family bridge. Distribution cancellation is kept:
the only PP supplier bounds the signed sum before taking its norm. -/
theorem p5z_eventually_mixedMarkedFamily_upper_of_actual_rho
    (k : ℝ) (hk : 0 ≤ k) (p q : ℕ)
    (S : (N : ℕ) → Finset (Fin p → Fin (N + 1)))
    (T : (N : ℕ) → Finset (Fin q → Fin (N + 1)))
    (W : (N : ℕ) → (Fin p → Fin (N + 1)) → ℝ)
    (V : (N : ℕ) → (Fin q → Fin (N + 1)) → ℝ)
    (hS : ∀ N, S N ⊆ Part3.labelledPrimeTuples p N)
    (hT : ∀ N, T N ⊆ Part3.labelledPrimeTuples q N)
    (B J a : ℝ) (hB : 0 ≤ B) (hJ : 0 ≤ J) (ha : 0 < a)
    (hW : ∀ N, ∀ t ∈ S N, 0 ≤ W N t ∧ W N t ≤ B)
    (hV : ∀ N, ∀ t ∈ T N, 0 ≤ V N t ∧ V N t ≤ B)
    (hcapS : ∀ N, ∀ t ∈ S N, Part3.labelledProduct t ≤ N)
    (hcapT : ∀ N, ∀ t ∈ T N, Part3.labelledProduct t ≤ N)
    (hroughS : ∀ᶠ N : ℕ in atTop, Even N → ∀ t ∈ S N, ∀ i,
      (N : ℝ) ^ a ≤ ((t i).val : ℝ))
    (hroughT : ∀ᶠ N : ℕ in atTop, Even N → ∀ t ∈ T N, ∀ i,
      (N : ℝ) ^ a ≤ ((t i).val : ℝ))
    (hmass : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledMass (S N) (W N) + p5z_labelledMass (T N) (V N) ≤
        (J + eta) * ((N : ℝ) / Real.log (N : ℝ)))
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
        (attachedUpperCoefficient nu r e retain cap N) ≤ k * (singularSeries N / Real.log (N : ℝ)))
    (hPP : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError p N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (p5z_markedPhysicalWeight (S N) (W N)) +
        Part3.primeProductSignedError q N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (p5z_markedPhysicalWeight (T N) (V N))| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledPrimeMass (S N) Part3.labelledProduct (W N) N +
        p5z_labelledPrimeMass (T N) Part3.labelledProduct (V N) N ≤
          (k * J + eta) * singularNormalization N := by
  have hmS0 (N : ℕ) : 0 ≤ p5z_labelledMass (S N) (W N) :=
    Finset.sum_nonneg (fun t ht => (hW N t ht).1)
  have hmT0 (N : ℕ) : 0 ≤ p5z_labelledMass (T N) (V N) :=
    Finset.sum_nonneg (fun t ht => (hV N t ht).1)
  have hmassS : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledMass (S N) (W N) ≤ (J + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro eta heta
    filter_upwards [hmass eta heta] with N hN
    intro hEven
    exact (le_add_of_nonneg_right (hmT0 N)).trans (hN hEven)
  have hmassT : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledMass (T N) (V N) ≤ (J + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro eta heta
    filter_upwards [hmass eta heta] with N hN
    intro hEven
    exact (le_add_of_nonneg_left (hmS0 N)).trans (hN hEven)
  intro eta heta
  let tau := eta / (k + 5)
  have htau : 0 < tau := div_pos heta (by linarith only [hk])
  have hbudget : (k + 5) * tau = eta := by
    dsimp [tau]
    field_simp [show k + 5 ≠ 0 by linarith only [hk]] <;> ring
  let R := attachedUpperCoefficient nu r e retain cap
  let A := fun N => p5z_activeModuli (attachedUpperModuli nu r e retain cap N) (R N)
  let Z := fun N : ℕ => Nat.ceil ((N : ℝ) ^ (nu * r))
  obtain ⟨C, _hC, hPPraw⟩ := hPP
  have hcopS := p5z_eventually_marked_correction_le S W hS
    (fun N t ht => (hW N t ht).1) a scopeNu 1 J ha hscopeNu (by norm_num) hJ hroughS hmassS tau htau
  have hcopT := p5z_eventually_marked_correction_le T V hT
    (fun N t ht => (hV N t ht).1) a scopeNu 1 J ha hscopeNu (by norm_num) hJ hroughT hmassT tau htau
  have hsmallS := p5z_eventually_marked_smallPrimeMass_le_ceil S W hS B hB
    (fun N t ht => (hW N t ht).2) hcapS (nu * r) hnur tau htau
  have hsmallT := p5z_eventually_marked_smallPrimeMass_le_ceil T V hT B hB
    (fun N t ht => (hV N t ht).2) hcapT (nu * r) hnur tau htau
  filter_upwards [hlicensed, hcap, hscope, hdensity, hPPraw,
    p5z_eventually_logCube_le_singularNormalization C tau htau,
    hcopS, hcopT, hsmallS, hsmallT, hmass tau htau, eventually_ge_atTop (2 : ℕ)]
    with N hLN hcapN hscopeN hdN hPPN hPPpaidN hcSN hcTN hsSN hsTN hmassN hN
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
  have hcS := hcSN hEven (A N) (Nat.floor ((N : ℝ) ^ scopeNu)) (R N) hD
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) (fun d _ => hrho d)
  have hcT := hcTN hEven (A N) (Nat.floor ((N : ℝ) ^ scopeNu)) (R N) hD
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) (fun d _ => hrho d)
  have hp : |p5z_labelledDistributionError (S N) Part3.labelledProduct (W N) N (A N) (R N) +
      p5z_labelledDistributionError (T N) Part3.labelledProduct (V N) N (A N) (R N)| ≤
        tau * singularNormalization N := by
    have hraw : |p5z_labelledDistributionError (S N) Part3.labelledProduct (W N) N (A N) (R N) +
        p5z_labelledDistributionError (T N) Part3.labelledProduct (V N) N (A N) (R N)| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
      rw [p5z_markedDistribution_eq_physicalPP (S N) (hS N) (W N),
        p5z_markedDistribution_eq_physicalPP (T N) (hT N) (V N)]
      dsimp only [A]
      rw [p5z_active_primeProductSignedError, p5z_active_primeProductSignedError]
      exact hPPN hEven hL
    exact hraw.trans hPPpaidN
  have hdA : physicalDensitySum (A N) (R N) ≤ k * (singularSeries N / Real.log (N : ℝ)) := by
    dsimp only [A]
    rw [p5z_active_physicalDensitySum]
    exact hdN hEven hL
  have hmain : (p5z_labelledMass (S N) (W N) + p5z_labelledMass (T N) (V N)) *
      physicalDensitySum (A N) (R N) ≤ (k * (J + tau)) * singularNormalization N := by
    calc
      _ ≤ (p5z_labelledMass (S N) (W N) + p5z_labelledMass (T N) (V N)) *
          (k * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hdA (add_nonneg (hmS0 N) (hmT0 N))
      _ ≤ ((J + tau) * ((N : ℝ) / Real.log (N : ℝ))) *
          (k * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right (hmassN hEven) (mul_nonneg hk (densityScale_pos hN).le)
      _ = (k * (J + tau)) * singularNormalization N := by
        rw [← sourceMassScale_mul_densityScale N]
        ring
  have hfS := p5z_labelledPrimeMass_le_main_add_errors (S N) Part3.labelledProduct (W N)
    N (Z N) (A N) (R N) (fun t ht => (hW N t ht).1) (hcapS N) hmajor
  have hfT := p5z_labelledPrimeMass_le_main_add_errors (T N) Part3.labelledProduct (V N)
    N (Z N) (A N) (R N) (fun t ht => (hV N t ht).1) (hcapT N) hmajor
  have hcSU := (le_abs_self _).trans hcS
  have hcTU := (le_abs_self _).trans hcT
  have hpU := (le_abs_self _).trans hp
  change p5z_labelledSmallPrimeMass (S N) Part3.labelledProduct (W N) N (Z N) ≤
    tau * singularNormalization N at hsSN
  change p5z_labelledSmallPrimeMass (T N) Part3.labelledProduct (V N) N (Z N) ≤
    tau * singularNormalization N at hsTN
  have hbH := congrArg (fun x : ℝ => x * singularNormalization N) hbudget
  have hmain' : p5z_labelledMass (S N) (W N) * physicalDensitySum (A N) (R N) +
      p5z_labelledMass (T N) (V N) * physicalDensitySum (A N) (R N) ≤
        (k * (J + tau)) * singularNormalization N := by
    simpa only [add_mul] using hmain
  nlinarith only [hfS, hfT, hmain', hcSU, hcTU, hpU, hsSN, hsTN, hbH]

end
end ImbalancedChen
