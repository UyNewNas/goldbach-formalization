import ImbalancedChen.P4BOriginalFineAttachedRetained
import ImbalancedChen.P5U7OriginalSourceSuppliedRoute
import ImbalancedChen.P5zUpsilon8OriginalSlot
import ImbalancedChen.P5zUpsilon9OriginalSlot

/-! The six physical tests in U7/U8/U9 share one actual Fine selection.  We
keep their signed discrepancy in the conclusion, so every remaining
hypothesis of the marked-family argument can be supplied at this stage. -/
namespace ImbalancedChen.P5OriginalFineSwitchedCosts

noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalFineAttachedUpper (Selection retention)
open P5U7OriginalPhysicalPP (weight3 weight4)
open P5U8SharpKSource (physicalWeight)

variable {m r n q : ℕ} {e : ℚ} {a nu v etaPP betaMax extra : ℝ} {ft : ℝ → ℝ}

abbrev family (s : Selection m r n e q a nu v etaPP betaMax extra ft) :=
  attachedUpperModuli nu v s.beta (retention m r n e q a (nu * s.beta ^ 2)) id
abbrev coefficient (s : Selection m r n e q a nu v etaPP betaMax extra ft) :=
  attachedUpperCoefficient nu v s.beta (retention m r n e q a (nu * s.beta ^ 2)) id
abbrev active (s : Selection m r n e q a nu v etaPP betaMax extra ft) (N : ℕ) :=
  p5z_activeModuli (family s N) (coefficient s N)
abbrev error (s : Selection m r n e q a nu v etaPP betaMax extra ft) (d N : ℕ)
    (W : (Fin d → Fin (N + 1)) → ℝ) :=
  Part3.primeProductSignedError d N N (family s N) (coefficient s N) W

theorem physical_receipt (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) (hnu : 0 < nu) (hcut : nu * v = 19 / 96) {N : ℕ} (hN : 2 ≤ N) :
    (∀ d ∈ active s N, 1 ≤ d ∧ (d : ℝ) ≤ (N : ℝ) ^ (599 / 1000 : ℝ)) ∧
    (∀ d : ℕ, |coefficient s N d| ≤ 1) ∧
    ∀ l : ℕ, (if Nat.Coprime l (sieveProduct N (Nat.ceil ((N : ℝ) ^ (nu * v))))
      then (1 : ℝ) else 0) ≤ physicalDivisorSum (active s N) (coefficient s N) l := by
  let f := retention m r n e q a (nu * s.beta ^ 2)
  refine ⟨?_, fun d => actualSmallRoughRho_abs_le_one (f N) N N _ _ _ d, ?_⟩
  · intro d hd
    obtain ⟨hq, hne⟩ := Finset.mem_filter.mp hd
    have hsq := actualSmallRoughModuli_squarefree (f N) N N _ _ hq
    exact ⟨Nat.one_le_iff_ne_zero.mpr hsq.ne_zero,
      (P4BOriginalFineAttachedRetained.attached_support s he hnu hN hne).le⟩
  · intro l
    rw [active, p5z_active_physicalDivisorSum]
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hz : (N:ℝ)^(nu*v) ≤ (N:ℝ) := by
      rw [hcut]
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (19 / 96 : ℝ) ≤ 1)
    exact attachedUpperCoefficient_majorant hnu s.pos (by linarith only [s.lt_eighth])
      s.square_lt.le f id hN hz l

private theorem marked_receipt (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) (hnu : 0 < nu) (hcut : nu * v = 19 / 96) {d : ℕ}
    (S : (N : ℕ) → Finset (Fin d → Fin (N+1)))
    (W : (N : ℕ) → (Fin d → Fin (N+1)) → ℝ)
    (hS : ∀ N, S N ⊆ Part3.labelledPrimeTuples d N)
    (hW : ∀ N, ∀ u ∈ S N, 0 ≤ W N u ∧ W N u ≤ 1)
    (hcap : ∀ N, ∀ u ∈ S N, Part3.labelledProduct u ≤ N)
    (g J : ℝ) (hg : 0 < g) (hJ : 0 ≤ J)
    (hrough : ∀ᶠ N : ℕ in atTop, Even N → ∀ u ∈ S N, ∀ i, (N : ℝ)^g ≤ ((u i).val : ℝ))
    (hm : ∀ t : ℝ, 0 < t → ∀ᶠ N : ℕ in atTop, Even N → p5z_labelledMass (S N) (W N) ≤
      (J+t)*((N : ℝ)/Real.log (N : ℝ))) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledPrimeMass (S N) Part3.labelledProduct (W N) N ≤
        p5z_labelledMass (S N) (W N) * (currentK * (singularSeries N / Real.log (N : ℝ))) +
          error s d N (p5z_markedPhysicalWeight (S N) (W N)) + δ * singularNormalization N := by
  have hc := p5z_eventually_marked_correction_le S W hS (fun N u h => (hW N u h).1)
    g (599/1000) 1 J hg (by norm_num) (by norm_num) hJ hrough hm (δ/2) (half_pos hδ)
  have hz := p5z_eventually_marked_smallPrimeMass_le_ceil S W hS 1 (by norm_num)
    (fun N u h => (hW N u h).2) hcap (nu*v) (by rw [hcut]; norm_num) (δ/2) (half_pos hδ)
  filter_upwards [hc, hz, s.attached_K, eventually_ge_atTop (2 : ℕ)] with N hcN hzN hdN hN
  intro hev
  obtain ⟨hs, hrho, hmaj⟩ := physical_receipt s he hnu hcut hN
  let Q := Nat.floor ((N : ℝ) ^ (599 / 1000 : ℝ))
  have hsub : active s N ⊆ Finset.Icc 1 Q := fun x hx =>
    Finset.mem_Icc.mpr ⟨(hs x hx).1, Nat.le_floor (hs x hx).2⟩
  have hcop := hcN hev (active s N) Q (coefficient s N) hsub
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) (fun x _ => hrho x)
  have hf := p5z_labelledPrimeMass_le_main_add_errors (S N) Part3.labelledProduct (W N) N
    (Nat.ceil ((N : ℝ) ^ (nu*v))) (active s N) (coefficient s N)
    (fun u h => (hW N u h).1) (hcap N) hmaj
  rw [p5z_markedDistribution_eq_physicalPP (S N) (hS N) (W N)] at hf
  simp only [active,p5z_active_primeProductSignedError,p5z_active_physicalDensitySum] at hf
  have hmass0 : 0 ≤ p5z_labelledMass (S N) (W N) :=
    Finset.sum_nonneg (fun u hu => (hW N u hu).1)
  have hmD := mul_le_mul_of_nonneg_left (hdN hev) hmass0
  change p5z_labelledMass (S N) (W N) * physicalDensitySum (family s N) (coefficient s N) ≤ _ at hmD
  dsimp only [error, active] at hcop ⊢
  linarith only [hf, hmD, (le_abs_self _).trans hcop, hzN]

private theorem price_mass {N : ℕ} (hN : 2 ≤ N) {M J δ : ℝ}
    (hm : M ≤ (J+δ)*((N : ℝ)/Real.log (N : ℝ))) :
    M*(currentK*(singularSeries N/Real.log (N : ℝ))) ≤
      (currentK*(J+δ))*singularNormalization N := by
  have hk : 0 ≤ currentK := by norm_num [currentK]
  calc
    _ ≤ ((J+δ)*((N : ℝ)/Real.log (N : ℝ)))*(currentK*(singularSeries N/Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_right hm (mul_nonneg hk (densityScale_pos hN).le)
    _ = _ := by rw [← sourceMassScale_mul_densityScale N]; ring

abbrev seventhError (s : Selection m r n e q a nu v etaPP betaMax extra ft) (N : ℕ) :=
  error s 3 N (weight3 N) + error s 4 N (weight4 N)
abbrev eighthError (s : Selection m r n e q a nu v etaPP betaMax extra ft) (N : ℕ) :=
  error s 3 N (physicalWeight N)
abbrev ninthError (s : Selection m r n e q a nu v etaPP betaMax extra ft) (N : ℕ) :=
  error s 3 N (p5z_u9_orderedPhysicalWeight 0 N) + error s 3 N (p5z_u9_orderedPhysicalWeight 1 N) +
    error s 3 N (p5z_u9_orderedPhysicalWeight 2 N)

theorem seventh_with_signed_error (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) (hnu : 0 < nu) (hcut : nu*v = 19/96) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Even N → currentChenUpsilon7 N ≤
      (currentK * p5U7OriginalOmegaIntegral 1 + δ)*singularNormalization N + seventhError s N := by
  let J := p5U7OriginalOmegaIntegral 1
  have hJ : 0 ≤ J := p5U7OriginalOmegaIntegral_nonneg (by norm_num)
  have hW3 (N : ℕ) (u : Fin 3 → Fin (N+1)) : 0 ≤ weight3 N u ∧ weight3 N u ≤ 1 := by
    rcases P5U7OriginalPhysicalPP.weight3_zero_or_one N u with h | h <;> rw [h] <;> norm_num
  have hW4 (N : ℕ) (u : Fin 4 → Fin (N+1)) : 0 ≤ weight4 N u ∧ weight4 N u ≤ 1 := by
    rcases P5U7OriginalPhysicalPP.weight4_zero_or_one N u with h | h <;> rw [h] <;> norm_num
  have hmass (t : ℝ) (ht : 0 < t) : ∀ᶠ N : ℕ in atTop,
      p5z_labelledMass (p5z_u7Source3 N) (weight3 N) + p5z_labelledMass (p5z_u7Source4 N) (weight4 N) ≤
        (J+t)*((N : ℝ)/Real.log (N : ℝ)) := by
    simpa only [p5z_u7_combinedMarked_mass_eq, J] using p5U7Original_eventually_arithmetic_mass_le_integral t ht
  let τ := δ / (currentK+3)
  have hτ : 0 < τ := div_pos hδ (by norm_num [currentK])
  have hbudget : (currentK+3)*τ = δ := by dsimp [τ]; field_simp [show currentK+3≠0 by norm_num [currentK]] <;> ring
  have hmass3 (t : ℝ) (ht : 0 < t) : ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledMass (p5z_u7Source3 N) (weight3 N) ≤ (J+t)*((N : ℝ)/Real.log (N : ℝ)) := by
    filter_upwards [hmass t ht] with N hm
    intro _
    exact (le_add_of_nonneg_right (show 0 ≤ p5z_labelledMass (p5z_u7Source4 N) (weight4 N) from
      Finset.sum_nonneg (fun u _ => (hW4 N u).1))).trans hm
  have hmass4 (t : ℝ) (ht : 0 < t) : ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledMass (p5z_u7Source4 N) (weight4 N) ≤ (J+t)*((N : ℝ)/Real.log (N : ℝ)) := by
    filter_upwards [hmass t ht] with N hm
    intro _
    exact (le_add_of_nonneg_left (show 0 ≤ p5z_labelledMass (p5z_u7Source3 N) (weight3 N) from
      Finset.sum_nonneg (fun u _ => (hW3 N u).1))).trans hm
  have h3 := marked_receipt s he hnu hcut p5z_u7Source3 weight3
    (fun N => p5z_u7MarkedSource_subset 3 N (weight3 N)) (fun N u _ => hW3 N u)
    (fun _ _ hu => (P5U7OriginalPhysicalPP.weight3_sorted_primitive (Finset.mem_filter.mp hu).2).2.2.1.le)
    (59/250) J (by norm_num) hJ (Filter.Eventually.of_forall (fun _ _ _ hu =>
      P5U7OriginalPhysicalPP.weight3_lower_power (Finset.mem_filter.mp hu).2)) hmass3 hτ
  have h4 := marked_receipt s he hnu hcut p5z_u7Source4 weight4
    (fun N => p5z_u7MarkedSource_subset 4 N (weight4 N)) (fun N u _ => hW4 N u)
    (fun _ _ hu => (P5U7OriginalPhysicalPP.weight4_sorted_primitive (Finset.mem_filter.mp hu).2).2.2.2.1.le)
    (59/250) J (by norm_num) hJ (Filter.Eventually.of_forall (fun _ _ _ hu =>
      P5U7OriginalPhysicalPP.weight4_lower_power (Finset.mem_filter.mp hu).2)) hmass4 hτ
  filter_upwards [h3, h4, hmass τ hτ, p5U7Arithmetic_eventually_error_budget τ hτ,
    eventually_ge_atTop (2 : ℕ)] with N h3N h4N hm hu hN
  intro hev
  have h3' := h3N hev
  have h4' := h4N hev
  change _ ≤ _ + Part3.primeProductSignedError 3 N N _ _
    (p5z_markedPhysicalWeight (p5z_u7MarkedSource 3 N (weight3 N)) (weight3 N)) + _ at h3'
  change _ ≤ _ + Part3.primeProductSignedError 4 N N _ _
    (p5z_markedPhysicalWeight (p5z_u7MarkedSource 4 N (weight4 N)) (weight4 N)) + _ at h4'
  rw [p5z_u7MarkedPhysicalPP_eq] at h3' h4'
  have hmD := price_mass hN hm
  have hunit : ((currentChenUpsilon7UnitFibres N).card : ℝ) ≤ τ * singularNormalization N := by
    unfold p5U7ArithmeticSmallUnitError at hu
    have hp0 : (0 : ℝ) ≤ (((currentChenUpsilon7PrimeTriples N).filter (fun x =>
      ((N-p5U7ThreeProduct x : ℕ) : ℝ) ≤ (N : ℝ)^(1/5 : ℝ))).card : ℝ) := Nat.cast_nonneg _
    have hs0 : (0 : ℝ) ≤ (((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x =>
      ((N-p5U7FourProduct x : ℕ) : ℝ) ≤ (N : ℝ)^(1/5 : ℝ))).card : ℝ) := Nat.cast_nonneg _
    linarith only [hu, hp0, hs0, (Nat.cast_nonneg (α:=ℝ) (currentChenUpsilon7UnitFibres N).card)]
  rw [p5z_u7_eq_mixedMarkedPrimeMass_add_units]
  dsimp only [seventhError, error]
  dsimp only [J] at hmD
  nlinarith only [h3', h4', hmD, hunit, congrArg (fun x : ℝ => x * singularNormalization N) hbudget]

theorem eighth_with_signed_error (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) (hnu : 0 < nu) (hcut : nu*v = 19/96) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Even N → currentChenUpsilon8 N ≤
      (currentK * currentChenUpsilon8HarmonicIntegral + δ)*singularNormalization N + eighthError s N := by
  have hmass (t : ℝ) (ht : 0 < t) : ∀ᶠ N : ℕ in atTop, p5z_labelledMass (p5z_u8MarkedSource N)
      (physicalWeight N) ≤ (currentChenUpsilon8HarmonicIntegral+t)*((N : ℝ)/Real.log (N : ℝ)) := by
    simpa only [p5z_u8Marked_mass_eq_card] using
      P5U8SharpKSourceMassSourceOnly.eventually_arithmeticTriples_mass_le_harmonicIntegral t ht
  let τ := δ / (currentK+2)
  have hτ : 0 < τ := div_pos hδ (by norm_num [currentK])
  have hbudget : (currentK+2)*τ = δ := by dsimp [τ]; field_simp [show currentK+2≠0 by norm_num [currentK]] <;> ring
  have hW (N : ℕ) (u : Fin 3 → Fin (N+1)) : 0 ≤ physicalWeight N u ∧ physicalWeight N u ≤ 1 := by
    unfold P5U8SharpKSource.physicalWeight
    split_ifs <;> norm_num
  have hp := marked_receipt s he hnu hcut p5z_u8MarkedSource physicalWeight
    p5z_u8MarkedSource_subset (fun N u _ => hW N u)
    (fun _ _ hu => (P5U8SharpKSource.physicalWeight_support_data (Finset.mem_filter.mp hu).2).2.2.1.le)
    (417/5000) currentChenUpsilon8HarmonicIntegral (by norm_num)
    P5U8LiteralPrimeFibreMassSourceOnly.harmonicIntegral_nonneg
    (Filter.Eventually.of_forall (fun _ _ _ hu => P5U8SharpKSource.physicalWeight_lower_power
      (Finset.mem_filter.mp hu).2)) (fun t ht => (hmass t ht).mono (fun _ h _ => h)) hτ
  filter_upwards [hp, hmass τ hτ, P5U8SharpKSource.eventually_units_add_diagonal_negligible τ hτ,
    eventually_ge_atTop (2 : ℕ)] with N hpN hm hu hN
  intro hev
  have hp' := hpN hev
  dsimp only [error] at hp'
  rw [p5z_u8_markedPhysicalPP_eq] at hp'
  have hd : (0 : ℝ) ≤ (P5U8SharpKSource.diagonalTriples N).card := Nat.cast_nonneg _
  rw [p5z_u8_eq_markedPrimeMass_add_units]
  dsimp only [eighthError, error]
  nlinarith only [hp', hu, hd, price_mass hN hm, congrArg (fun x : ℝ => x * singularNormalization N) hbudget]

theorem ninth_with_signed_error (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) (hnu : 0 < nu) (hcut : nu*v = 19/96) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Even N → currentChenUpsilon9 N ≤
      (currentK * currentChenUpsilon9HarmonicIntegral + δ)*singularNormalization N + ninthError s N := by
  let τ := δ / (currentK+3)
  have hτ : 0 < τ := div_pos hδ (by norm_num [currentK])
  have hbudget : (currentK+3)*τ = δ := by dsimp [τ]; field_simp [show currentK+3≠0 by norm_num [currentK]] <;> ring
  filter_upwards [s.attached_K, eventually_p5z_u9_productWeight_correction_of_real_modulus_scope
    (599/1000) (by norm_num) τ hτ, p5z_eventually_u9_smallPrimeMass_le_ceil_rpow (nu*v)
    (by rw [hcut]; norm_num) τ hτ, p5z_eventually_u9_switchedWeight_mass_le_harmonicIntegral τ hτ,
    eventually_currentChenUpsilon9_unitFibres_le_singularNormalization τ hτ, eventually_ge_atTop (2 : ℕ)]
    with N hD hc hz hm hu hN
  intro hev
  obtain ⟨hs, hrho, hmaj⟩ := physical_receipt s he hnu hcut hN
  have hcop := hc (active s N) (coefficient s N) hs (fun x _ => hrho x)
  have hf := p5z_u9_le_same_rho_main_add_errors N (Nat.ceil ((N : ℝ)^(nu*v))) (active s N)
    (coefficient s N) hmaj
  rw [p5z_u9_switched_distribution_eq_labels, p5z_u9_orderedPhysicalPP_decomposition] at hf
  simp only [active, p5z_active_primeProductSignedError, p5z_active_physicalDensitySum] at hf hcop
  have hmass0 : 0 ≤ p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) :=
    Finset.sum_nonneg (fun u _ => p5z_u9_switchedWeight_nonneg N u)
  have hmD := mul_le_mul_of_nonneg_left (hD hev) hmass0
  change p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) *
    physicalDensitySum (family s N) (coefficient s N) ≤ _ at hmD
  dsimp only [ninthError, error]
  nlinarith only [hf, hmD, price_mass hN hm, (le_abs_self _).trans hcop, hz, hu,
    congrArg (fun x : ℝ => x * singularNormalization N) hbudget]

/-- Independent tolerances are fixed before a single even target. The
leading seventh mass prices the sum of the two ranks only once. -/
theorem three_costs (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) (hnu : 0 < nu) (hcut : nu*v = 19/96) {δ7 δ8 δ9 : ℝ}
    (h7 : 0 < δ7) (h8 : 0 < δ8) (h9 : 0 < δ9) :
    ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon7 N ≤ (currentK*p5U7OriginalOmegaIntegral 1 + δ7)*singularNormalization N +
        seventhError s N ∧
      currentChenUpsilon8 N ≤ (currentK*currentChenUpsilon8HarmonicIntegral + δ8)*singularNormalization N +
        eighthError s N ∧
      currentChenUpsilon9 N ≤ (currentK*currentChenUpsilon9HarmonicIntegral + δ9)*singularNormalization N +
        ninthError s N := by
  filter_upwards [seventh_with_signed_error s he hnu hcut h7, eighth_with_signed_error s he hnu hcut h8,
    ninth_with_signed_error s he hnu hcut h9] with N h7N h8N h9N
  exact fun hev => ⟨h7N hev, h8N hev, h9N hev⟩

end
end ImbalancedChen.P5OriginalFineSwitchedCosts
