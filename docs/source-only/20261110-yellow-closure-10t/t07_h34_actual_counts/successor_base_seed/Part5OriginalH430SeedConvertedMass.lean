import ImbalancedChen.Part5OriginalH430SeedLastWords
import ImbalancedChen.P2EnhancedBadAndShortCostAssembly
import ImbalancedChen.P2SeedOmegaOriginalNumerical

/-! Inclusive rough-integer source for the original adopted-seed action.
The analytic threshold precedes the marked family and its physical Q. -/
namespace ImbalancedChen.Part5OriginalH430SeedConvertedMass
noncomputable section
open Real Finset Wu2008DoubleSieve
open P2SeedOmegaLiteralFibre P2SeedOmegaLiteralFunctional
open P2EnhancedSwitchedTrueNormalization P2EnhancedNonunitMarkedMass
open P2EnhancedUnitSourceMass P2SeedOmegaLastUnitIntegrals
open P2EnhancedShortWordInclusiveMass P2EnhancedBadGamma5CostTheta
open P2EnhancedBadAndShortCostAssembly Part5OriginalH430SeedLastWords
open P2OriginalChildPhysicalNormalization (Theta_eq_sum_atoms thetaAtom)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open scoped Classical BigOperators

def converted (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) : ℝ :=
  convertedBad N Q D σ + ∑ j : Fin 13,
    ((secondFunctionalMotherGammaWords (9+j.val)).map (convertedOrdinary N Q D σ)).sum

def convertedCap : ℝ := badRawCost + ∑ j : Fin 13, switchedMass j

private theorem split13 (F : Fin 13 → ℝ) :
    (∑ j : Fin 13, F j) = (∑ j : Fin 11, F ⟨j.val,by omega⟩) + F 11 + F 12 := by
  calc
    _ = (∑ j : Fin 12, F j.castSucc) + F 12 := Fin.sum_univ_castSucc F
    _ = _ := by rw [Fin.sum_univ_castSucc (fun j : Fin 12 => F j.castSucc)]; rfl

private theorem costs (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) :
    converted N Q D σ = convertedBad N Q D σ + originalShortOrdinary N Q D σ +
      convertedOrdinary N Q D σ [2,3,3,3,3] + convertedOrdinary N Q D σ [3,3,3,3,3,3] := by
  unfold converted
  rw [split13]
  change _ + ((originalShortOrdinary N Q D σ + _) + _) = _
  simp only [show secondFunctionalMotherGammaWords (9+(11 : Fin 13).val) = [[2,3,3,3,3]]
      from rfl,show secondFunctionalMotherGammaWords (9+(12 : Fin 13).val) = [[3,3,3,3,3,3]]
      from rfl,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  ring

private theorem cap_split : convertedCap = originalCost + switchedMass 11 + switchedMass 12 := by
  unfold convertedCap originalCost
  rw [split13]
  ring

private theorem sumPayload {N : ℕ} {Q : ℝ} {D : Finset ℕ} {σ : ℕ → ℝ}
    (hw : ∀ d ∈ D, 0≤σ d*thetaAtom N Q d) (F G : ℝ → ℝ) (c : ℝ)
    (hc : ∀ alpha, F alpha + G alpha ≤ c) :
    thetaPayload N Q D σ F + thetaPayload N Q D σ G ≤ c*Theta N Q D σ := by
  rw [← constant_thetaPayload N Q D σ c]
  unfold thetaPayload
  rw [← sum_add_distrib]
  exact sum_le_sum (fun d hd => by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hc _) (hw d hd))

theorem original_inclusive_converted_mass {η ε : ℝ} (hη : 0<η) (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → ∀ (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ),
      (∀ d ∈ D, 0<d) → (∀ d ∈ D, 0≤σ d) → (∀ d ∈ D, (N:ℝ)^η≤Q/d) →
      (∀ d ∈ D, 2≤trueAlpha N Q d) →
      converted N Q D σ ≤ convertedCap * Theta N Q D σ + ε * Theta N Q D σ := by
  have he4 : 0<ε/4 := by positivity
  obtain ⟨Ta,hTa,ha⟩ := original_badGamma5_Gamma9_to_19_cost_theta hη he4
  obtain ⟨Tb,hTb,hb⟩ := all_original_word_theta_upper hη (show 0<5*ε by positivity)
  obtain ⟨Tc,hTc,hc⟩ := actual_unit_theta_upper hη he4
  let T := max (max Ta Tb) Tc
  refine ⟨T,hTa.trans ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro N hN Q D σ hd hσ hr hα
  have hNa : Ta≤N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNb : Tb≤N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNc : Tc≤N := (le_max_right _ _).trans hN
  have hshort := ha N hNa Q D σ hd hσ hr hα
  have hwords := hb N hNb Q D σ hd hσ hr hα
  have h20 := hwords (11:Fin 13) [2,3,3,3,3] (by decide)
  have h21 := hwords (12:Fin 13) [3,3,3,3,3,3] (by decide)
  have hun := (hc N hNc Q D σ hd hσ hr).2.2
  have hw (d : ℕ) (hm : d ∈ D) : 0≤σ d*thetaAtom N Q d := by
    have h1 : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
    exact mul_nonneg (hσ d hm) (P2OriginalPositiveSameQMassLift.thetaAtom_nonneg
      (hTa.trans hNa) (hd d hm) ((one_lt_rpow h1 hη).trans_le (hr d hm)))
  have hc20 := sumPayload hw (nonunitIntegral [2,3,3,3,3]) unit20Mass (switchedMass 11)
    (fun α => (original_last_full_costs α).1)
  have hc21 := sumPayload hw (nonunitIntegral [3,3,3,3,3,3]) unit21Mass (switchedMass 12)
    (fun α => (original_last_full_costs α).2)
  rw [costs,convertedOrdinary_eq_unit_add_nonunit N Q D σ hd,
    convertedOrdinary_eq_unit_add_nonunit N Q D σ hd,cap_split]
  change _ + (convertedUnit20 N Q D σ + _) + (convertedUnit21 N Q D σ + _) ≤ _
  linarith only [hshort,h20,h21,hun,hc20,hc21]

def ordinaryPart : ℝ :=
  -(4*correction s0+correction phi1) + (negative b+negative a2+negative a3) -
    (ordinaryTriangle a2+ordinaryRectangle a2 a3+ordinaryTriangle a1+ordinaryRectangle a1 a2) +
    badOrdinaryDouble

theorem seed_split : actualJ2omega = (ordinaryPart - (K/4)*convertedCap)/5 := by
  unfold actualJ2omega ordinaryPart convertedCap switchCost badRawCost
  rw [← badRoughDouble_eq_original_log]
  have h : omegaCap/a0 = omegaCap*s0 := by norm_num [a0,s0]; ring
  rw [h]
  ring

/-- The original numerical surplus absorbs the positive rough-integer error
on the actual marked family, including both quotient-one charts. -/
theorem base_after_converted {η J : ℝ} (hη : 0<η) (hJ : J<actualJ2omega) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → ∀ (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ),
      (∀ d ∈ D, 0<d) → (∀ d ∈ D, 0≤σ d) → (∀ d ∈ D, (N:ℝ)^η≤Q/d) →
      (∀ d ∈ D, 2≤trueAlpha N Q d) →
      J*Theta N Q D σ ≤ (ordinaryPart*Theta N Q D σ - (K/4)*converted N Q D σ)/5 := by
  let δ := (actualJ2omega-J)*20/K
  have hδ : 0<δ := div_pos (mul_pos (sub_pos.mpr hJ) (by norm_num)) (by norm_num [K])
  obtain ⟨T,hT,h⟩ := original_inclusive_converted_mass hη hδ
  refine ⟨T,hT,?_⟩
  intro N hN Q D σ hd hσ hr hα
  have hupper := mul_le_mul_of_nonneg_left (h N hN Q D σ hd hσ hr hα)
    (by norm_num [K] : (0:ℝ)≤K/4)
  have hsplit := congrArg (fun x : ℝ => x*Theta N Q D σ) seed_split
  have heq : (K/4)*δ = 5*(actualJ2omega-J) := by dsimp [δ,K]; ring
  have hprod := congrArg (fun x : ℝ => x*Theta N Q D σ) heq
  dsimp only at hsplit hprod
  linarith only [hupper,hsplit,hprod]

theorem first_seed_after_converted {η : ℝ} (hη : 0<η) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → ∀ (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ),
      (∀ d ∈ D, 0<d) → (∀ d ∈ D, 0≤σ d) → (∀ d ∈ D, (N:ℝ)^η≤Q/d) →
      (∀ d ∈ D, 2≤trueAlpha N Q d) →
      (1/50:ℝ)*Theta N Q D σ ≤ (ordinaryPart*Theta N Q D σ -
        (K/4)*converted N Q D σ)/5 := by
  apply base_after_converted hη
  exact (show (1/50:ℝ)<20249/1000000 by norm_num).trans
    P2SeedOmegaOriginalNumerical.actualJ2omega_gt_safe_base

end
end ImbalancedChen.Part5OriginalH430SeedConvertedMass
