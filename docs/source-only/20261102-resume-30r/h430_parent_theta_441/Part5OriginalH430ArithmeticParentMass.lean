import ImbalancedChen.P2OriginalLiteralW1OldProfile

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The constant-one CLOSED table is used only to measure the actual positive
feedback row. Its lower support is still [2,5], so the row mass is bounded
by, and is not identified with, the full scalar W1/W2 mass.

The arithmetic rows retain the literal W1 d*N window, W2 N windows,
the fresh/repeated prime factors, same Q, all 401 atoms, and the exact
1/2, 4/5, 1/5 coefficients. The threshold precedes the labelled positive
parent family. No norm12, old count licence or convergence premise is used.

This file does not identify these rows with the immutable430 interpreter,
construct a moving full-Member refinement, or prove its switched bases.
-/

namespace ImbalancedChen.Part5OriginalH430ArithmeticParentMass

noncomputable section
open Set MeasureTheory Filter Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables Part5UpperTables.Renewal
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalBankThetaMassLimits P2OriginalHalfOpenProfileCarrier
open P2OriginalOldProfilePrimeLimits P2OriginalPhysicalOldProfileMass
open P2OriginalBankOldProfilePassage P2OriginalProfileThetaNormalization
open P2OriginalLiteralW1OldProfile P2OriginalPositiveSameQMassLift

/-- This array measures coefficient mass; it is not a proposed H/h seed. -/
def oneNumerators : Fin 200 → ℤ := fun _ => 2 ^ 80

theorem oneNumerators_bounded : UnitBoundedData oneNumerators := by
  intro i
  exact ⟨by dsimp [oneNumerators]; positivity, le_rfl⟩

theorem one_floorValue (i : Fin 200) : floorValue oneNumerators i = 1 := by
  simp only [floorValue, oneNumerators, Int.cast_pow, Int.cast_ofNat]
  exact div_self (by positivity)

theorem one_floorAtomValue (b : FloorAtom) : floorAtomValue oneNumerators b = 1 := by
  cases b with
  | inl i => exact one_floorValue i
  | inr j =>
      simp only [floorAtomValue, floorKnotValue]
      split_ifs <;> simp only [one_floorValue, min_self]

theorem one_table_bounds (lower : Bool) (s : ℝ) :
    0 ≤ tableFunction lower oneNumerators s ∧
      tableFunction lower oneNumerators s ≤ 1 :=
  tableFunction_bounds lower oneNumerators_bounded s

/-- The actual table support is retained in this comparison. -/
theorem singleton_unit_integral_bounds {D : Set ℝ} (hD : MeasurableSet D)
    (hsub : D ⊆ singletonAmbient) (s0 : ℝ) :
    0 ≤ (∫ u in D, tableFunction true oneNumerators (s0*(1-u))/(u*(1-u))) ∧
      (∫ u in D, tableFunction true oneNumerators (s0*(1-u))/(u*(1-u))) ≤
        singletonMass D := by
  have hk : IntegrableOn singletonKernel D :=
    (singletonKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have ht := integrableOn_weightedTable true oneNumerators
    (measurable_singletonProfile s0) hD hk
  have heq : (∫ u in D, tableFunction true oneNumerators (s0*(1-u))/(u*(1-u))) =
      ∫ u in D, weightedTable true oneNumerators (singletonProfile s0) singletonKernel u := by
    apply setIntegral_congr_fun hD
    intro u hu
    rw [weightedTable, singletonKernel_eq_raw (hsub hu)]
    dsimp [singletonProfile]
    ring
  rw [heq]
  constructor
  · exact setIntegral_nonneg hD (fun u _ =>
      (weightedTable_bounds true oneNumerators_bounded _ _ u (singletonKernel_nonneg u)).1)
  · exact setIntegral_mono_on ht hk hD (fun u _ =>
      (weightedTable_bounds true oneNumerators_bounded _ _ u (singletonKernel_nonneg u)).2)

theorem pair_unit_integral_bounds {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4) :
    0 ≤ pairOldIntegral p k oneNumerators ∧
      pairOldIntegral p k oneNumerators ≤ pairMass (W2PairDomain p k) := by
  have hD := measurableSet_W2PairDomain p k
  have hk : IntegrableOn pairKernel (W2PairDomain p k) :=
    (pairKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (W2PairDomain_subset hp k)
  have ht := integrableOn_weightedTable false oneNumerators
    (measurable_pairProfile p k) hD hk
  have heq : pairOldIntegral p k oneNumerators =
      ∫ x in W2PairDomain p k,
        weightedTable false oneNumerators (pairProfile p k) pairKernel x := by
    apply setIntegral_congr_fun hD
    intro x hx
    rw [weightedTable, pairKernel_eq_raw
      (W2PairDomain_geometry hp k hx).1 (W2PairDomain_geometry hp k hx).2]
    ring
  rw [heq]
  constructor
  · exact setIntegral_nonneg hD (fun x _ =>
      (weightedTable_bounds false oneNumerators_bounded _ _ x (pairKernel_nonneg x)).1)
  · exact setIntegral_mono_on ht hk hD (fun x _ =>
      (weightedTable_bounds false oneNumerators_bounded _ _ x (pairKernel_nonneg x)).2)

theorem W1_unit_integral_bounds (i : Fin 7) (j : Fin 10) :
    0 ≤ W1OldIntegral i j oneNumerators oneNumerators ∧
      W1OldIntegral i j oneNumerators oneNumerators ≤ (5/2:ℝ) := by
  have ht := one_table_bounds false (W1Anchor j)
  have hs := singleton_unit_integral_bounds measurableSet_Ioo
    (W1Domain_subset i j) (W1Anchor j)
  have hm := singletonMass_le_three (W1Domain_subset i j)
  change 0 ≤ singleOldIntegral (1/W1Anchor j) (1/W1Target i) (W1Anchor j) oneNumerators ∧
      singleOldIntegral (1/W1Anchor j) (1/W1Target i) (W1Anchor j) oneNumerators ≤
        singletonMass (W1Domain i j) at hs
  unfold W1OldIntegral
  constructor <;> linarith only [ht.1, ht.2, hs.1, hs.2, hm]

theorem W2_unit_integral_bounds {p : W2Parameters} (hp : W2Geometry p) :
    0 ≤ W2OldIntegral p oneNumerators oneNumerators ∧
      W2OldIntegral p oneNumerators oneNumerators ≤ (59/5:ℝ) := by
  have ht0 := one_table_bounds false p.s0
  have ht1 := one_table_bounds false p.phi1
  have hs (k : Fin 3) :
      0 ≤ singleOldIntegral (a0 p) (singletonTop p k) p.s0 oneNumerators ∧
        singleOldIntegral (a0 p) (singletonTop p k) p.s0 oneNumerators ≤ 3 := by
    have he : Ioo (a0 p) (singletonTop p k) = W2SingletonDomain p k := by
      fin_cases k <;> rfl
    have h := singleton_unit_integral_bounds (measurableSet_W2SingletonDomain p k)
      (W2SingletonDomain_subset hp k) p.s0
    rw [← he] at h
    have hsub : Ioo (a0 p) (singletonTop p k) ⊆ singletonAmbient := by
      rw [he]
      exact W2SingletonDomain_subset hp k
    exact ⟨h.1, h.2.trans (singletonMass_le_three hsub)⟩
  have hp' (k : Fin 4) : 0 ≤ pairOldIntegral p k oneNumerators ∧
      pairOldIntegral p k oneNumerators ≤ (45/4:ℝ) :=
    ⟨(pair_unit_integral_bounds hp k).1,
      (pair_unit_integral_bounds hp k).2.trans
        (pairMass_le_45_fourths (W2PairDomain_subset hp k))⟩
  have hs0 := Finset.sum_nonneg (s := Finset.univ) (fun k _ => (hs k).1)
  have hp0 := Finset.sum_nonneg (s := Finset.univ) (fun k _ => (hp' k).1)
  have hs1 := Finset.sum_le_sum (s := Finset.univ) (fun k _ => (hs k).2)
  have hp1 := Finset.sum_le_sum (s := Finset.univ) (fun k _ => (hp' k).2)
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs1 hp1
  unfold W2OldIntegral
  constructor <;> linarith only [ht0.1, ht0.2, ht1.1, ht1.2, hs0, hp0, hs1, hp1]

/-- All bank actions use their actual carrier; W1 is not replaced by W2's N-mask. -/
def arithmeticProfile (N : ℕ) (Q L : ℝ) (d : ℕ)
    (oldH oldh : Fin 200 → ℤ) : Original106Action → ℝ
  | .inl (i,j) => literalW1ThetaOldProfile N Q d i j oldH oldh
  | .inr j => W2ThetaOldProfile N Q L d (originalW2At j) oldH oldh

def idealProfile (oldH oldh : Fin 200 → ℤ) : Original106Action → ℝ
  | .inl (i,j) => W1OldIntegral i j oldH oldh
  | .inr j => W2OldIntegral (originalW2At j) oldH oldh

theorem ideal_unit_profile_le (a : Original106Action) :
    idealProfile oneNumerators oneNumerators a ≤ (59/5:ℝ) := by
  rcases a with ⟨i,j⟩ | j
  · exact (W1_unit_integral_bounds i j).2.trans (by norm_num)
  · exact (W2_unit_integral_bounds
      (originalRepairedW2Bank_geometry _ (originalW2At_mem j))).2

/-- An actual arithmetic local estimate, uniform BEFORE N, Q, d and the
action are chosen. The supplied old arrays may be any fixed arrays. -/
theorem all106_arithmetic_profile_error {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (oldH oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q L : ℝ, ∀ d : ℕ,
      L ∈ Icc Lmin Lmax → 0 < d → Q = (d:ℝ)*(N:ℝ)^L →
      2 ≤ P2OriginalChildPhysicalNormalization.alpha (Real.log (d:ℝ)/Real.log (N:ℝ)) L →
      ∀ a : Original106Action,
        |arithmeticProfile N Q L d oldH oldh a - thetaAtom N Q d*idealProfile oldH oldh a| ≤
          epsilon*thetaAtom N Q d := by
  obtain ⟨T1,h1⟩ := all70_literal_sameQ_Theta_profile_passage hmin hmax he oldH oldh
  obtain ⟨T2,h2⟩ := all106_sameQ_Theta_profile_passage hmin hmax he oldH oldh
  refine ⟨max T1 T2, ?_⟩
  intro N hN Q L d hL hd hQ ha a
  rcases a with ⟨i,j⟩ | j
  · have h := h1 N (by omega) Q ({()} : Finset Unit)
      (fun _ => L) (fun _ => d) (fun _ => 1)
      (fun _ _ => hL) (fun _ _ => hd) (fun _ _ => hQ)
      (fun _ _ => zero_le_one) (fun _ _ => ha) i j
    simpa only [arithmeticProfile, idealProfile, Finset.sum_singleton, one_mul] using h
  · have h := (h2 N (by omega) Q ({()} : Finset Unit)
      (fun _ => L) (fun _ => d) (fun _ => 1)
      (fun _ _ => hL) (fun _ _ => hd) (fun _ _ => hQ)
      (fun _ _ => zero_le_one)).2 j
    simpa only [arithmeticProfile, idealProfile, Finset.sum_singleton, one_mul] using h

/-- The manuscript's parent normalizer, with labels retained even when
two different histories produce the same integer prefix. -/
def parentTheta {ι : Type*} (N : ℕ) (Q : ℝ) (S : Finset ι)
    (d : ι → ℕ) (sigma : ι → ℝ) : ℝ :=
  ∑ a ∈ S, sigma a*thetaAtom N Q (d a)

theorem parentTheta_natural (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    parentTheta N Q D id sigma = P2EnhancedTwentyOneSameQWeighted.Theta N Q D sigma :=
  (Theta_eq_sum_atoms N Q D sigma).symm

theorem parentTheta_nonneg {ι : Type*} {N : ℕ} (hN : 4 ≤ N)
    (Q : ℝ) (S : Finset ι) (d : ι → ℕ) (sigma : ι → ℝ)
    (hd : ∀ a ∈ S, 0 < d a) (hsigma : ∀ a ∈ S, 0 ≤ sigma a)
    (hR : ∀ a ∈ S, 1 < Q/(d a:ℝ)) : 0 ≤ parentTheta N Q S d sigma :=
  Finset.sum_nonneg (fun a ha => mul_nonneg (hsigma a ha)
    (thetaAtom_nonneg hN (hd a ha) (hR a ha)))

/-- Positive occurrence mass of all 106 actual rows. The strict margin
59/5 < 12 pays the genuine arithmetic replacement error. The common
threshold precedes arbitrary parent-dependent action selection. -/
theorem all106_parentTheta_mass_le_twelve {Lmin Lmax : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ) (action : ι → Original106Action),
      (∀ a ∈ S, L a ∈ Icc Lmin Lmax) → (∀ a ∈ S, 0 < d a) →
      (∀ a ∈ S, Q = (d a:ℝ)*(N:ℝ)^(L a)) → (∀ a ∈ S, 0 ≤ sigma a) →
      (∀ a ∈ S, 2 ≤ P2OriginalChildPhysicalNormalization.alpha
        (Real.log (d a:ℝ)/Real.log (N:ℝ)) (L a)) →
      (∑ a ∈ S, sigma a*arithmeticProfile N Q (L a) (d a)
        oneNumerators oneNumerators (action a)) ≤ 12*parentTheta N Q S d sigma := by
  obtain ⟨T,hT⟩ := all106_arithmetic_profile_error hmin hmax
    (by norm_num : (0:ℝ) < 1/10) oneNumerators oneNumerators
  refine ⟨max 4 T, ?_⟩
  intro N hN Q ι S L d sigma action hL hd hQ hsigma halpha
  have hN4 : 4 ≤ N := by omega
  have hN1 : 1 < N := by omega
  have hterm (a) (ha : a ∈ S) :
      arithmeticProfile N Q (L a) (d a) oneNumerators oneNumerators (action a) ≤
        12*thetaAtom N Q (d a) := by
    have hw := thetaAtom_nonneg hN4 (hd a ha)
      (sameQ_residual_gt_one hN1 (hd a ha) (hmin.trans_le (hL a ha).1) (hQ a ha))
    have he := (abs_le.mp (hT N (by omega) Q (L a) (d a)
      (hL a ha) (hd a ha) (hQ a ha) (halpha a ha) (action a))).2
    have hi := mul_le_mul_of_nonneg_left (ideal_unit_profile_le (action a)) hw
    linarith only [he, hi, hw]
  calc
    _ ≤ ∑ a ∈ S, sigma a*(12*thetaAtom N Q (d a)) :=
      Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hterm a ha) (hsigma a ha))
    _ = _ := by simp only [parentTheta, Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring

end
end ImbalancedChen.Part5OriginalH430ArithmeticParentMass
