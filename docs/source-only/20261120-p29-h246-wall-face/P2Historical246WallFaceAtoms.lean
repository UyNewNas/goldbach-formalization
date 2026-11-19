import ImbalancedChen.P2Historical246RepeatedCeilingDecomposition
import ImbalancedChen.P2OriginalPhysicalOldProfileMass

/-! SOURCE ONLY / UNEVALUATED. The lower wall is a literal finite
prime face, not an integral-null deletion. This packet gives exact
face uniqueness and a same-Q H246 atom bound without any fresh-prime
assumption. It does not yet sum or pay the wall. -/
namespace ImbalancedChen.P2Historical246WallFaceAtoms
noncomputable section
open Set Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2Historical246SuccessorParentWindow
open P2Historical246PairCarrierPartition P2Historical246RepeatedCeilingAtom
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalBankThetaMassLimits P2OriginalHalfOpenProfileCarrier
open P2OriginalPhysicalOldProfileMass P2OriginalPositiveSameQMassLift P2OriginalCompactThetaMass
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

/-- A physical logarithmic coordinate determines its actual positive
prime at fixed N,L. This works on the original N-deleted box, without
assuming prefix coprimality or selecting an asymptotic threshold. -/
theorem same_wall_coordinate {N : ℕ} {L : ℝ} (hN : 1 < N) (hL : 0 < L)
    (j : Fin 36) (k : Fin 4) {p q : Pair}
    (hp : p ∈ halfCarrier N L j k) (hq : q ∈ halfCarrier N L j k)
    (i : Fin 2) (heq : normalizedLog N L p i = normalizedLog N L q i) :
    p i = q i := by
  have hpbox := (Finset.mem_filter.mp hp).1
  have hqbox := (Finset.mem_filter.mp hq).1
  have hp0 : ∀ a : Fin 2, 0 < p a := fun a => ((mem_actualPrimeBoxTuples_iff.mp hpbox) a).1.pos
  have hq0 : ∀ a : Fin 2, 0 < q a := fun a => ((mem_actualPrimeBoxTuples_iff.mp hqbox) a).1.pos
  have hpr := normalizedLog_rpow hN hL p hp0 i
  have hqr := normalizedLog_rpow hN hL q hq0 i
  rw [heq] at hpr
  exact_mod_cast hpr.symm.trans hqr

/-- Fix one of the actual lower-face equations. The other coordinate is
an injective label of the original pair: no pair occurrence is merged. -/
theorem fixed_face_other_injective {N : ℕ} {L : ℝ}
    (hN : 1 < N) (hL : 0 < L) (j : Fin 36) (k : Fin 4)
    (i : Fin 2) (r : ℝ) {p q : Pair}
    (hp : p ∈ halfCarrier N L j k) (hq : q ∈ halfCarrier N L j k)
    (hpr : normalizedLog N L p i = r) (hqr : normalizedLog N L q i = r)
    (hother : p (1-i) = q (1-i)) : p = q := by
  have hi := same_wall_coordinate hN hL j k hp hq i (hpr.trans hqr.symm)
  funext a
  fin_cases i <;> fin_cases a <;> first
    | simpa using hi
    | simpa using hother

/-- Exact physical identity before any wall, prefix-collision or
ceiling restriction. Both local factors retain the original d and d*p0,
so repeated-prefix and fresh factors are not interchanged. -/
theorem full_pair_atom_identity {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (hA : 4 ≤ (N : ℝ)^(L/10)) (j : Fin 36) (k : Fin 4)
    {p : Pair} (hp : p ∈ halfCarrier N L j k) :
    oldPairAtom N Q L (parentProduct old) j k p =
      thetaAtom N Q (parentProduct old) *
        (localPrimeFactor (parentProduct old) (p 0) *
          localPrimeFactor (parentProduct old*p 0) (p 1)) *
            pairTest (originalW2At j) k (outputAt 246 true) (normalizedLog N L p) := by
  have hbox := (Finset.mem_filter.mp hp).1
  have hhalf := (Finset.mem_filter.mp hp).2
  have hp0 := (mem_actualPrimeBoxTuples_iff.mp hbox) 0
  have hp1 := (mem_actualPrimeBoxTuples_iff.mp hbox) 1
  have hp02 : 2 < p 0 := by
    have h := hA.trans hp0.2.2.1
    exact_mod_cast (show (2 : ℝ) < p 0 by linarith)
  have hp12 : 2 < p 1 := by
    have h := hA.trans hp1.2.2.1
    exact_mod_cast (show (2 : ℝ) < p 1 by linarith)
  have hp0N : (p 0).Coprime N := hp0.1.coprime_iff_not_dvd.mpr hp0.2.1
  have hp1N : (p 1).Coprime N := hp1.1.coprime_iff_not_dvd.mpr hp1.2.1
  have hR := sameQ_residual_gt_one hN hd hL hQ
  have hlog (i : Fin 2) : Real.log (p i : ℝ)/Real.log (Q/(parentProduct old : ℝ)) =
      normalizedLog N L p i := by
    rw [hQ]
    exact physical_log_ratio hN hd hL p i
  have hden : (1/10 : ℝ) ≤ 1-normalizedLog N L p 0-normalizedLog N L p 1 := by
    have hg := pairHalf_geometry (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k hhalf
    linarith [hg.2.1]
  unfold oldPairAtom
  rw [thetaAtom_pair (by omega) hd hp0.1 hp1.1 hp02 hp12 hp0N hp1N hR, hlog 0, hlog 1]
  unfold pairTest residualPair
  rw [max_eq_right hden]
  ring

/-- Pointwise bound valid for every actual H246 half-box pair, including
wall, prefix repeats, fresh primes and strict-ceiling cases. -/
theorem full_pair_atom_bound {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (hA : 4 ≤ (N : ℝ)^(L/10)) (j : Fin 36) (k : Fin 4)
    {p : Pair} (hp : p ∈ halfCarrier N L j k) :
    |oldPairAtom N Q L (parentProduct old) j k p| ≤
      |thetaAtom N Q (parentProduct old)| *
        ((2*(1/((p 0 : ℝ)-1))) * (2*(1/((p 1 : ℝ)-1)))) *
          (10*floorBound (outputAt 246 true)) := by
  have hbox := (Finset.mem_filter.mp hp).1
  have hp0 := (mem_actualPrimeBoxTuples_iff.mp hbox) 0
  have hp1 := (mem_actualPrimeBoxTuples_iff.mp hbox) 1
  have hp02 : (2 : ℝ) < p 0 := by have h := hA.trans hp0.2.2.1; linarith
  have hp12 : (2 : ℝ) < p 1 := by have h := hA.trans hp1.2.2.1; linarith
  have ha : 0 ≤ localPrimeFactor (parentProduct old) (p 0) := (localPrimeFactor_pos hp02).le
  have hb : 0 ≤ localPrimeFactor (parentProduct old*p 0) (p 1) := (localPrimeFactor_pos hp12).le
  have ha' := local_le_twice (d := parentProduct old) hA hp0.2.2.1
  have hb' := local_le_twice (d := parentProduct old*p 0) hA hp1.2.2.1
  have hs0 : (0 : ℝ) < (p 0 : ℝ)-1 := by linarith
  have hs1 : (0 : ℝ) < (p 1 : ℝ)-1 := by linarith
  have hright : 0 ≤ 2*(1/((p 0 : ℝ)-1)) :=
    mul_nonneg (by norm_num) (one_div_pos.mpr hs0).le
  have hright1 : 0 ≤ 2*(1/((p 1 : ℝ)-1)) :=
    mul_nonneg (by norm_num) (one_div_pos.mpr hs1).le
  have hprod := mul_le_mul ha' hb' hb hright
  have htest := pairTest_bound (originalW2At j) k (outputAt 246 true) (normalizedLog N L p)
  rw [full_pair_atom_identity hN hd hL hQ hA j k hp,abs_mul,abs_mul,
    abs_of_nonneg (mul_nonneg ha hb)]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hprod htest (abs_nonneg _) (mul_nonneg hright hright1)) (abs_nonneg _)


/-- The source supplies positive L and the unchanged Q for each actual
successor; equal normalized wall coordinates force the same prime. -/
theorem successor_wall_coordinate_unique {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (m : Mark) (choice : SuccessorChoice)
    (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) (j : Fin 36) (k : Fin 4)
    {p q : Pair}
    (hp : p ∈ halfCarrier N (residualExponent N (parentProduct (oldWord t)) nu) j k)
    (hq : q ∈ halfCarrier N (residualExponent N (parentProduct (oldWord t)) nu) j k)
    (i : Fin 2)
    (heq : normalizedLog N (residualExponent N (parentProduct (oldWord t)) nu) p i =
      normalizedLog N (residualExponent N (parentProduct (oldWord t)) nu) q i) : p i = q i := by
  obtain ⟨_,hL,_⟩ := successor_sameQ_positive_level hN he m choice hm ht
  exact same_wall_coordinate hN hL j k hp hq i heq

/-- One threshold for the genuine successor and every historical pair
row; the atom may lie on the wall or in any other half-box class. -/
theorem successor_all_pair_atoms_uniform {eta : ℝ} (he : 0 < eta) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu, ∀ (j : Fin 36) (k : Fin 4) (p : Pair),
      p ∈ halfCarrier N (residualExponent N (parentProduct (oldWord t)) nu) j k →
      |oldPairAtom N ((N : ℝ)^nu) (residualExponent N (parentProduct (oldWord t)) nu)
        (parentProduct (oldWord t)) j k p| ≤
      |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| *
        ((2*(1/((p 0 : ℝ)-1))) * (2*(1/((p 1 : ℝ)-1)))) *
          (10*floorBound (outputAt 246 true)) := by
  obtain ⟨T,hT,hfloor⟩ := successor_pair_floor_uniform he horizon
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu m choice hm t ht j k p hp
  obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level (by omega) he m choice hm ht
  exact full_pair_atom_bound (by omega) hd hL hQ
    (hfloor N hN nu hnu m choice hm t ht) j k hp

end
end ImbalancedChen.P2Historical246WallFaceAtoms
