import ImbalancedChen.P2Historical246SuccessorPrimeCeiling
import ImbalancedChen.P2OriginalPhysicalOldProfileMass
import ImbalancedChen.P2OriginalCompactThetaMass

/-!
SOURCE ONLY / UNEVALUATED. Exact same-Q repeated-large-prime factor and
pointwise H246 atom bound. No sum, epsilon*Theta payment, endpoint or
entire prefix-collision estimate is claimed.
-/
namespace ImbalancedChen.P2Historical246RepeatedCeilingAtom

noncomputable section
open Set Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization
open P2Historical246PairCarrierPartition P2Historical246SuccessorParentWindow
open P2Historical246SuccessorPrimeCeiling
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalBankThetaMassLimits P2OriginalHalfOpenProfileCarrier
open P2OriginalPhysicalOldProfileMass P2OriginalCompactThetaMass P2OriginalPositiveSameQMassLift
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

/-- On the actual pair box, repetition of the large prime against the
old prefix contributes exactly 1/large, with the same parent Theta and
original signed H246 profile. The 1/5 W2 factor is not applied here. -/
theorem repeated_large_atom_identity {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (hA : 4 ≤ (N : ℝ)^(L/10)) (j : Fin 36) (k : Fin 4)
    {p : Pair} (hp : p ∈ halfCarrier N L j k) (hrepeat : p 1 ∣ parentProduct old) :
    oldPairAtom N Q L (parentProduct old) j k p =
      thetaAtom N Q (parentProduct old) *
        (localPrimeFactor (parentProduct old) (p 0)/(p 1 : ℝ)) *
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
  have hdiv : p 1 ∣ parentProduct old * p 0 := by
    obtain ⟨v,hv⟩ := hrepeat
    refine ⟨v*p 0,?_⟩
    rw [hv]
    ring
  have hfactor : localPrimeFactor (parentProduct old*p 0) (p 1) = 1/(p 1 : ℝ) := by
    simp only [localPrimeFactor,if_pos hdiv]
  have hlog (i : Fin 2) : Real.log (p i : ℝ)/Real.log (Q/(parentProduct old : ℝ)) =
      normalizedLog N L p i := by
    rw [hQ]
    exact physical_log_ratio hN hd hL p i
  have hden : (1/10 : ℝ) ≤ 1-normalizedLog N L p 0-normalizedLog N L p 1 := by
    have hg := pairHalf_geometry (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k hhalf
    linarith [hg.2.1]
  unfold oldPairAtom
  rw [thetaAtom_pair (by omega) hd hp0.1 hp1.1 hp02 hp12 hp0N hp1N hR,
    hfactor,hlog 0,hlog 1]
  unfold pairTest residualPair
  rw [max_eq_right hden]
  ring

/-- A precise pointwise majorant of the actual repeated-large atom. The
factor 1/large is preserved, and the profile bound is for H246 itself. -/
theorem repeated_large_atom_bound {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (hA : 4 ≤ (N : ℝ)^(L/10)) (j : Fin 36) (k : Fin 4)
    {p : Pair} (hp : p ∈ halfCarrier N L j k) (hrepeat : p 1 ∣ parentProduct old) :
    |oldPairAtom N Q L (parentProduct old) j k p| ≤
      |thetaAtom N Q (parentProduct old)| *
        ((2*(1/((p 0 : ℝ)-1)))/(p 1 : ℝ)) *
          (10*floorBound (outputAt 246 true)) := by
  have hbox := (Finset.mem_filter.mp hp).1
  have hp0 := (mem_actualPrimeBoxTuples_iff.mp hbox) 0
  have hp1 := (mem_actualPrimeBoxTuples_iff.mp hbox) 1
  have hp02 : 2 < p 0 := by
    have h := hA.trans hp0.2.2.1
    exact_mod_cast (show (2 : ℝ) < p 0 by linarith)
  have hloc : 0 ≤ localPrimeFactor (parentProduct old) (p 0) :=
    (localPrimeFactor_pos (by exact_mod_cast hp02)).le
  have hp1R : (0 : ℝ) < p 1 := by exact_mod_cast hp1.1.pos
  have hfac := local_le_twice (d := parentProduct old) hA hp0.2.2.1
  have hratio : 0 ≤ localPrimeFactor (parentProduct old) (p 0)/(p 1 : ℝ) :=
    div_nonneg hloc hp1R.le
  have hratio_le := div_le_div_of_nonneg_right hfac hp1R.le
  have hbig : 0 ≤ (2*(1/((p 0 : ℝ)-1)))/(p 1 : ℝ) := by
    have hp0R : (1 : ℝ) < p 0 := by exact_mod_cast (show 1 < p 0 by omega)
    have hp0R' : (0 : ℝ) < (p 0 : ℝ)-1 := by linarith
    positivity
  have htest := pairTest_bound (originalW2At j) k (outputAt 246 true) (normalizedLog N L p)
  rw [repeated_large_atom_identity hN hd hL hQ hA j k hp hrepeat,abs_mul,abs_mul,
    abs_of_nonneg hratio]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hratio_le htest (abs_nonneg _) hbig) (abs_nonneg _)


/-- Apply the pointwise estimate to the exact last prime of a generated
successor and to each separate pair lane of the actual H246 row. -/
theorem successor_equal_ceiling_atom_bound {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (m : Mark) (choice : SuccessorChoice)
    (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu)
    (hA : 4 ≤ (N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu/10))
    {b : Tagged} (hb : b ∈ taggedW2 246) :
    ∃ c : ℕ, c.Prime ∧ c ∣ parentProduct (oldWord t) ∧
      (advance m choice).history.ceiling (advance m choice).ceiling t = physicalPrime N c ∧
      ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
        (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        ∀ (k : Fin 4) (p : Pair),
          p ∈ halfCarrier N (residualExponent N (parentProduct (oldWord t)) nu) j k →
          p 1 = c →
          |oldPairAtom N ((N : ℝ)^nu) (residualExponent N (parentProduct (oldWord t)) nu)
            (parentProduct (oldWord t)) j k p| ≤
          |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| *
            ((2*(1/((p 0 : ℝ)-1)))/(c : ℝ)) * (10*floorBound (outputAt 246 true)) := by
  obtain ⟨c,hc,hdiv,hchi⟩ := successor_ceiling_is_prime hN he m choice hm ht
  obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level hN he m choice hm ht
  obtain ⟨j,hp,hn,hlanes⟩ := actual_pair_lists 246 hb
  refine ⟨c,hc,hdiv,hchi,j,hp,hn,hlanes,?_⟩
  intro k p hmem heq
  have hrepeat : p 1 ∣ parentProduct (oldWord t) := by simpa only [heq] using hdiv
  have hbound := repeated_large_atom_bound hN hd hL hQ hA j k hmem hrepeat
  simpa only [heq] using hbound

/-- One threshold, before the actual successor, proves the technical
lower-prime floor used by the original Theta insertion identity. -/
theorem successor_pair_floor_uniform {eta : ℝ} (he : 0 < eta) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu,
        4 ≤ (N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu/10) := by
  have hlo := floorAt_pos he (horizon+1)
  obtain ⟨T0,hT⟩ := compact_multiplier_error (k := 1)
    hlo (le_max_right (1 : ℝ) (floorAt eta (horizon+1)))
    (show (0 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max 4 T0,le_max_left _ _,?_⟩
  intro N hN nu hnu m choice hm t ht
  have hN1 : 1 < N := by omega
  have hn := advance_boxRows m choice hm
  have hf := (advance m choice).source_facts hN1 he hn ht
  have h := facts_trueAlpha hN1 hlo hf
  have hleft : floorAt eta (horizon+1) ≤
      residualExponent N (parentProduct (oldWord t)) nu := by
    rw [oldWord_product]
    linarith only [h.2.1,hlo]
  have hd1 : (1 : ℝ) ≤ Part3.labelledProduct t := by exact_mod_cast h.1
  have hb : 0 ≤ prefixExponent N (Part3.labelledProduct t) :=
    div_nonneg (Real.log_nonneg hd1) (Real.log_pos (by exact_mod_cast hN1)).le
  have hright : residualExponent N (parentProduct (oldWord t)) nu ≤
      max 1 (floorAt eta (horizon+1)) := by
    rw [oldWord_product]
    have hu : residualExponent N (Part3.labelledProduct t) nu ≤ 1 := by
      unfold residualExponent
      linarith only [hnu,hb]
    exact hu.trans (le_max_left _ _)
  exact (hT N ((le_max_right _ _).trans hN) _ ⟨hleft,hright⟩).1

/-- Combined receipt: the pre-N threshold applies to the actual H246
row and to every one of its four original pair occurrences. -/
theorem successor_equal_ceiling_atom_bound_uniform {eta : ℝ} (he : 0 < eta) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu, ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ c : ℕ, c.Prime ∧ c ∣ parentProduct (oldWord t) ∧
        (advance m choice).history.ceiling (advance m choice).ceiling t = physicalPrime N c ∧
        ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
          (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
          ∀ (k : Fin 4) (p : Pair),
            p ∈ halfCarrier N (residualExponent N (parentProduct (oldWord t)) nu) j k →
            p 1 = c →
            |oldPairAtom N ((N : ℝ)^nu) (residualExponent N (parentProduct (oldWord t)) nu)
              (parentProduct (oldWord t)) j k p| ≤
            |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| *
              ((2*(1/((p 0 : ℝ)-1)))/(c : ℝ)) * (10*floorBound (outputAt 246 true)) := by
  obtain ⟨T,hT,hfloor⟩ := successor_pair_floor_uniform he horizon
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu m choice hm t ht b hb
  exact successor_equal_ceiling_atom_bound (by omega) he m choice hm ht
    (hfloor N hN nu hnu m choice hm t ht) hb

end
end ImbalancedChen.P2Historical246RepeatedCeilingAtom
