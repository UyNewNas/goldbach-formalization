import ImbalancedChen.P2Historical246RectanglePrimeMass
import ImbalancedChen.P2Historical246PrefixCollisionFibres

/-! SOURCE ONLY / UNEVALUATED. Same-Q, actual marked-prefix bridge for the
H246 j=0, k=0 rectangle, CONDITIONAL on the actual inherited ceiling lying
below its v interval. No marked source with that condition is constructed;
no H247 endpoint, reserve, or sieve count licence is proved. -/
namespace ImbalancedChen.P2Historical246ActualRectangleDebit
noncomputable section
open Set Finset Filter
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2Historical246RectanglePrimeMass P2Historical246StrictRectangleIntegral
open P2Historical246StrictDebit P2Historical246StrictCeilingChildUpper
open P2Historical246PairCarrierPartition P2Historical246PrefixCollisionFibres
open P2Historical246RepeatedCeilingAtom P2Historical246RepeatedCeilingBook
open P2Historical246SuccessorParentWindow P2Historical246SuccessorPrimeCeiling
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalPhysicalOldProfileMass P2OriginalHalfOpenProfileCarrier
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def rectCarrier (N : ℕ) (L : ℝ) : Finset Pair :=
  (actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5)).filter
    (fun p => normalizedLog N L p ∈ primeRect)

def rectGood (N : ℕ) (L : ℝ) (old : List ℕ) : Finset Pair :=
  (rectCarrier N L).filter (bothCoprime N old)

def rectBad (N : ℕ) (L : ℝ) (old : List ℕ) : Finset Pair :=
  (rectCarrier N L).filter (fun p => ¬ bothCoprime N old p)

theorem rectCarrier_subset_half (N : ℕ) (L : ℝ) :
    rectCarrier N L ⊆ halfCarrier N L 0 0 := by
  intro p hp
  obtain ⟨hbox,hrect⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hbox,?_⟩
  exact (pairHalf_partition (originalW2At 0) 0 _).mpr
    (Or.inl (primeRect_geometry hrect).1)

/-- Exact finite original same-Q atom identity on the actual N-deleted
rectangle. The two local factors retain their original order and repeats. -/
theorem rectangle_theta_eq_test {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hA : 4 ≤ (N:ℝ)^(L/10)) (hQ : Q = (d:ℝ)*(N:ℝ)^L) :
    (∑ p ∈ rectCarrier N L, oldPairAtom N Q L d 0 0 p) =
      thetaAtom N Q d * truePairTest N L d primeRect
        (pairTest (originalW2At 0) 0 (outputAt 246 true)) := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  unfold rectCarrier truePairTest
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 := mem_actualPrimeBoxTuples_iff.mp hp 0
  have hp1 := mem_actualPrimeBoxTuples_iff.mp hp 1
  have hp02 : 2 < p 0 := by
    have hh := hA.trans hp0.2.2.1
    exact_mod_cast (show (2:ℝ) < p 0 by linarith)
  have hp12 : 2 < p 1 := by
    have hh := hA.trans hp1.2.2.1
    exact_mod_cast (show (2:ℝ) < p 1 by linarith)
  by_cases hx : normalizedLog N L p ∈ primeRect
  · simp only [if_pos hx,indicator_of_mem hx]
    unfold oldPairAtom
    rw [thetaAtom_pair (by omega) hd hp0.1 hp1.1 hp02 hp12
      (hp0.1.coprime_iff_not_dvd.mpr hp0.2.1)
      (hp1.1.coprime_iff_not_dvd.mpr hp1.2.1) hR]
    have hlog (i : Fin 2) : Real.log (p i:ℝ)/Real.log (Q/d) = normalizedLog N L p i := by
      rw [hQ]
      exact physical_log_ratio hN hd hL p i
    rw [hlog 0,hlog 1]
    obtain ⟨h0,h1,h2,h3⟩ := mem_primeRect.mp hx
    have hden : (1/10:ℝ) ≤ 1-normalizedLog N L p 0-normalizedLog N L p 1 := by linarith
    simp only [pairTest,residualPair,max_eq_right hden]
    ring
  · simp only [if_neg hx,indicator_of_notMem hx,mul_zero]

theorem rect_sum_good_bad (N : ℕ) (L : ℝ) (old : List ℕ) (F : Pair → ℝ) :
    (∑ p ∈ rectCarrier N L,F p) =
      (∑ p ∈ rectGood N L old,F p) + (∑ p ∈ rectBad N L old,F p) := by
  unfold rectGood rectBad
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : bothCoprime N old p <;> simp [h]

/-- An actual full-prefix collision is charged once, including both
ceiling-equality slices already contained in prefixCarrier. -/
theorem rectBad_subset_prefix {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hparent : parentWindow N Q old chi) :
    rectBad N L old ⊆ prefixCarrier N Q L chi old 0 0 := by
  intro p hp
  obtain ⟨hr,hbad⟩ := Finset.mem_filter.mp hp
  have hh := rectCarrier_subset_half N L hr
  have hx := (Finset.mem_filter.mp hr).2
  apply Finset.mem_filter.mpr
  exact ⟨hh,(primeRect_geometry hx).1,hparent,hbad⟩

/-- The same inherited ceiling is a prime c of the actual marked prefix.
The strict cap condition makes every GOOD rectangle pair rejected in the
actual c<p1 branch; there is no equality-to-ceiling double count. -/
theorem rectGood_subset_strict {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (m : Mark) (choice : SuccessorChoice) (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu)
    (hcap : (advance m choice).history.ceiling (advance m choice).ceiling t <
      residualExponent N (parentProduct (oldWord t)) nu * (2999/10000:ℝ)) :
    let L := residualExponent N (parentProduct (oldWord t)) nu
    let Q := (N:ℝ)^nu
    let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
    let c := ceilingPrime N m choice t
    rectGood N L (oldWord t) ⊆ (halfCarrier N L 0 0).filter
      (fun p => interior N L 0 0 p ∧ parentWindow N Q (oldWord t) chi ∧
        bothCoprime N (oldWord t) p ∧ c < p 1) := by
  dsimp only
  intro p hp
  obtain ⟨hr,hcop⟩ := Finset.mem_filter.mp hp
  have hh := rectCarrier_subset_half _ _ hr
  have hx := (Finset.mem_filter.mp hr).2
  have hbox := (Finset.mem_filter.mp hr).1
  have hp1 := (mem_actualPrimeBoxTuples_iff.mp hbox 1).1
  have hparent := successor_parentWindow hN he hnu m choice hm ht
  obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level hN he m choice hm ht
  obtain ⟨hc,hdiv,hchi⟩ := ceilingPrime_spec hN he m choice hm ht
  have hnorm : residualExponent N (parentProduct (oldWord t)) nu *
      normalizedLog N (residualExponent N (parentProduct (oldWord t)) nu) p 1 =
        physicalPrime N (p 1) := by
    simp [normalizedLog,actualPrimeTupleLog,physicalPrime,Pi.smul_apply,smul_eq_mul,
      mul_assoc,hL.ne']
  have hv := (mem_primeRect.mp hx).2.2.1
  have hphys : physicalPrime N (ceilingPrime N m choice t) < physicalPrime N (p 1) := by
    rw [← hchi,← hnorm]
    nlinarith
  have hlt := (physicalPrime_lt_iff hN hc.pos hp1.pos).mp hphys
  apply Finset.mem_filter.mpr
  exact ⟨hh,(primeRect_geometry hx).1,hparent,hcop,hlt⟩

/-- Once a literal marked source satisfies the stated ceiling inequality,
the full-prefix collision is the only debit from the rectangle: all
remaining terms lie in its real strictLane. No empty-source conclusion is
asserted by this pointwise inequality. -/
theorem rectangle_le_strict_add_prefix {N horizon : ℕ} {nu eta : ℝ}
    (hN : 4 ≤ N) (he : 0 < eta) (hnu : nu ≤ 1)
    (m : Mark) (choice : SuccessorChoice) (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu)
    (hcap : (advance m choice).history.ceiling (advance m choice).ceiling t <
      residualExponent N (parentProduct (oldWord t)) nu * (2999/10000:ℝ)) :
    let L := residualExponent N (parentProduct (oldWord t)) nu
    let Q := (N:ℝ)^nu
    let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
    (∑ p ∈ rectCarrier N L, oldPairAtom N Q L (parentProduct (oldWord t)) 0 0 p) ≤
      strictLane N nu m choice t 0 0 +
      ∑ p ∈ prefixCarrier N Q L chi (oldWord t) 0 0,
        oldPairAtom N Q L (parentProduct (oldWord t)) 0 0 p := by
  dsimp only
  obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level (by omega) he m choice hm ht
  have hparent := successor_parentWindow (by omega) he hnu m choice hm ht
  have hnonneg {p : Pair} (hp : p ∈ halfCarrier N
      (residualExponent N (parentProduct (oldWord t)) nu) 0 0) :
      0 ≤ oldPairAtom N ((N:ℝ)^nu) (residualExponent N (parentProduct (oldWord t)) nu)
        (parentProduct (oldWord t)) 0 0 p :=
    halfCarrier_oldAtom_nonnegative hN hd hL hQ 0 0 hp
  rw [rect_sum_good_bad N _ (oldWord t)]
  apply add_le_add
  · unfold strictLane
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (rectGood_subset_strict (by omega) he hnu m choice hm ht hcap)
    intro p hp _
    exact hnonneg (Finset.mem_filter.mp hp).1
  · apply Finset.sum_le_sum_of_subset_of_nonneg (rectBad_subset_prefix hparent)
    intro p hp _
    exact hnonneg (Finset.mem_filter.mp hp).1

/-- For every actual marked tuple satisfying the explicit geometric
ceiling condition and the displayed compact L interval, its ORIGINAL
row-0 D5 strict debit contains a definite same-Q Theta mass. The single
threshold is selected before N, nu, mark, successor choice and tuple.
This does not assert that any such tuple exists. -/
theorem actual_rectangle_strictLane_lower {Lmin Lmax eta : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < eta) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu,
      let L := residualExponent N (parentProduct (oldWord t)) nu
      let Q := (N:ℝ)^nu
      L ∈ Icc Lmin Lmax →
      (advance m choice).history.ceiling (advance m choice).ceiling t < L*(2999/10000:ℝ) →
      (h52/400000000)*thetaAtom N Q (parentProduct (oldWord t)) ≤
        strictLane N nu m choice t 0 0 := by
  have heps : 0 < h52/400000000 := by positivity
  obtain ⟨Tp,hTp⟩ := rectangle_original_H246_uniform_positive hmin hmax
  obtain ⟨Tc,hTc,hcollision⟩ := successor_full_prefix_uniform he heps horizon
  obtain ⟨Tf,hTf,hfloor⟩ := successor_pair_floor_uniform he horizon
  refine ⟨max Tp (max Tc Tf), ?_, ?_⟩
  · exact hTc.trans ((le_max_left Tc Tf).trans (le_max_right Tp _))
  · intro N hN nu hnu m choice hm t ht
    dsimp only
    intro hcompact hcap
    have hN4 : 4 ≤ N := by omega
    obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level (by omega) he m choice hm ht
    have hA := hfloor N (by omega) nu hnu m choice hm t ht
    have htest := hTp N (by omega) _ hcompact (parentProduct (oldWord t))
    have hrect := rectangle_le_strict_add_prefix hN4 he hnu m choice hm ht hcap
    have hcollision := hcollision N (by omega) nu hnu m choice hm t ht 0 0
    have hcoll := (abs_le.mp hcollision).2
    have htheta : 0 ≤ thetaAtom N ((N:ℝ)^nu) (parentProduct (oldWord t)) :=
      thetaAtom_nonneg hN4 hd (sameQ_residual_gt_one (by omega) hd hL hQ)
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt htest) htheta
    have heq := rectangle_theta_eq_test (by omega) hd hL hA hQ
    rw [heq] at hrect
    nlinarith only [hmul,hrect,hcoll]

end
end ImbalancedChen.P2Historical246ActualRectangleDebit
