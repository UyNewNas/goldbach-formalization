import ImbalancedChen.Part5OriginalH430OrdinaryPairWalls
import ImbalancedChen.Part5OriginalH430W2UpperBankPayment
import ImbalancedChen.Part5OriginalH430SeedHistoryMass
import ImbalancedChen.P2OriginalProfileThetaNormalization
import ImbalancedChen.CanonicalUpperCancellationP5

/-! Actual ordinary four-pair centre at every original W2 action. The signed
child discrepancy is evaluated on the immutable old arithmetic state and
the matching predecessor H, on the same half-open parent windows. -/
namespace ImbalancedChen.Part5OriginalH430OrdinaryPairCounts
noncomputable section
open Set MeasureTheory Filter Finset
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2OriginalW2CountTupleReindex P2OriginalHalfOpenProfileCarrier P2OriginalCompactThetaMass
open P2OriginalPositiveSameQMassLift P2OriginalProfileThetaNormalization
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2AllW1SameQRawCountInduction (PhysicalState)
open Part5OriginalH430W2UpperWeights Part5OriginalH430W2UpperArchiveData
open Part5OriginalH430W2UpperBankPayment Part5OriginalH430OrdinaryPairWalls
open Part5OriginalH430ImmutableBankProfiles (precedingH)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SeedHistoryMass
open scoped Classical BigOperators

def ordinaryIntegral (j : Fin 36) (k : Fin 4) : ℝ :=
  ∫ x in W2PairDomain (originalW2At j) k, 1/(x 0*x 1*(1-x 0-x 1))

def archivedLane (j : Fin 36) (k : Fin 4) (g : Fin 430) : ℝ :=
  ∑ i : Fin 200, ((weightAt (weights j k) i.val:ℝ)/(2^80:ℝ))*floorValue (precedingH g) i

def childDiscrepancy (N : ℕ) (Q L : ℝ) (old : PhysicalState) (d : ℕ)
    (j : Fin 36) (k : Fin 4) (g : Fin 430) : ℝ :=
  ∑ x ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
    if normalizedLog N L x ∈ pairHalf (originalW2At j) k then
      let b := d*x 0*x 1
      let s := pairProfile (originalW2At j) k (normalizedLog N L x)
      old.upper b (occurrenceCutoff Q d (originalW2At j) k (x 0) (x 1)) -
        thetaAtom N Q b*(P5CanonicalUpperCancellation.upperA s -
          tableFunction false (precedingH g) s)
    else 0

/-- Exact ordinary/feedback/old-count decomposition before averaging. -/
theorem true_pair_split {N n p d : ℕ} {root : Root} {t L : ℝ}
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (hQ : rootQ N n root t p=(d:ℝ)*(N:ℝ)^L)
    (old : PhysicalState) (j : Fin 36) (k : Fin 4) (g : Fin 430) :
    let Q := rootQ N n root t p
    sourceGoodOccurrence N Q old d (originalW2At j) k =
      pairChildTheta N Q L d (originalW2At j) k -
        pairThetaOldProfile N Q L d (originalW2At j) k (precedingH g) +
        childDiscrepancy N Q L old d j k g := by
  dsimp only
  have hj := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  rw [all_four_old_count_occurrences_reindex hN hd hL hQ old hj]
  unfold pairChildTheta pairThetaOldProfile childDiscrepancy
  rw [← sum_sub_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  have he := actual_half_iff_open hN hL hQ j k x (fun i =>
    ⟨(mem_actualPrimeBoxTuples_iff.mp hx i).1,(mem_actualPrimeBoxTuples_iff.mp hx i).2.1⟩)
  by_cases hmem : normalizedLog N L x ∈ pairHalf (originalW2At j) k
  · have h := W2PairDomain_profile_bounds hj k (he.mp hmem)
    have hone := P5CanonicalUpperCancellation.upperA_eq_one (zero_lt_one.trans h.1)
      (h.2.1.le.trans h.2.2)
    simp only [if_pos hmem,show L⁻¹ • actualPrimeTupleLog N x ∈ W2PairDomain (originalW2At j) k
        from he.mp hmem,if_true,hone]
    ring
  · have hopen : L⁻¹ • actualPrimeTupleLog N x ∉ W2PairDomain (originalW2At j) k :=
      fun h => hmem (he.mpr h)
    simp only [if_neg hmem,if_neg hopen,sub_zero,add_zero]

private theorem floor_le_one : frozenResidualFloor≤1 := by
  unfold frozenResidualFloor
  have h : (1:ℝ)≤101^440 := one_le_pow₀ (by norm_num) 
  exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h])

/-- One threshold works on all generated positions, all 36 actions and all
430 predecessor tables. Each genuine signed old-child discrepancy is kept. -/
theorem uniform_four_ordinary_cells {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → ∀ (n : ℕ) (root : Root) (t : ℝ) (p dep : ℕ),
    0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N root →
    ∀ (l : LevelIndex N n root t p dep) (old : PhysicalState) (j : Fin 36) (k : Fin 4)
      (g : Fin 430), let Q := rootQ N n root t p; let d := wordProduct l; let L := wordLevel l
      sourceGoodOccurrence N Q old d (originalW2At j) k ≤
        thetaAtom N Q d * (ordinaryIntegral j k - archivedLane j k g) +
          childDiscrepancy N Q L old d j k g + ε * thetaAtom N Q d := by
  obtain ⟨Tm,hm⟩ := all36_compact_uniform_pair_mass frozenResidualFloor_pos floor_le_one (half_pos hε)
  obtain ⟨Ta,ha⟩ := compact_multiplier_error (k:=2) frozenResidualFloor_pos floor_le_one
    (show (0:ℝ)≤0 by norm_num) (show (0:ℝ)<1 by norm_num)
  obtain ⟨Th,_,hh⟩ := uniform_original_four_windows frozenResidualFloor_pos floor_le_one (half_pos hε)
  let T := max 4 (max Tm (max Ta Th))
  refine ⟨T,le_max_left _ _,?_⟩
  intro N hNT n root t p dep ht ht' hn hp l old j k g
  have hN4 : 4≤N := (le_max_left _ _).trans hNT
  have hNm : Tm≤N := ((le_max_left _ _).trans (le_max_right _ _)).trans hNT
  have hNa : Ta≤N := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hNT
  have hNh : Th≤N := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hNT
  let L := wordLevel l
  let d := wordProduct l
  let Q := rootQ N n root t p
  obtain ⟨hd,hRange,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
  have hL : 0<L := frozenResidualFloor_pos.trans_le hRange.1
  have hN1 : 1<N := by omega
  have htheta := thetaAtom_nonneg hN4 hd (sameQ_residual_gt_one hN1 hd hL hQ)
  have hA := (ha N hNa L hRange).1
  have hgeom := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have hreal := (abs_lt.mp (hm N hNm L hRange d j k)).2.le
  have harch := hh N hNh L hRange d hd Q hQ j k g
  rw [physicalUpperWindow_eq_profile hN1 hd hL hQ] at harch
  change archivedLane j k g ≤ _ + ε/2 at harch
  have hdiff : P2OriginalBankThetaMassLimits.truePairMass N L d (originalW2At j) k -
      P2OriginalPhysicalOldProfileMass.truePairOldProfile N L d (originalW2At j) k (precedingH g) ≤
      ordinaryIntegral j k - archivedLane j k g + ε := by
    unfold ordinaryIntegral
    linarith only [hreal,harch]
  dsimp only
  rw [true_pair_split hN1 hd hL hQ old j k g,pairChildTheta_eq hN1 hd hL _ hgeom k hA hQ,
    pairThetaOldProfile_eq hN1 hd hL hA hQ hgeom k]
  nlinarith only [mul_le_mul_of_nonneg_left hdiff htheta]

end
end ImbalancedChen.Part5OriginalH430OrdinaryPairCounts
