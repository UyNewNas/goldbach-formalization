import ImbalancedChen.Part5OriginalH430SeedRosserCountCredit

/-! Initial 1/50 and the four literal rounds on the original positive
occurrences. The upper anchors and ordinary lower means have now been
priced at their true signed AP packets. The extra true lower count above
the polynomial remains available at every round. -/
namespace ImbalancedChen.Part5OriginalH430SeedAtSignedAP
noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted P2EnhancedTwentyOneChildCorrection
open P2EnhancedNegativeChildModulusPrimePayment (piCenteredPhysicalError)
open P2ActualSameQTwentyOnePositiveSourceBinding (actualLocalPrimeMass)
open P2SeedOmegaLiteralFibre P2SeedOmegaLiteralFunctional P2FrozenReceiverCountActions
open P2SeedOmegaOriginalNumerical (actualJ2omega_gt_safe_base)
open P5OriginalU5FrozenSource (receiver)
open P2OriginalW2CentreThetaPayment (groupedSigma weighted_fiber_sum)
open P2OriginalHalfOpenProfileCarrier (below_two_comparison)
open P2OriginalPositiveSameQMassLift (sameQ_residual_gt_one)
open P2Selected430CausalOccurrenceExporter (iterate seed)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OriginalRootQBound
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430SeedConvertedMass
open Part5OriginalH430SelectedOrdinaryPairCounts (trueAt)
open Part5OriginalH430SeedHistoryMass Part5OriginalH430SignedSeedCount
open Part5OriginalH430SeedFourMarkedRounds Part5OriginalH430SeedSevenPhysicalWindows
open Part5OriginalH430SeedThreeNegativeMeans (three_negative_mean_payment)
open Part5OriginalH430SeedRosserCountCredit (credit source_count_with_credit)
open Part5OriginalH430SeedUpperAnchorsAP (anchorAP seed_anchor_payment)
open scoped Classical BigOperators

/-- Grouped arithmetic source at the same target and physical modulus.
Both appearances of the centre use their original normalizations. -/
def residue (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) : ℝ :=
  anchorAP N Q D σ-piCenteredPhysicalError N Q D σ+signedPositive N Q D σ

theorem true_seed_to_mother {N n p : ℕ} {k : Root} {t : ℝ}
    (hN : 2≤N) (ht : 0≤t) (ht' : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) :
    let S := seedPositions N n k t p
    (∑ l∈S,levelMark l*trueAt l) ≤
      Phi N (rootQ N n k t p) (S.image wordProduct) (groupedSigma S wordProduct levelMark) (11/5) := by
  let Q := rootQ N n k t p
  let S := seedPositions N n k t p
  dsimp only
  unfold Phi
  rw [weighted_fiber_sum]
  apply sum_le_sum
  intro l hl
  apply mul_le_mul_of_nonneg_left _ (mark_pos (levelOccurrence l)).le
  have ho := (levelOccurrence_source l).1
  have h1 : 1<N := by omega
  have hgeom := original_band_geometry hN hp
  have hc := rootHistory_coherent h1 ht ht' hn (original_band_prime hp) hgeom ho
  have hpos := (mem_filter.mp hl).2
  have ha : (levelOccurrence l).current.node.physical.argument≤11/5 := by
    cases hi : resolve 0 (levelOccurrence l).current with
    | none => exact False.elim ((lt_irrefl 0) (hpos.trans_le (resolve_none_value hi).le))
    | some i =>
        rw [resolve_value hi] at hpos
        have hidx : i.val<60 := by
          by_contra h
          simp [iterate,seed,h,Part5OriginalUpsilon5CausalDictionary.floorValue] at hpos
        have hcell := (resolve_contains hc.read_valid hi).2
        have hright : (i.val:ℝ)≤59 := by exact_mod_cast (show i.val≤59 by omega)
        linarith only [hcell,hright]
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht ht' hn hp l
  have hR := sameQ_residual_gt_one h1 hd (frozenResidualFloor_pos.trans_le hL.1) hQ
  have hs := (rootHistory_support h1 ht ht' hn (original_band_prime hp) hgeom ho).2.2.2.1
  have hmono := below_two_comparison N (wordProduct l) (receiver N) hR.le (zero_lt_one.trans_le hs.1) ha
  have hz := history_frozen_count_eq_true_quotient hN ht ht' hn hp ho
  have hle : trueAt l≤(frozenCount N (wordProduct l) (receiver N) (cutoff Q (wordProduct l) (11/5)):ℝ) := by
    unfold trueAt
    rw [←hz]
    exact_mod_cast hmono
  apply hle.trans
  simp only [frozenCount,frozenCarrier,Int.cast_natCast,sourceSieveCount]
  exact_mod_cast card_le_card (filter_subset _ _)

theorem seed_source_at_signed_AP {ε J : ℝ} (he : 0<ε) (hJ : J<actualJ2omega) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      let Q := rootQ N n k t p; let S := seedPositions N n k t p
      let D := S.image wordProduct; let σ := groupedSigma S wordProduct levelMark
      5*((∑ l∈S,levelMark l*trueAt l)-(1-J)*markedTheta S)+credit N Q D σ ≤
        residue N Q D σ+ε*markedTheta S := by
  have hδ : 0<ε/3 := div_pos he (by norm_num)
  obtain ⟨Ta,h4,ha⟩ := converted_centre_on_histories hJ
  obtain ⟨Tb,_,hb⟩ := source_count_with_credit frozenLeafCutoffFloor_pos hδ
  obtain ⟨Tc,_,hc⟩ := seed_anchor_payment hδ
  obtain ⟨Td,_,hds⟩ := three_negative_mean_payment hδ
  let T := max Ta (max Tb (max Tc Td))
  refine ⟨T,h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven n k t p ht ht' hn hp
  let Q := rootQ N n k t p
  let S := seedPositions N n k t p
  let D := S.image wordProduct
  let σ := groupedSigma S wordProduct levelMark
  have hNa := (le_max_left Ta _).trans hN
  have hNs := (le_max_right Ta _).trans hN
  have hNb := (le_max_left Tb _).trans hNs
  have hNcd := (le_max_right Tb _).trans hNs
  have hN2 : 2≤N := by have := h4.trans hNa; omega
  have hdata (d : ℕ) (h : d∈D) : 0<d ∧ 1<Q/(d:ℝ) ∧
      (∀ q∈d.primeFactors,(N:ℝ)^frozenLeafCutoffFloor≤(q:ℝ)) ∧
      (N:ℝ)^frozenLeafCutoffFloor≤cutoff Q d (227/50) := by
    obtain ⟨l,hl,rfl⟩ := mem_image.mp h
    obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN2 ht ht' hn hp l
    exact ⟨hd,sameQ_residual_gt_one (by omega) hd (frozenResidualFloor_pos.trans_le hL.1) hQ,
      (history_integer_roughness hN2 ht ht' hn hp (levelOccurrence_source l).1).2.2⟩
  have hsource := hb N hNb hEven Q D σ (original_root_Q_le_target N n k t p hN2 ht ht' hp)
    (fun d h => (hdata d h).1) (fun _ _ => sum_nonneg (fun l _ => (mark_pos (levelOccurrence l)).le))
    (fun d h => (hdata d h).2.1) (fun d h => (hdata d h).2.2.1) (fun d h => (hdata d h).2.2.2)
  have hcounts := true_seed_to_mother hN2 ht ht' hn hp
  have hconv := ha N hNa n k t p 0 ht ht' hn hp S
  have hanchor := hc N ((le_max_left _ _).trans hNcd) hEven n k t p 0 ht ht' hn hp S
  have hsing := hds N ((le_max_right _ _).trans hNcd) hEven n k t p 0 ht ht' hn hp S
  change J*markedTheta S≤(ordinaryPart*markedTheta S-(K/4)*converted N Q D σ)/5 at hconv
  change signedAnchors N Q D σ≤anchorAP N Q D σ+(ε/3)*markedTheta S at hanchor
  change signedSingles N Q D σ≤-(piCenteredPhysicalError N Q D σ)+(ε/3)*markedTheta S at hsing
  change (∑ l∈S,levelMark l*trueAt l)≤Phi N Q D σ (11/5) at hcounts
  change 5*((∑ l∈S,levelMark l*trueAt l)-(1-J)*markedTheta S)+credit N Q D σ≤
    residue N Q D σ+ε*markedTheta S
  have hθ : Theta N Q D σ=markedTheta S := real_word_theta S
  unfold signedAnchors at hanchor
  unfold signedSingles at hsing
  unfold residue signedPositive
  unfold ordinaryPart at hconv
  rw [hθ] at hanchor hsing hsource ⊢
  linarith only [hcounts,hsource,hanchor,hsing,hconv]

theorem initial_and_four_rounds_at_signed_AP {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      let Q := rootQ N n k t p; let S := seedPositions N n k t p
      let D := S.image wordProduct; let σ := groupedSigma S wordProduct levelMark
      let count := ∑ l∈S,levelMark l*trueAt l
      (5*(count-(1-1/50:ℝ)*markedTheta S)+credit N Q D σ ≤ residue N Q D σ+ε*markedTheta S) ∧
      (∀ r : Fin 4,5*(count-(1-originalRound r.succ)*markedTheta S)+credit N Q D σ ≤
        residue N Q D σ+5*originalRound r.castSucc*
          (∑ l∈S,levelMark l*physicalFeedback N Q (wordLevel l) (wordProduct l))+ε*markedTheta S) := by
  obtain ⟨Ta,h4,ha⟩ := seed_source_at_signed_AP he ((show (1/50:ℝ)<20249/1000000 by norm_num).trans
    actualJ2omega_gt_safe_base)
  obtain ⟨Tb,_,hb⟩ := seed_source_at_signed_AP he actualJ2omega_gt_safe_base
  obtain ⟨Tc,_,hc⟩ := seven_actual_on_marks
  refine ⟨max Ta (max Tb Tc),h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven n k t p ht ht' hn hp
  refine ⟨ha N ((le_max_left _ _).trans hN) hEven n k t p ht ht' hn hp,?_⟩
  intro r
  have hst := (le_max_right Ta _).trans hN
  have hu := hb N ((le_max_left _ _).trans hst) hEven n k t p ht ht' hn hp
  have hseven := hc N ((le_max_right _ _).trans hst) n k t p 0 ht ht' hn hp (seedPositions N n k t p)
  have hpaid := mul_le_mul_of_nonneg_left hseven (previous_round r).1.le
  dsimp only at hu ⊢
  rw [(previous_round r).2]
  linarith only [hu,hpaid]

end
end ImbalancedChen.Part5OriginalH430SeedAtSignedAP
