import ImbalancedChen.Part5OriginalH430SelectedOrdinaryPairCounts
import ImbalancedChen.P2EnhancedTwentyOnePNTReceiver
import ImbalancedChen.P2ActualSameQTwentyOnePositiveSourceBinding

/-! The initial 1/50 liability at positive U3/U4 seed positions. Every term
on the right is a specified ordinary or switched source debt. The estimate
already includes the actual converted integer supply and the PNT payment. -/
namespace ImbalancedChen.Part5OriginalH430SignedSeedCount
noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted P2EnhancedTwentyOneChildCorrection
open P2EnhancedNegativeChildModulusPrimePayment P2EnhancedTwentyOnePNTReceiver
open P2ActualSameQTwentyOnePositiveSourceBinding (actualLocalPrimeMass actual_marked_source_identity)
open P2SeedOmegaLiteralFibre P2SeedOmegaLiteralFunctional
open P2FrozenReceiverCountActions P5OriginalU5FrozenSource (receiver)
open P2OriginalHalfOpenProfileCarrier (below_two_comparison)
open P2OriginalW2CentreThetaPayment (groupedSigma weighted_fiber_sum)
open P2Selected430CausalOccurrenceExporter (iterate seed)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OriginalRootQBound
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430SeedConvertedMass
open Part5OriginalH430SeedHistoryMass Part5OriginalH430SelectedOrdinaryPairCounts (trueAt)
open scoped Classical BigOperators

def signedAnchors (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) : ℝ :=
  let θ := Theta N Q D σ
  4*(Phi N Q D σ s0-(1+correction s0)*θ) +
    (Phi N Q D σ phi1-(1+correction phi1)*θ)

def signedSingles (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) : ℝ :=
  (negative b+negative a2+negative a3)*Theta N Q D σ -
    negativeMean N Q D σ - piCenteredPhysicalError N Q D σ

def signedPositive (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) : ℝ :=
  positivePairs N Q D σ + (∑ d ∈ D, σ d*actualLocalPrimeMass N Q d) -
    (ordinaryTriangle a2 + ordinaryRectangle a2 a3 + ordinaryTriangle a1 +
      ordinaryRectangle a1 a2 - badOrdinaryDouble)*Theta N Q D σ -
    (K/4)*converted N Q D σ

private theorem seed_arg {N n p : ℕ} {k : Root} {t : ℝ} (hN : 2≤N) (ht : 0≤t)
    (ht' : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k)
    {l : LevelIndex N n k t p 0} (hl : l ∈ seedPositions N n k t p) :
    (levelOccurrence l).current.node.physical.argument ≤ 11/5 := by
  have hc := rootHistory_coherent (by omega : 1<N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) (levelOccurrence_source l).1
  have hpos := (mem_filter.mp hl).2
  cases hi : resolve 0 (levelOccurrence l).current with
  | none => exact False.elim ((lt_irrefl 0) (hpos.trans_le (resolve_none_value hi).le))
  | some i =>
      rw [resolve_value hi] at hpos
      have hi' : i.val < 60 := by
        by_contra h
        simp [iterate,seed,h,Part5OriginalUpsilon5CausalDictionary.floorValue] at hpos
      have hh := (resolve_contains hc.read_valid hi).2
      have hr : (i.val:ℝ)≤59 := by exact_mod_cast (show i.val≤59 by omega)
      linarith only [hh,hr]

theorem seed_source_debt_below_base {ε J : ℝ} (hε : 0<ε) (hJ : J<actualJ2omega) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      let Q := rootQ N n k t p
      let S := seedPositions N n k t p
      let D := S.image wordProduct
      let σ := groupedSigma S wordProduct levelMark
      5*((∑ l∈S,levelMark l*trueAt l) - (1-J)*markedTheta S) ≤
        signedAnchors N Q D σ + signedSingles N Q D σ + signedPositive N Q D σ +
          ε*markedTheta S := by
  obtain ⟨Ta,hTa,ha⟩ := converted_centre_on_histories hJ
  obtain ⟨Tb,hTb,hb⟩ := actual_sameQ_pi_packet_receiver frozenLeafCutoffFloor_pos hε
  refine ⟨max Ta Tb,hTa.trans (le_max_left _ _),?_⟩
  intro N hNT hEven n k t p ht ht' hn hp
  have hNa := (le_max_left Ta Tb).trans hNT
  have hNb := (le_max_right Ta Tb).trans hNT
  have hN4 := hTa.trans hNa
  have hN2 : 2≤N := by omega
  let Q := rootQ N n k t p
  let S := seedPositions N n k t p
  let D := S.image wordProduct
  let σ := groupedSigma S wordProduct levelMark
  have data (d : ℕ) (hd : d∈D) :
      0<d ∧ 1<Q/(d:ℝ) ∧
      (∀ q∈d.primeFactors,(N:ℝ)^frozenLeafCutoffFloor≤(q:ℝ)) ∧
        (N:ℝ)^frozenLeafCutoffFloor≤cutoff Q d (227/50) := by
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hd
    obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN2 ht ht' hn hp l
    have hf := history_integer_roughness hN2 ht ht' hn hp (levelOccurrence_source l).1
    exact ⟨hd,P2OriginalPositiveSameQMassLift.sameQ_residual_gt_one (by omega) hd
        (frozenResidualFloor_pos.trans_le hL.1) hQ,hf.2.2⟩
  have hs (d : ℕ) (_ : d∈D) : 0≤σ d := sum_nonneg (fun l _ => (mark_pos _).le)
  have hi := hb N hNb hEven Q D σ (original_root_Q_le_target N n k t p hN2 ht ht' hp)
    (fun d hd => (data d hd).1) hs (fun d hd => (data d hd).2.1)
    (fun d hd => (data d hd).2.2.1) (fun d hd => (data d hd).2.2.2)
  rw [actual_marked_source_identity Q D σ hN4 hEven (fun d hd => (data d hd).1)] at hi
  have counts : (∑ l∈S,levelMark l*trueAt l) ≤ Phi N Q D σ (11/5) := by
    unfold Phi
    rw [weighted_fiber_sum]
    apply sum_le_sum
    intro l hl
    apply mul_le_mul_of_nonneg_left _ (mark_pos _).le
    have harg := (rootHistory_support (by omega : 1<N) ht ht' hn (original_band_prime hp)
      (original_band_geometry hN2 hp) (levelOccurrence_source l).1).2.2.2.1
    have hmono := below_two_comparison N (wordProduct l) (receiver N)
      ((data _ (mem_image_of_mem _ hl)).2.1.le) (zero_lt_one.trans_le harg.1)
      (seed_arg hN2 ht ht' hn hp hl)
    have hz := history_frozen_count_eq_true_quotient hN2 ht ht' hn hp (levelOccurrence_source l).1
    have hle : trueAt l ≤ (frozenCount N (wordProduct l) (receiver N)
        (cutoff Q (wordProduct l) (11/5)):ℝ) := by
      unfold trueAt
      rw [←hz]
      exact_mod_cast hmono
    apply hle.trans
    simp only [frozenCount,frozenCarrier,Int.cast_natCast,sourceSieveCount]
    exact_mod_cast card_le_card (filter_subset _ _)
  have hpaid := ha N hNa n k t p 0 ht ht' hn hp S
  have hθ : Theta N Q D σ=markedTheta S := real_word_theta S
  change J*markedTheta S ≤ (ordinaryPart*markedTheta S-(K/4)*converted N Q D σ)/5 at hpaid
  change 5*Phi N Q D σ (11/5)+negativeMean N Q D σ+piCenteredPhysicalError N Q D σ ≤
    4*Phi N Q D σ s0+Phi N Q D σ phi1+positivePairs N Q D σ+
      (∑ d∈D,σ d*actualLocalPrimeMass N Q d)+ε*Theta N Q D σ at hi
  change 5*((∑ l∈S,levelMark l*trueAt l)-(1-J)*markedTheta S) ≤
    signedAnchors N Q D σ+signedSingles N Q D σ+signedPositive N Q D σ+ε*markedTheta S
  unfold signedAnchors signedSingles signedPositive
  rw [hθ] at hi ⊢
  unfold ordinaryPart at hpaid
  linarith only [hi,counts,hpaid]

theorem actual_seed_source_debt {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      let Q := rootQ N n k t p
      let S := seedPositions N n k t p
      let D := S.image wordProduct
      let σ := groupedSigma S wordProduct levelMark
      5*((∑ l∈S,levelMark l*trueAt l) - (1-1/50:ℝ)*markedTheta S) ≤
        signedAnchors N Q D σ + signedSingles N Q D σ + signedPositive N Q D σ +
          ε*markedTheta S := by
  apply seed_source_debt_below_base hε
  exact (show (1/50:ℝ)<20249/1000000 by norm_num).trans
    P2SeedOmegaOriginalNumerical.actualJ2omega_gt_safe_base

end
end ImbalancedChen.Part5OriginalH430SignedSeedCount
