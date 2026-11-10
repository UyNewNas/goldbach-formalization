import ImbalancedChen.Part5OriginalH430BankOrdinarySingletons
import ImbalancedChen.Part5OriginalH430W1ArchivedFeedback

/-! Full signed ordinary contribution of all 70 W1 actions. The term left
for switching names the original masked triple count with its coefficient
one half and the exact reserve remaining in the stored Q80 base. -/
namespace ImbalancedChen.Part5OriginalH430W1SignedOrdinaryBase
noncomputable section
open Set Real Finset Filter Wu2008DoubleSieve
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels Part5OriginalUpsilon5CausalDictionary
open P2FrozenReceiverCountActions P5OriginalU5FrozenSource (receiver)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalHalfOpenProfileCarrier (below_two_comparison)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalPositiveSameQMassLift P2OriginalLiteralW1OldProfile
open P2AllW1FrozenReceiverFiniteAction P2OriginalBankOldProfilePassage
open P2Selected430CausalOccurrenceExporter (iterate)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430BankSlotTargets Part5OriginalH430FixedReadDictionary
open Part5OriginalH430SelectedFixedReadSupply Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430FixedReadRows Part5OriginalH430LiteralBankBudget
open Part5OriginalH430ImmutableBankProfiles (precedingH precedingh)
open Part5OriginalH430W1ArchivedFeedback Part5OriginalH430ActualFeedbackQuotientRemainders
open Part5OriginalH430SelectedOrdinaryPairCounts (trueAt) Part5OriginalH430SeedHistoryMass
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430BankOrdinarySingletons
open P5CanonicalUpperCancellation (upperA lowerBar)
open scoped Classical BigOperators Topology

def ordinaryBase (i : Fin 7) (j : Fin 10) : ℝ :=
  upperA (W1Target i) - upperA (W1Anchor j) + integral (.inl (i,j))/2

def fixedDebt (N : ℕ) (Q : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10) (g : Fin 430) : ℝ :=
  (frozenCount N d (receiver N) (cutoff Q d (W1Anchor j)):ℝ) -
    thetaAtom N Q d*(upperA (W1Anchor j)-fixedValue (precedingH g) (.inl (i,j)))

def lowerDebt (N : ℕ) (Q L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10) (g : Fin 430) : ℝ :=
  ∑ q∈window N Q L d (.inl (i,j)),
    thetaAtom N Q (d*q)*(lowerBar (argument N Q d q (.inl (i,j)))+
      tableFunction true (precedingh g) (argument N Q d q (.inl (i,j)))) -
      (frozenCount N (d*q) (receiver N) (cutoff Q d (W1Anchor j)):ℝ)

def switchedDebt (N : ℕ) (Q : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10) : ℝ :=
  (rawTripleCount N d (d*N) (receiver N) (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i)):ℝ)/2 -
    (ordinaryBase i j-baseValue (.inl (i,j)))*thetaAtom N Q d

private theorem archive_le_single (i : Fin 7) (j : Fin 10) (g : Fin 430) :
    idealFeedbackValue (iterate g.val) (.inl (i,j)) ≤
      singleOldIntegral (1/W1Anchor j) (1/W1Target i) (W1Anchor j) (precedingh g)/2 := by
  apply (immutable_w1_feedback_le_integral i j g).trans_eq
  rw [Fintype.sum_sum_type]
  simp only [dynamicIdeal,oldAtomValue,zero_mul,sum_const_zero,zero_add]
  simp_rw [div_mul_eq_mul_div]
  rw [←sum_div,singletonIntegralAtom_value (W1Domain_subset i j)]

private theorem profile_uniform {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ, ∀ N : ℕ,T≤N → ∀ (Q L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10) (g : Fin 430),
      L∈Icc frozenResidualFloor 1 → 0<d → Q=(d:ℝ)*(N:ℝ)^L →
      2≤P2OriginalChildPhysicalNormalization.alpha (log (d:ℝ)/log (N:ℝ)) L →
      0≤thetaAtom N Q d →
      thetaAtom N Q d*idealFeedbackValue (iterate g.val) (.inl (i,j)) ≤
        (∑ q∈primeWindow (d*N) (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i)),
          thetaAtom N Q (d*q)*tableFunction true (precedingh g)
            (argument N Q d q (.inl (i,j))))/2 + ε*thetaAtom N Q d := by
  have hF : frozenResidualFloor≤1 := by
    unfold frozenResidualFloor
    have h : (1:ℝ)≤101^440 := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h])
  have hprev (g : Fin 430) := all70_literal_sameQ_Theta_profile_passage
    frozenResidualFloor_pos hF he (precedingH g) (precedingh g)
  choose T hT using hprev
  refine ⟨univ.sup T,?_⟩
  intro N hN Q L d i j g hL hd hQ hα hθ
  have h := hT g N ((le_sup (mem_univ g)).trans hN) Q ({()} : Finset Unit)
    (fun _ => L) (fun _ => d) (fun _ => (1:ℝ)) (fun _ _ => hL) (fun _ _ => hd)
    (fun _ _ => hQ) (fun _ _ => zero_le_one) (fun _ _ => hα) i j
  simp only [sum_singleton,one_mul] at h
  have hl := (abs_le.mp h).1
  unfold literalW1ThetaOldProfile W1OldIntegral at hl
  have ha := mul_le_mul_of_nonneg_left (archive_le_single i j g) hθ
  change thetaAtom N Q d * idealFeedbackValue (iterate g.val) (.inl (i,j)) ≤
    (∑ q∈P2EnhancedActualBuchstabTransfer.childWindow N d Q (W1Target i) (W1Anchor j),
      thetaAtom N Q (d*q)*tableFunction true (precedingh g)
        (W1Anchor j*(1-log (q:ℝ)/log (Q/d))))/2 + ε*thetaAtom N Q d
  linarith only [hl,ha]

/-- The stored base, designated fixed cell and all archived old-h weights now
stand opposite the true requested quotient count. Only the old signed count
comparisons and the positive switched count minus its exact stored reserve
remain. Rank, labels, target and same-Q dependence remain inside the sum. -/
theorem selected_W1_signed_base {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ,T≤N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ (g : Fin 430) (i : Fin 7) (j : Fin 10), let S := selectedLevel N n k t p g (.inl (i,j))
      let Q := rootQ N n k t p
      (∑ l∈S,levelMark l*(trueAt l - thetaAtom N Q (wordProduct l) *
        (upperA (levelOccurrence l).current.node.physical.argument - baseValue (.inl (i,j)) -
          fixedValue (precedingH g) (.inl (i,j))-idealFeedbackValue (iterate g.val) (.inl (i,j))))) ≤
        (∑ l∈S,levelMark l*(fixedDebt N Q (wordProduct l) i j g +
          lowerDebt N Q (wordLevel l) (wordProduct l) i j g/2 +
          switchedDebt N Q (wordProduct l) i j)) + ε*markedTheta S := by
  obtain ⟨Ta,hTa,ha⟩ := all_original_singletons he
  obtain ⟨Tb,hb⟩ := profile_uniform (half_pos he)
  refine ⟨max Ta Tb,hTa.trans (le_max_left _ _),?_⟩
  intro N hN n k t p ht ht' hn hp g i j
  have hNa := (le_max_left Ta Tb).trans hN
  have hNb := (le_max_right Ta Tb).trans hN
  have hN4 := hTa.trans hNa
  have h1 : 1<N := by omega
  let S := selectedLevel N n k t p g (.inl (i,j))
  let Q := rootQ N n k t p
  dsimp only
  unfold markedTheta
  rw [mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro l hl
  let d := wordProduct l
  let L := wordLevel l
  let a : Lane := .inl (i,j)
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
  have hR := sameQ_residual_gt_one h1 hd (frozenResidualFloor_pos.trans_le hL.1) hQ
  have ho := (levelOccurrence_source l).1
  have hs := rootHistory_support h1 ht ht' hn (original_band_prime hp)
    (original_band_geometry (by omega) hp) ho
  have hc := rootHistory_coherent h1 ht ht' hn (original_band_prime hp)
    (original_band_geometry (by omega) hp) ho
  obtain ⟨u,hu⟩ := (mem_filter.mp hl).2
  have htar := (requested_bank_tests hc hu).2.1
  rw [action_slot] at htar
  change (levelOccurrence l).current.node.physical.argument ≤ W1Target i at htar
  have htar3 : W1Target i≤3 := by
    unfold W1Target; have hi : (i.val:ℝ)≤6 := by exact_mod_cast (show i.val≤6 by omega)
    linarith only [hi]
  have hpms := original_W1_parameters i j
  have hz := history_frozen_count_eq_true_quotient (by omega : 2≤N) ht ht' hn hp ho
  have htarg : trueAt l ≤ (frozenCount N d (receiver N) (cutoff Q d (W1Target i)):ℝ) := by
    unfold trueAt
    rw [←hz]
    exact_mod_cast below_two_comparison N d (receiver N) hR.le
      (zero_lt_one.trans_le hs.2.2.2.1.1) htar
  have horder : cutoff Q d (W1Anchor j) ≤ cutoff Q d (W1Target i) :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le (by linarith [hpms.1]) hpms.2.1)
  have hfinite : 2*(frozenCount N d (receiver N) (cutoff Q d (W1Target i)):ℝ) ≤
      2*(frozenCount N d (receiver N) (cutoff Q d (W1Anchor j)):ℝ) -
        (∑ q∈primeWindow (d*N) (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i)),
          (frozenCount N (d*q) (receiver N) (cutoff Q d (W1Anchor j)):ℝ)) +
        (rawTripleCount N d (d*N) (receiver N) (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i)):ℝ) := by
    exact_mod_cast frozen_selected_three_prime_weight N d (receiver N) horder
  have hmask := selected_W1_window (by omega : 2≤N) ht ht' hn hp i j l hl
  have hθ := thetaAtom_nonneg hN4 hd hR
  have hprof := hb N hNb Q L d i j g hL hd hQ hs.2.2.2.2.1 hθ
  rw [hmask] at hfinite hprof
  have hsingle := (abs_le.mp (ha N hNa n k t p (g.val+1) ht ht' hn hp l a)).1
  have hsource := P5CanonicalUpperCancellation.upperA_eq_one
    (zero_lt_one.trans_le hs.2.2.2.1.1) (htar.trans htar3)
  have htarget := P5CanonicalUpperCancellation.upperA_eq_one (by linarith [hpms.1]) htar3
  have hdecomp : lowerDebt N Q L d i j g =
      ordinaryWindow N Q L d a +
        (∑ q∈window N Q L d a,thetaAtom N Q (d*q) * tableFunction true (precedingh g)
          (argument N Q d q a)) -
        (∑ q∈window N Q L d a,(frozenCount N (d*q) (receiver N) (cutoff Q d (W1Anchor j)):ℝ)) := by
    simp only [lowerDebt,ordinaryWindow,a,mul_add,sum_sub_distrib,sum_add_distrib]
  have hpnt : trueAt l - thetaAtom N Q d *
      (upperA (levelOccurrence l).current.node.physical.argument - baseValue (.inl (i,j)) -
        fixedValue (precedingH g) (.inl (i,j))-idealFeedbackValue (iterate g.val) (.inl (i,j))) ≤
      fixedDebt N Q d i j g + lowerDebt N Q L d i j g/2 + switchedDebt N Q d i j +
        ε*thetaAtom N Q d := by
    rw [hdecomp,hsource]
    unfold fixedDebt switchedDebt ordinaryBase
    rw [htarget]
    dsimp only [a] at hsingle hprof ⊢
    linarith only [htarg,hfinite,hprof,hsingle]
  have scaled := mul_le_mul_of_nonneg_left hpnt (mark_pos (levelOccurrence l)).le
  simpa only [mul_add,mul_assoc,mul_left_comm,levelMark] using scaled

end
end ImbalancedChen.Part5OriginalH430W1SignedOrdinaryBase
