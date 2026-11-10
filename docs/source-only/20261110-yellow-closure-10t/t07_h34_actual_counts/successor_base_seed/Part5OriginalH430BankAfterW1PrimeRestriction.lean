import ImbalancedChen.Part5OriginalH430W1FirstSquare
import ImbalancedChen.Part5OriginalH430BankAfterTrueW1Conversion

/-! Full 106-slot terminal after removing the actual first-letter exemption.
The W1 positive debt now compares the same inclusive integer carriers,
with and without their literal additive-prime condition. -/
namespace ImbalancedChen.Part5OriginalH430BankAfterW1PrimeRestriction
noncomputable section
open Set Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalPositiveSameQMassLift P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430BankSlotTargets Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger (selectedBankRoundingLoss)
open Part5OriginalH430ActualSelectedRowBudget (actualBankTheta)
open Part5OriginalH430SeedHistoryMass Part5OriginalH430AllBankSignedCounts
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430W1FirstSquare
open Part5OriginalH430W1TrueConvertedBase (primeDebt)
open Part5OriginalH430W1OriginalBaseEnclosure (currentK)
open Part5OriginalH430W1PhysicalRoughDictionary (integerMass)
open Part5OriginalH430BankAfterTrueW1Conversion (remaining full_bank_after_true_W1_conversion)
open scoped Classical BigOperators

def primeRestriction (N d : ℕ) (z w : ℝ) : ℝ :=
  ∑ t∈orderedTriples (primeWindow (d*N) z w),
    (((roughNumbers ((N:ℝ)/((d*t.1*t.2.1*t.2.2:ℕ):ℝ)) (t.2.1:ℝ)).filter
      (fun m => m∈chenQuotientPrimeSource N (d*t.1*t.2.1*t.2.2))).card:ℝ)

/-- The finite clean source equals the literal restriction of the independently
constructed unsifted integer carrier, including its unit endpoint. -/
theorem prime_restriction_eq (N d : ℕ) (z w : ℝ) (hd : 0<d) :
    cleanCount N d z w=primeRestriction N d z w := by
  unfold cleanCount primeRestriction
  apply sum_congr rfl
  intro t ht
  obtain ⟨hc,_⟩ := mem_filter.mp ht
  obtain ⟨ha,hbc⟩ := mem_product.mp hc
  obtain ⟨hb,hc'⟩ := mem_product.mp hbc
  have hp := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd (mem_primeWindow.mp ha).1.pos)
    (mem_primeWindow.mp hb).1.pos) (mem_primeWindow.mp hc').1.pos
  let D := d*t.1*t.2.1*t.2.2
  have heq : d*Part5OriginalH430W1FirstSquare.prod t=D := by dsimp [Part5OriginalH430W1FirstSquare.prod,D]; ring
  simp only [tail,heq]
  rw [←chenQuotientPrimeSource_filter_card N D (ChenPrimeRough (t.2.1:ℝ))]
  congr 2
  ext m
  rw [mem_filter,mem_filter,mem_roughNumbers]
  constructor
  · rintro ⟨hsrc,hr⟩
    obtain ⟨hell,he,rfl⟩ := mem_image.mp hsrc
    obtain ⟨ha,hdiv⟩ := mem_chenQuotientPrimeCarrier.mp he
    have hh := Nat.mul_div_cancel' hdiv
    have hq : (N-hell)/D∈chenQuotientPrimeSource N D := mem_image.mpr ⟨hell,he,rfl⟩
    refine ⟨⟨(chenQuotientPrimeSource_data hq).1,(le_div_iff₀ (Nat.cast_pos.mpr hp)).mpr ?_,hr⟩,hq⟩
    exact_mod_cast (show (N-hell)/D*D≤N by rw [mul_comm,hh]; exact Nat.sub_le _ _)
  · exact fun h => ⟨h.2,h.1.2.2⟩

def cleanDebt (N : ℕ) (Q : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10) : ℝ :=
  (primeRestriction N d (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i)) -
    (currentK:ℝ)/4*(thetaConversion N d*integerMass N Q d i j))/2

private theorem selected_gate {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}
    (hN : 2≤N) (ht : 0≤t) (ht' : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈originalBand N k) (i : Fin 7) (j : Fin 10) (l : Index N n k t p g)
    (hl : l∈selectedLevel N n k t p g (.inl (i,j))) :
    let Q := rootQ N n k t p; let d := wordProduct l
    (N:ℝ)^(frozenResidualFloor/5)≤cutoff Q d (W1Anchor j) ∧
      ChenPrimeRough (cutoff Q d (W1Target i)) d := by
  let Q := rootQ N n k t p
  let d := wordProduct l
  have h1 : 1<N := by omega
  have hNr : (1:ℝ)<N := by exact_mod_cast h1
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht ht' hn hp l
  have hR := sameQ_residual_gt_one h1 hd (frozenResidualFloor_pos.trans_le hL.1) hQ
  have hs := rootHistory_support h1 ht ht' hn (original_band_prime hp)
    (original_band_geometry hN hp) (levelOccurrence_source l).1
  have hc := rootHistory_coherent h1 ht ht' hn (original_band_prime hp)
    (original_band_geometry hN hp) (levelOccurrence_source l).1
  obtain ⟨b,hb⟩ := (mem_filter.mp hl).2
  have htar := (requested_bank_tests hc hb).2.1
  rw [action_slot] at htar
  change (levelOccurrence l).current.node.physical.argument≤W1Target i at htar
  have hold := (history_integer_roughness hN ht ht' hn hp (levelOccurrence_source l).1).1
  have hcut : cutoff Q d (W1Target i) ≤ cutoff Q d (levelOccurrence l).current.node.physical.argument :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le (zero_lt_one.trans_le hs.2.2.2.1.1) htar)
  have hm := P2AllW1FrozenReceiverFiniteAction.original_W1_parameters i j
  have hap : 0<W1Anchor j := by linarith [hm.1,hm.2.1]
  have hlp := frozenResidualFloor_pos.trans_le hL.1
  constructor
  · rw [cutoff_eq_physical_power hd hQ]
    apply rpow_le_rpow_of_exponent_le hNr.le
    calc
      _ ≤ wordLevel l/5 := div_le_div_of_nonneg_right hL.1 (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left hlp.le hap hm.2.2
  · exact fun r hr hrd => hcut.trans (hold r hr hrd)

def finalDebt (N : ℕ) (Q L : ℝ) (d : ℕ) (g : Fin 430) : Original106Action → ℝ
  | .inl (i,j) => Part5OriginalH430W1SignedOrdinaryBase.fixedDebt N Q d i j g+
      Part5OriginalH430W1SignedOrdinaryBase.lowerDebt N Q L d i j g/2+cleanDebt N Q d i j
  | .inr j => Part5OriginalH430W2SignedOrdinaryBase.rowDebt N Q L d j g

theorem full_bank_after_W1_prime_restriction {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (root : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N root →
      ∀ g : Fin 430,
        (∑ a : Original106Action, ∑ l∈selectedLevel N n root t p g a,
          levelMark l*physicalDefect l)+selectedBankRoundingLoss N n root t p g ≤
        (∑ a : Original106Action, ∑ l∈selectedLevel N n root t p g a,
          levelMark l*finalDebt N (rootQ N n root t p) (wordLevel l) (wordProduct l) g a)+
          ε*actualBankTheta N n root t p g := by
  obtain ⟨Ta,hTa,ha⟩ := full_bank_after_true_W1_conversion (half_pos he)
  obtain ⟨Tb,hTb,hb⟩ := true_clean_count (div_pos frozenResidualFloor_pos (by norm_num : (0:ℝ)<5)) he
  refine ⟨max Ta Tb,hTa.trans (le_max_left _ _),?_⟩
  intro N hN hEven n root t p ht ht' hn hp g
  have hNa := (le_max_left _ _).trans hN
  have hNb := (le_max_right _ _).trans hN
  have h4 := hTa.trans hNa
  let Q := rootQ N n root t p
  let S := selectedLevel N n root t p g
  have hu := ha N hNa hEven n root t p ht ht' hn hp g
  have hr : (∑ a : Original106Action,∑ l∈S a,levelMark l*remaining N Q (wordLevel l) (wordProduct l) g a) ≤
      (∑ a : Original106Action,∑ l∈S a,levelMark l*finalDebt N Q (wordLevel l) (wordProduct l) g a)+
        ε/2*actualBankTheta N n root t p g := by
    unfold actualBankTheta
    rw [mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro a _
    unfold levelTheta
    rw [mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro l hl
    obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
    have hR := sameQ_residual_gt_one (by omega) hd (frozenResidualFloor_pos.trans_le hL.1) hQ
    have hθ := thetaAtom_nonneg h4 hd hR
    have hmark := (mark_pos (levelOccurrence l)).le
    rcases a with ⟨i,j⟩ | j
    · let d := wordProduct l
      obtain ⟨hz,hrough⟩ := selected_gate (by omega) ht ht' hn hp i j l hl
      have hR' : Q/(d:ℝ)≤(N:ℝ) := by
        have hscale : Q/(d:ℝ)=(N:ℝ)^(wordLevel l) := by
          rw [show Q=(d:ℝ)*(N:ℝ)^(wordLevel l) from hQ]
          field_simp [(Nat.cast_pos.mpr hd).ne']
        rw [hscale]
        simpa using rpow_le_rpow_of_exponent_le (show (1:ℝ)≤N by exact_mod_cast (show 1≤N by omega)) hL.2
      have h := hb N hNb Q d (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i)) hd hR hR' hz hrough
      rw [prime_restriction_eq _ _ _ _ hd] at h
      have h' : primeDebt N Q d i j≤cleanDebt N Q d i j+ε/2*thetaAtom N Q d := by
        unfold primeDebt cleanDebt; linarith only [h]
      dsimp only [remaining,finalDebt]
      linarith only [mul_le_mul_of_nonneg_left h' hmark]
    · dsimp only [remaining,finalDebt]
      exact le_add_of_nonneg_right (mul_nonneg (half_pos he).le (mul_nonneg hmark hθ))
  dsimp only [S,Q] at hr
  linarith only [hu,hr]

end
end ImbalancedChen.Part5OriginalH430BankAfterW1PrimeRestriction
