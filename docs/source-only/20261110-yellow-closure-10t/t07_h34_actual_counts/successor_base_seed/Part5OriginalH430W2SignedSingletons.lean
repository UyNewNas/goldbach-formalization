import ImbalancedChen.Part5OriginalH430BankOrdinarySingletons

namespace ImbalancedChen.Part5OriginalH430W2SignedSingletons
noncomputable section
open Set Real Finset Wu2008DoubleSieve
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2FrozenReceiverCountActions P5OriginalU5FrozenSource (receiver)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2W2PhysicalChildFeedback P2OriginalW2CountTupleReindex P2OriginalBankChildPrimeMass
open P2OriginalBankThetaMassLimits P2OriginalProfileThetaNormalization
open P2OriginalBankOldProfilePassage P2OriginalHalfOpenProfileCarrier P2OriginalCompactThetaMass
open P2OriginalPositiveSameQMassLift P2OriginalLiteralW1OldProfile
open P2OriginalChildPhysicalNormalization (thetaAtom)
open Part5OriginalH430SeedHistoryMass Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ImmutableBankProfiles (precedingH precedingh)
open Part5OriginalH430W2ArchivedSingletons (archivedChannel immutable_w2_singletons_le_integral)
open Part5OriginalH430LiteralBankBudget Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430ActualFeedbackQuotientRemainders Part5OriginalH430FixedReadRows
open Part5OriginalH430OrdinaryPairCounts
open P2Selected430CausalOccurrenceExporter (iterate)
open scoped Classical BigOperators

def stop (j : Fin 36) (k : Fin 3) : ℝ :=
  ![(originalW2At j).s,(originalW2At j).phi2,(originalW2At j).phi3] k

theorem top_eq (j : Fin 36) (k : Fin 3) : top (.inr (j,k)) = 1/stop j k := by fin_cases k <;> rfl

def oldLower (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 3) (g : Fin 430) : ℝ :=
  ∑ q∈window N Q L d (.inr (j,k)), thetaAtom N Q (d*q) *
    tableFunction true (precedingh g) (argument N Q d q (.inr (j,k)))

def negative (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 3) : ℝ :=
  negativeWindow N Q (receiver N) (actualState N) d (cutoff Q d (originalW2At j).s0)
    (cutoff Q d (stop j k))

def lowerDebt (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 3) (g : Fin 430) : ℝ :=
  ∑ q∈window N Q L d (.inr (j,k)), thetaAtom N Q (d*q) *
    (P5CanonicalUpperCancellation.lowerBar (argument N Q d q (.inr (j,k))) +
      tableFunction true (precedingh g) (argument N Q d q (.inr (j,k)))) -
      (frozenCount N (d*q) (receiver N) (cutoff Q d (originalW2At j).s0):ℝ)

theorem lowerDebt_eq {N d : ℕ} {Q L : ℝ} (hd : 0<d) (hQ : Q=(d:ℝ)*(N:ℝ)^L)
    (j : Fin 36) (k : Fin 3) (g : Fin 430) :
    lowerDebt N Q L d j k g = ordinaryWindow N Q L d (.inr (j,k)) +
      oldLower N Q L d j k g - negative N Q d j k := by
  have htop : (N:ℝ)^(L*top (.inr (j,k)))=cutoff Q d (stop j k) := by
    rw [top_eq,cutoff_eq_physical_power hd hQ]; congr 1; ring
  unfold lowerDebt ordinaryWindow oldLower negative negativeWindow window
  simp only [mul_add,sum_sub_distrib,sum_add_distrib,anchor,htop,negativeChild,actualState,ite_self]

theorem oldLower_eq {N d : ℕ} {Q L : ℝ} (hN : 1<N) (hd : 0<d) (hL : 0<L)
    (hQ : Q=(d:ℝ)*(N:ℝ)^L) (j : Fin 36) (k : Fin 3) (g : Fin 430) :
    oldLower N Q L d j k g = singleThetaOldProfile N Q L d (a0 (originalW2At j))
      (singletonTop (originalW2At j) k) (originalW2At j).s0 true (precedingh g) := by
  have hgeo := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  unfold oldLower window
  rw [cutoff_eq_physical_power hd hQ,show L/anchor (.inr (j,k))=L*a0 (originalW2At j) by
    change L/(originalW2At j).s0=L*(1/(originalW2At j).s0); ring,
    single_window_reindex hN hL hgeo.1 (W2_singleton_top hgeo k)]
  apply sum_congr rfl
  intro x _
  have hx : log (x 0:ℝ)/log (Q/d)=normalizedLog N L x 0 := by
    rw [hQ]; exact physical_log_ratio hN hd hL x 0
  simp only [argument,anchor,top,hx,P2OriginalOldProfilePrimeLimits.singleRho]

theorem archive_lower (j : Fin 36) (g : Fin 430) :
    5*archivedChannel (iterate g.val) j false ≤
      ∑ k : Fin 3,singleOldIntegral (a0 (originalW2At j)) (singletonTop (originalW2At j) k)
        (originalW2At j).s0 (precedingh g) := by
  have hh := immutable_w2_singletons_le_integral j g
  change _ ≤ ∑ b : FloorAtom, ((∑ k : Fin 3,singletonIntegralAtom (a0 (originalW2At j))
    (singletonTop (originalW2At j) k) (originalW2At j).s0 b)/5)*floorAtomValue (precedingh g) b at hh
  simp_rw [div_mul_eq_mul_div,sum_mul] at hh
  rw [←sum_div,sum_comm] at hh
  have hgeom := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have hk (k : Fin 3) : Ioo (a0 (originalW2At j)) (singletonTop (originalW2At j) k) ⊆
      singletonAmbient := by
    have hd : Ioo (a0 (originalW2At j)) (singletonTop (originalW2At j) k) =
        W2SingletonDomain (originalW2At j) k := by fin_cases k <;> rfl
    rw [hd]; exact W2SingletonDomain_subset hgeom k
  simp_rw [singletonIntegralAtom_value (hk _)] at hh
  linarith only [hh]

/-- Original three singleton counts, including their own old-h scalar readings.
The two finite quadratures share the same positive parent atom. -/
theorem all_W2_singles_signed {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (n : ℕ) (rt : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N rt →
      ∀ (l : LevelIndex N n rt t p dep) (g : Fin 430) (j : Fin 36),
      let Q := rootQ N n rt t p; let d := wordProduct l; let L := wordLevel l
      thetaAtom N Q d*((∑ k : Fin 3, integral (.inr (j,k)))+5*archivedChannel (iterate g.val) j false) -
        (∑ k : Fin 3, negative N Q d j k) ≤
        (∑ k : Fin 3,lowerDebt N Q L d j k g) + ε*thetaAtom N Q d := by
  have he6 : 0<ε/6 := by positivity
  obtain ⟨To,hTo,ho⟩ := all_original_singletons he6
  have hF : frozenResidualFloor≤1 := by
    unfold frozenResidualFloor
    have h : (1:ℝ)≤101^440 := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h])
  have hprev (g : Fin 430) := all36_three_true_old_h_profiles frozenResidualFloor_pos hF he6 (precedingh g)
  choose T hT using hprev
  obtain ⟨Ta,ha⟩ := compact_multiplier_error (k:=1) frozenResidualFloor_pos hF
    (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)<1)
  let M := max To (max Ta (univ.sup T))
  refine ⟨M,hTo.trans (le_max_left _ _),?_⟩
  intro N hNM n rt t p dep ht ht' hn hp l g j
  have hNo : To≤N := (le_max_left _ _).trans hNM
  have hNa : Ta≤N := ((le_max_left _ _).trans (le_max_right _ _)).trans hNM
  have hNg : T g≤N := (le_sup (mem_univ g)).trans (((le_max_right _ _).trans (le_max_right _ _)).trans hNM)
  have hN4 := hTo.trans hNo
  obtain ⟨hd,hRange,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
  have hL := frozenResidualFloor_pos.trans_le hRange.1
  have h1 : 1<N := by omega
  let Q := rootQ N n rt t p
  let L := wordLevel l
  let d := wordProduct l
  let θ := thetaAtom N Q d
  have hθ : 0≤θ := thetaAtom_nonneg hN4 hd (sameQ_residual_gt_one h1 hd hL hQ)
  let I := fun k : Fin 3 => singleOldIntegral (a0 (originalW2At j)) (singletonTop (originalW2At j) k)
    (originalW2At j).s0 (precedingh g)
  have row (k : Fin 3) : θ*(integral (.inr (j,k))+I k) - negative N Q d j k ≤
      lowerDebt N Q L d j k g+(ε/3)*θ := by
    have h1' := (abs_le.mp (ho N hNo n rt t p dep ht ht' hn hp l (.inr (j,k)))).1
    have hp' := (abs_lt.mp (hT g N hNg L hRange d j k)).1.le
    have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
    have hp'' := mul_le_mul_of_nonneg_left hp' hθ
    rw [lowerDebt_eq hd hQ,oldLower_eq h1 hd hL hQ,singleThetaOldProfile_eq h1 hd hL
      (W2_singleton_top hg k) (ha N hNa L hRange).1 hQ]
    dsimp only [I,θ,Q,L,d] at *
    linarith only [h1',hp'']
  have hsum := sum_le_sum (s:=univ) (fun k _ => row k)
  simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_ofNat] at hsum
  have hbind := mul_le_mul_of_nonneg_left (archive_lower j g) hθ
  change θ*((∑ k : Fin 3,integral (.inr (j,k)))+5*archivedChannel (iterate g.val) j false) -
    (∑ k : Fin 3,negative N Q d j k) ≤ (∑ k : Fin 3,lowerDebt N Q L d j k g)+ε*θ
  dsimp only [I] at hsum
  linarith only [hsum,hbind]

end
end ImbalancedChen.Part5OriginalH430W2SignedSingletons
