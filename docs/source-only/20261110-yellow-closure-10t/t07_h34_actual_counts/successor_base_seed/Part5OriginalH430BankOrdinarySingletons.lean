import ImbalancedChen.Part5OriginalH430OrdinarySingletonKernel
import ImbalancedChen.Part5OriginalH430SelectedOrdinaryPairCounts
import ImbalancedChen.P2OriginalLiteralW1OldProfile

/-! The 70 W1 negative windows and the three W2 windows in each of the
36 actions. The old-prefix exclusion in a selected W1 window is empty
by the actual history's integer roughness, even before taking limits. -/
namespace ImbalancedChen.Part5OriginalH430BankOrdinarySingletons
noncomputable section
open Set Real Finset Filter Wu2008DoubleSieve
open P5OriginalActionMassBound P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalPositiveSameQMassLift P2OriginalCompactThetaMass
open P2OriginalHalfOpenProfileCarrier P2OriginalBankOldProfilePassage
open P2AllW1FrozenReceiverFiniteAction P2OriginalLiteralW1OldProfile
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open Part5OriginalH430SeedHistoryMass Part5OriginalH430OrdinarySingletonKernel
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedAdmission Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430HistoryQuotientCounts
open Part5OriginalH430W2UpperPolygons (parameterQ original_parameters physical)
open scoped Classical BigOperators Topology

abbrev Lane := (Fin 7 × Fin 10) ⊕ (Fin 36 × Fin 3)

def anchor : Lane → ℝ
  | .inl (_,j) => W1Anchor j
  | .inr (j,_) => (originalW2At j).s0

def top : Lane → ℝ
  | .inl (i,_) => 1/W1Target i
  | .inr (j,k) => singletonTop (originalW2At j) k

def leftQ : Lane → ℚ
  | .inl (_,j) => 1/(16/5+(j.val:ℚ)/5)
  | .inr (j,_) => 1/(parameterQ j 1)

theorem original_left (a : Lane) : (leftQ a:ℝ)=1/(anchor a) := by
  obtain ⟨i,j⟩ | ⟨j,k⟩ := a
  · simp [leftQ,anchor,W1Anchor]
  · change ((1/parameterQ j 1 : ℚ):ℝ)=1/(originalW2At j).s0
    rw [← original_parameters j]
    simp [physical]

private theorem endpoints (a : Lane) :
    (1/5:ℝ)≤(leftQ a:ℝ) ∧ top a≤1/2 ∧ 0<anchor a ∧ anchor a≤5 := by
  rw [original_left]
  obtain ⟨i,j⟩ | ⟨j,k⟩ := a
  · have h := W1_endpoints i j
    exact ⟨h.1,h.2.1,h.2.2,(original_W1_parameters i j).2.2⟩
  · have h := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
    exact ⟨h.1,W2_singleton_top h k,P5OriginalFeedbackDomains.W2_anchor_positive h,
      P5OriginalFeedbackDomains.W2_anchor_le_five h⟩

def window (N : ℕ) (Q L : ℝ) (d : ℕ) (a : Lane) : Finset ℕ :=
  primeWindow N (cutoff Q d (anchor a)) ((N:ℝ)^(L*top a))

def argument (N : ℕ) (Q : ℝ) (d q : ℕ) (a : Lane) : ℝ :=
  anchor a*(1-log (q:ℝ)/log (Q/d))

def ordinaryWindow (N : ℕ) (Q L : ℝ) (d : ℕ) (a : Lane) : ℝ :=
  ∑ q∈window N Q L d a, thetaAtom N Q (d*q)*P5CanonicalUpperCancellation.lowerBar (argument N Q d q a)

def integral (a : Lane) : ℝ := ordinaryLowerIntegral (1/anchor a) (top a) (anchor a)

private theorem window_eq_true {N n p d : ℕ} {k : Root} {t L : ℝ}
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (hQ : rootQ N n k t p=(d:ℝ)*(N:ℝ)^L)
    (a : Lane) : ordinaryWindow N (rootQ N n k t p) L d a =
      weightedLower N (rootQ N n k t p) L d (leftQ a) (top a) (anchor a) := by
  have h := endpoints a
  unfold ordinaryWindow window
  rw [cutoff_eq_physical_power hd hQ,show L/anchor a=L*(leftQ a:ℝ) by rw [original_left]; ring,
    single_window_reindex hN hL h.1 h.2.1]
  apply sum_congr rfl
  intro x _
  have hlog : log (x 0:ℝ)/log (rootQ N n k t p/d)=normalizedLog N L x 0 := by
    rw [hQ]; exact physical_log_ratio hN hd hL x 0
  simp only [argument,hlog]

theorem all_original_singletons {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ,T≤N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ (l : LevelIndex N n k t p dep) (a : Lane), let Q := rootQ N n k t p
      let d := wordProduct l; let L := wordLevel l
      |ordinaryWindow N Q L d a-thetaAtom N Q d*integral a|≤ε*thetaAtom N Q d := by
  have hF : frozenResidualFloor≤1 := by
    unfold frozenResidualFloor
    have h : (1:ℝ)≤101^440 := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h])
  have hm (a : Lane) := moving_ordinary_lower frozenResidualFloor_pos hF (endpoints a).1
    (endpoints a).2.1 (endpoints a).2.2.1.le (endpoints a).2.2.2 he
  choose T hT using hm
  obtain ⟨Ta,ha⟩ := compact_multiplier_error (k:=1) frozenResidualFloor_pos hF
    (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)<1)
  let M := max 4 (max Ta (univ.sup T))
  refine ⟨M,le_max_left _ _,?_⟩
  intro N hNM n k t p dep ht ht' hn hp l a
  have hN4 : 4≤N := (le_max_left _ _).trans hNM
  have hNa : Ta≤N := ((le_max_left _ _).trans (le_max_right _ _)).trans hNM
  have hNT : T a≤N := (le_sup (mem_univ a)).trans
    (((le_max_right _ _).trans (le_max_right _ _)).trans hNM)
  obtain ⟨hd,hRange,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
  have hL := frozenResidualFloor_pos.trans_le hRange.1
  have h1 : 1<N := by omega
  have hθ := thetaAtom_nonneg hN4 hd (sameQ_residual_gt_one h1 hd hL hQ)
  have h := hT a N hNT (wordLevel l) hRange (wordProduct l)
  dsimp only
  rw [window_eq_true h1 hd hL hQ,weightedLower_eq (leftQ a) h1 hd hL (endpoints a).1
    (endpoints a).2.1 (endpoints a).2.2.1.le (endpoints a).2.2.2 (ha N hNa _ hRange).1 hQ,
    integral,←original_left,←mul_sub,abs_mul,abs_of_nonneg hθ,mul_comm ε]
  exact mul_le_mul_of_nonneg_left h.le hθ

theorem selected_W1_window {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}
    (hN : 2≤N) (ht : 0≤t) (ht' : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈originalBand N k) (i : Fin 7) (j : Fin 10) (l : Index N n k t p g)
    (hl : l∈selectedLevel N n k t p g (.inl (i,j))) :
    let Q := rootQ N n k t p; let d := wordProduct l
    primeWindow (d*N) (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i)) =
      window N Q (wordLevel l) d (.inl (i,j)) := by
  dsimp only
  have h1 : 1<N := by omega
  have hs := rootHistory_support h1 ht ht' hn (original_band_prime hp)
    (original_band_geometry hN hp) (levelOccurrence_source l).1
  have hc := rootHistory_coherent h1 ht ht' hn (original_band_prime hp)
    (original_band_geometry hN hp) (levelOccurrence_source l).1
  obtain ⟨b,hb⟩ := (mem_filter.mp hl).2
  have htar := (requested_bank_tests hc hb).2.1
  rw [action_slot] at htar
  change (levelOccurrence l).current.node.physical.argument≤W1Target i at htar
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht ht' hn hp l
  have hR := sameQ_residual_gt_one h1 hd (frozenResidualFloor_pos.trans_le hL.1) hQ
  have hrough := (history_integer_roughness hN ht ht' hn hp (levelOccurrence_source l).1).1
  have hcut : cutoff (rootQ N n k t p) (wordProduct l) (W1Target i) ≤
      cutoff (rootQ N n k t p) (wordProduct l) (levelOccurrence l).current.node.physical.argument :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le (zero_lt_one.trans_le hs.2.2.2.1.1) htar)
  have htop : (N:ℝ)^(wordLevel l*top (.inl (i,j))) = cutoff (rootQ N n k t p) (wordProduct l) (W1Target i) := by
    rw [cutoff_eq_physical_power hd hQ]
    congr 1
    change _*(1/W1Target i)=_
    ring
  rw [window,htop]
  ext q
  simp only [mem_primeWindow,Nat.coprime_mul_iff_right,anchor]
  constructor
  · rintro ⟨hpr,⟨_,hnq⟩,hz⟩
    exact ⟨hpr,hnq,hz⟩
  · rintro ⟨hpr,hnq,hlo,hhi⟩
    refine ⟨hpr,⟨hpr.coprime_iff_not_dvd.mpr ?_,hnq⟩,hlo,hhi⟩
    exact fun hqd => (not_lt_of_ge (hrough q hpr hqd)) (hhi.trans_le hcut)

end
end ImbalancedChen.Part5OriginalH430BankOrdinarySingletons
