import ImbalancedChen.Part5OriginalH430LiteralBankBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The arithmetic limit is taken for each actual open-cell or knot atom,
before multiplication by an old table and before cancellation. The exact
repeated-prefix singular factors are retained. W1 uses the literal d*N
mask; W2 uses the original N mask. The finite threshold precedes N, L,
the integer prefix, and the choice of the old array.

This file does not identify these normalized bank carriers with the full
physical Member tree, and does not supply its switched bases.
-/

namespace ImbalancedChen.Part5OriginalH430TrueAtomLimits

noncomputable section
open Set MeasureTheory Filter Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalAffineProfilePassage
open P2OriginalClosedCellProfileAtoms P2OriginalCompactThetaMass
open P2OriginalOldProfilePrimeLimits P2OriginalPhysicalOldProfileMass
open P2OriginalBankOldProfilePassage P2OriginalProfileThetaNormalization
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2OriginalPrefixMaskMass P2OriginalLiteralW1OldProfile
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430ArithmeticAtomRows

def singleAtomDomain (lo hi s0 : ℝ) (b : FloorAtom) : Set (Coord 1) :=
  singleHalf lo hi ∩ tablePullback true (singleRho s0) b

def pairAtomDomain (p : W2Parameters) (k : Fin 4) (b : FloorAtom) : Set (Coord 2) :=
  pairHalf p k ∩ tablePullback false (pairProfile p k) b

def singleAtomIntegral (lo hi s0 : ℝ) (b : FloorAtom) : ℝ :=
  ∫ x in singleAtomDomain lo hi s0 b, residualSingle x * ∏ i, 1 / x i

def pairAtomIntegral (p : W2Parameters) (k : Fin 4) (b : FloorAtom) : ℝ :=
  ∫ x in pairAtomDomain p k b, residualPair x * ∏ i, 1 / x i

def trueSingleAtom (N : ℕ) (L : ℝ) (d : ℕ) (lo hi s0 : ℝ) (b : FloorAtom) : ℝ :=
  trueSingleTest N L d (singleAtomDomain lo hi s0 b) residualSingle

def truePairAtom (N : ℕ) (L : ℝ) (d : ℕ) (p : W2Parameters)
    (k : Fin 4) (b : FloorAtom) : ℝ :=
  truePairTest N L d (pairAtomDomain p k b) residualPair

/-- The original proper affine pullback supplier is applied to every
atom, including the closed knot atoms. No knot-mass limit is assumed. -/
theorem compact_uniform_single_atom {Lmin Lmax lo hi s0 epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (hlo : (1/5:ℝ) ≤ lo) (hhi : hi ≤ 1/2) (hs : 0 < s0)
    (b : FloorAtom) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      |trueSingleAtom N L d lo hi s0 b-singleAtomIntegral lo hi s0 b| < epsilon := by
  have hp := single_profile_form hs
  obtain ⟨Tp,hTp⟩ := compact_uniform_profile_atom hmin hmax
    (by norm_num : (0:ℝ) ≤ 10) (by positivity : (0:ℝ) < epsilon/2)
    singleForms (singleBounds lo hi) singleForms_ne (singleHalf_sandwich lo hi)
    (fun x hx i => by fin_cases i; exact ⟨hlo.trans hx.1,hx.2.le.trans hhi⟩)
    (s0 • coord 0) 0 s0 1 (singleRho s0) hp.1 (fun x _ => hp.2 x)
    (by intro x _; norm_num) residualSingle residualSingle_continuous
    (fun x => by rw [abs_of_nonneg (residualSingle_bounds x).1]; exact (residualSingle_bounds x).2)
    true b
  obtain ⟨Te,hTe⟩ := compact_multiplier_error (k := 1) hmin hmax
    (by norm_num : (0:ℝ) ≤ 20) (by positivity : (0:ℝ) < epsilon/2)
  refine ⟨max Tp Te, ?_⟩
  intro N hN L hL d
  obtain ⟨hA,he'⟩ := hTe N (by omega) L hL
  have hm := trueSingleTest_error d (singleAtomDomain lo hi s0 b) residualSingle
    (by norm_num : (0:ℝ) ≤ 10)
    (fun x => by rw [abs_of_nonneg (residualSingle_bounds x).1]; exact (residualSingle_bounds x).2) hA
  have hh := hTp N (by omega) L hL
  have ht := abs_sub_le (trueSingleAtom N L d lo hi s0 b)
    (scaledPrimeSum N L (singleAtomDomain lo hi s0 b) residualSingle)
    (singleAtomIntegral lo hi s0 b)
  change |trueSingleAtom N L d lo hi s0 b -
    scaledPrimeSum N L (singleAtomDomain lo hi s0 b) residualSingle| ≤ _ at hm
  change |scaledPrimeSum N L (singleAtomDomain lo hi s0 b) residualSingle -
    singleAtomIntegral lo hi s0 b| < epsilon/2 at hh
  norm_num only at hm
  linarith

theorem compact_uniform_pair_atom {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4) (b : FloorAtom) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      |truePairAtom N L d p k b-pairAtomIntegral p k b| < epsilon := by
  obtain ⟨hform,hrho,hden⟩ := pair_profile_form hp k
  obtain ⟨Tp,hTp⟩ := compact_uniform_profile_atom hmin hmax
    (by norm_num : (0:ℝ) ≤ 10) (by positivity : (0:ℝ) < epsilon/2)
    (pairForms k) (pairBounds p k) (pairForms_ne k) (pairHalf_sandwich p k)
    (fun x hx i => ⟨(pairHalf_geometry hp k hx).1.1 i,(pairHalf_geometry hp k hx).1.2 i⟩)
    (pairNumeratorForm p k) (pairDenominatorForm k) (pairNumeratorConstant p k)
    (pairDenominatorConstant k) (pairProfile p k) hform hrho hden
    residualPair residualPair_continuous
    (fun x => by rw [abs_of_nonneg (residualPair_bounds x).1]; exact (residualPair_bounds x).2)
    false b
  obtain ⟨Te,hTe⟩ := compact_multiplier_error (k := 2) hmin hmax
    (by norm_num : (0:ℝ) ≤ 60) (by positivity : (0:ℝ) < epsilon/2)
  refine ⟨max Tp Te, ?_⟩
  intro N hN L hL d
  obtain ⟨hA,he'⟩ := hTe N (by omega) L hL
  have hm := truePairTest_error d (pairAtomDomain p k b) residualPair
    (by norm_num : (0:ℝ) ≤ 10)
    (fun x => by rw [abs_of_nonneg (residualPair_bounds x).1]; exact (residualPair_bounds x).2) hA
  have hh := hTp N (by omega) L hL
  have ht := abs_sub_le (truePairAtom N L d p k b)
    (scaledPrimeSum N L (pairAtomDomain p k b) residualPair) (pairAtomIntegral p k b)
  change |truePairAtom N L d p k b -
    scaledPrimeSum N L (pairAtomDomain p k b) residualPair| ≤ _ at hm
  change |scaledPrimeSum N L (pairAtomDomain p k b) residualPair -
    pairAtomIntegral p k b| < epsilon/2 at hh
  norm_num only at hm
  linarith

def singleAtomTest (s0 : ℝ) (b : FloorAtom) (x : Coord 1) : ℝ :=
  (tablePullback true (singleRho s0) b).indicator residualSingle x

theorem singleAtomTest_bound (s0 : ℝ) (b : FloorAtom) (x : Coord 1) :
    |singleAtomTest s0 b x| ≤ 10 :=
  indicator_abs_bound _ _ (by norm_num)
    (fun y => by rw [abs_of_nonneg (residualSingle_bounds y).1]; exact (residualSingle_bounds y).2) x

def maskedSingleAtom (N : ℕ) (L : ℝ) (d : ℕ) (lo hi s0 : ℝ) (b : FloorAtom) : ℝ :=
  ∑ p ∈ primeWindow (d*N) ((N:ℝ)^(L*lo)) ((N:ℝ)^(L*hi)),
    localPrimeFactor d p * singleAtomTest s0 b (normalizedLog N L (fun _ : Fin 1 => p))

theorem trueSingleAtom_eq_N_window {N : ℕ} {L lo hi : ℝ}
    (hN : 1 < N) (hL : 0 < L) (hlo : (1/5:ℝ) ≤ lo) (hhi : hi ≤ 1/2)
    (d : ℕ) (s0 : ℝ) (b : FloorAtom) :
    trueSingleAtom N L d lo hi s0 b =
      ∑ p ∈ primeWindow N ((N:ℝ)^(L*lo)) ((N:ℝ)^(L*hi)),
        localPrimeFactor d p * singleAtomTest s0 b
          (normalizedLog N L (fun _ : Fin 1 => p)) := by
  symm
  rw [single_window_reindex hN hL hlo hhi]
  unfold trueSingleAtom trueSingleTest
  apply Finset.sum_congr rfl
  intro p _
  have hp : (fun _ : Fin 1 => p 0) = p := by funext i; fin_cases i; rfl
  rw [hp]
  by_cases hx : normalizedLog N L p ∈ singleHalf lo hi <;>
    by_cases hb : normalizedLog N L p ∈ tablePullback true (singleRho s0) b <;>
    simp [singleAtomDomain,singleAtomTest,hx,hb]

theorem compact_uniform_masked_single_atom {Lmin Lmax lo hi s0 epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (hlo : (1/5:ℝ) ≤ lo) (hhi : hi ≤ 1/2) (hs : 0 < s0) (b : FloorAtom) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ d : ℕ, 0 < d → d ≤ N →
      |maskedSingleAtom N L d lo hi s0 b-singleAtomIntegral lo hi s0 b| < epsilon := by
  obtain ⟨Tp,hTp⟩ := compact_uniform_single_atom hmin hmax
    (by positivity : (0:ℝ) < epsilon/2) hlo hhi hs b
  obtain ⟨Tm,hTm⟩ := compact_uniform_moving_prefixMask_difference hmin
    (by norm_num : (0:ℝ) ≤ 10) (by positivity : (0:ℝ) < epsilon/2)
  refine ⟨max 2 (max Tp Tm), ?_⟩
  intro N hN L hL d hd hdN
  have hm : |maskedSingleAtom N L d lo hi s0 b-trueSingleAtom N L d lo hi s0 b| < epsilon/2 := by
    rw [trueSingleAtom_eq_N_window (by omega) (hmin.trans_le hL.1) hlo hhi]
    exact hTm N (by omega) d hd hdN L lo hi hL.1 hlo _
      (fun q _ => singleAtomTest_bound s0 b _)
  have hp := hTp N (by omega) L hL d
  have ht := abs_sub_le (maskedSingleAtom N L d lo hi s0 b)
    (trueSingleAtom N L d lo hi s0 b) (singleAtomIntegral lo hi s0 b)
  linarith

/-- Exact child-Theta factorization for the actual N-window singleton
atom. The finite coefficient is present even when its limiting mass is zero. -/
theorem singleChildAtom_eq {N d : ℕ} {Q L lo hi s0 : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L) (hhi : hi ≤ 1/2)
    (hA : 4 ≤ (N:ℝ)^(L/10)) (hQ : Q = (d:ℝ)*(N:ℝ)^L) (b : FloorAtom) :
    singleChildAtom N Q L d lo hi s0 b =
      thetaAtom N Q d * trueSingleAtom N L d lo hi s0 b := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  unfold singleChildAtom profileAtomSum trueSingleAtom trueSingleTest
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 := mem_actualPrimeBoxTuples_iff.mp hp 0
  have hp2 : 2 < p 0 := by
    have hh := hA.trans hp0.2.2.1
    exact_mod_cast (show (2:ℝ) < p 0 by linarith)
  by_cases hx : normalizedLog N L p ∈ singleAtomDomain lo hi s0 b
  · rw [indicator_of_mem hx,indicator_of_mem hx]
    rw [thetaAtom_single (by omega) hd hp0.1 hp2
      (hp0.1.coprime_iff_not_dvd.mpr hp0.2.1) hR]
    have hlog : Real.log (p 0:ℝ)/Real.log (Q/d) = normalizedLog N L p 0 := by
      rw [hQ]; exact physical_log_ratio hN hd hL p 0
    rw [hlog]
    have hden : (1/10:ℝ) ≤ 1-normalizedLog N L p 0 := by linarith [hx.1.2]
    simp only [residualSingle,max_eq_right hden]
    ring
  · rw [indicator_of_notMem hx,indicator_of_notMem hx,mul_zero,mul_zero]

theorem pairChildAtom_eq {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hA : 4 ≤ (N:ℝ)^(L/10)) (hQ : Q = (d:ℝ)*(N:ℝ)^L)
    {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4) (b : FloorAtom) :
    pairChildAtom N Q L d p k b = thetaAtom N Q d * truePairAtom N L d p k b := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  unfold pairChildAtom profileAtomSum truePairAtom truePairTest
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 := mem_actualPrimeBoxTuples_iff.mp hq 0
  have hq1 := mem_actualPrimeBoxTuples_iff.mp hq 1
  have hq02 : 2 < q 0 := by
    have hh := hA.trans hq0.2.2.1
    exact_mod_cast (show (2:ℝ) < q 0 by linarith)
  have hq12 : 2 < q 1 := by
    have hh := hA.trans hq1.2.2.1
    exact_mod_cast (show (2:ℝ) < q 1 by linarith)
  by_cases hx : normalizedLog N L q ∈ pairAtomDomain p k b
  · rw [indicator_of_mem hx,indicator_of_mem hx]
    rw [thetaAtom_pair (by omega) hd hq0.1 hq1.1 hq02 hq12
      (hq0.1.coprime_iff_not_dvd.mpr hq0.2.1) (hq1.1.coprime_iff_not_dvd.mpr hq1.2.1) hR]
    have hlog (i : Fin 2) : Real.log (q i:ℝ)/Real.log (Q/d) = normalizedLog N L q i := by
      rw [hQ]; exact physical_log_ratio hN hd hL q i
    rw [hlog 0,hlog 1]
    have hden := (pairHalf_geometry hp k hx.1).2.1
    simp only [residualPair,max_eq_right
      (show (1/10:ℝ) ≤ 1-normalizedLog N L q 0-normalizedLog N L q 1 by linarith)]
    ring
  · rw [indicator_of_notMem hx,indicator_of_notMem hx,mul_zero,mul_zero]

theorem W1ChildAtom_eq {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hA : 4 ≤ (N:ℝ)^(L/10)) (hQ : Q = (d:ℝ)*(N:ℝ)^L)
    (i : Fin 7) (j : Fin 10) (b : FloorAtom) :
    W1ChildAtom N Q d i j b = thetaAtom N Q d *
      maskedSingleAtom N L d (1/W1Anchor j) (1/W1Target i) (W1Anchor j) b := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  have hNR : (1:ℝ) < N := by exact_mod_cast hN
  obtain ⟨hlo,hhi,hs⟩ := W1_endpoints i j
  have hcut (s : ℝ) : P2EnhancedTwentyOneSameQWeighted.cutoff Q d s =
      (N:ℝ)^(L*(1/s)) := by
    rw [cutoff_eq_physical_power hd hQ]
    congr 1
    ring
  unfold W1ChildAtom profileAtomSum maskedSingleAtom
  rw [P2EnhancedActualBuchstabTransfer.childWindow,hcut,hcut,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpm := mem_primeWindow.mp hp
  have hpN := (Nat.coprime_mul_iff_right.mp hpm.2.1).2
  have hfloor : (N:ℝ)^(L/10) ≤ (N:ℝ)^(L*(1/W1Anchor j)) :=
    Real.rpow_le_rpow_of_exponent_le hNR.le (by
      nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hlo)])
  have hp2 : 2 < p := by
    have hh : (4:ℝ) ≤ p := hA.trans (hfloor.trans hpm.2.2.1)
    exact_mod_cast (show (2:ℝ) < p by linarith)
  have hx : normalizedLog N L (fun _ : Fin 1 => p) ∈
      singleHalf (1/W1Anchor j) (1/W1Target i) :=
    (normalizedLog_window hN hL _ (fun _ => hpm.1.pos) 0 _ _).mpr
      ⟨hpm.2.2.1,hpm.2.2.2⟩
  have hlog : Real.log (p:ℝ)/Real.log (Q/d) =
      normalizedLog N L (fun _ : Fin 1 => p) 0 := by
    rw [hQ]
    exact physical_log_ratio hN hd hL (fun _ : Fin 1 => p) 0
  have hden : (1/10:ℝ) ≤ 1-normalizedLog N L (fun _ : Fin 1 => p) 0 := by
    linarith [hx.2]
  have hrho : W1Anchor j*(1-Real.log (p:ℝ)/Real.log (Q/d)) =
      singleRho (W1Anchor j) (normalizedLog N L (fun _ : Fin 1 => p)) := by
    rw [hlog]
    rfl
  by_cases hb : singleRho (W1Anchor j) (normalizedLog N L (fun _ : Fin 1 => p)) ∈
      tableAtomSet true b
  · have hpull : p ∈ (univ : Set ℕ) ∩ tablePullback true
        (fun q : ℕ => W1Anchor j*(1-Real.log (q:ℝ)/Real.log (Q/d))) b :=
      ⟨mem_univ _, by change W1Anchor j*(1-Real.log (p:ℝ)/Real.log (Q/d)) ∈ _; rwa [hrho]⟩
    have hnpull : normalizedLog N L (fun _ : Fin 1 => p) ∈
        tablePullback true (singleRho (W1Anchor j)) b := hb
    rw [indicator_of_mem hpull]
    unfold singleAtomTest
    rw [indicator_of_mem hnpull,thetaAtom_single (by omega) hd hpm.1 hp2 hpN hR,hlog]
    simp only [residualSingle,max_eq_right hden]
    ring
  · have hpull : p ∉ (univ : Set ℕ) ∩ tablePullback true
        (fun q : ℕ => W1Anchor j*(1-Real.log (q:ℝ)/Real.log (Q/d))) b := by
      intro h
      apply hb
      simpa only [← hrho] using h.2
    have hnpull : normalizedLog N L (fun _ : Fin 1 => p) ∉
        tablePullback true (singleRho (W1Anchor j)) b := hb
    rw [indicator_of_notMem hpull]
    unfold singleAtomTest
    rw [indicator_of_notMem hnpull,mul_zero,mul_zero]

end
end ImbalancedChen.Part5OriginalH430TrueAtomLimits
