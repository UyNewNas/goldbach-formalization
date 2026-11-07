import ImbalancedChen.P2OriginalProfileThetaNormalization
import ImbalancedChen.P2OriginalPrefixMaskMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original W1 childWindow deletes primes dividing d*N. The frozen O
profile theorem instead enumerates primes not dividing N and keeps the
repeated-prefix lane. These are not equal carriers. The P prefix-mask
supplier pays their actual signed difference on the physical alpha range.
W2 restored windows use N and are deliberately left unchanged.
-/
namespace ImbalancedChen.P2OriginalLiteralW1OldProfile

noncomputable section
open Set MeasureTheory Filter Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalBankThetaMassLimits P2OriginalHalfOpenProfileCarrier
open P2OriginalOldProfilePrimeLimits P2OriginalPhysicalOldProfileMass
open P2OriginalBankOldProfilePassage P2OriginalProfileThetaNormalization
open P2OriginalPositiveSameQMassLift P2OriginalCompactThetaMass
open P2OriginalPrefixMaskMass P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary (floorBound floorBound_nonneg)

/-- The manuscript's true alpha range supplies the needed prefix bound;
the arbitrary-prefix O theorem alone would not supply it. -/
theorem prefix_le_target_of_true_alpha {N d : ℕ} {L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (ha : 2 ≤ alpha (Real.log (d:ℝ)/Real.log (N:ℝ)) L) : d ≤ N := by
  have hNR : (1:ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N:ℝ) := Real.log_pos hNR
  change 2 ≤ (1-Real.log (d:ℝ)/Real.log (N:ℝ))/L at ha
  have halpha : 2*L ≤ 1-Real.log (d:ℝ)/Real.log (N:ℝ) :=
    (le_div_iff₀ hL).mp ha
  have hquot : Real.log (d:ℝ)/Real.log (N:ℝ) ≤ 1 := by linarith
  have hlog : Real.log (d:ℝ) ≤ Real.log (N:ℝ) := by
    simpa only [one_mul] using (div_le_iff₀ hlogN).mp hquot
  have hreal := (Real.log_le_log_iff (Nat.cast_pos.mpr hd)
    (zero_lt_one.trans hNR)).mp hlog
  exact_mod_cast hreal

/-- Reindex the implemented O sum before changing its target mask. -/
theorem true_single_eq_N_window {N : ℕ} {L lo hi : ℝ}
    (hN : 1 < N) (hL : 0 < L) (hlo : (1/5:ℝ) ≤ lo) (hhi : hi ≤ 1/2)
    (d : ℕ) (s0 : ℝ) (lower : Bool) (nums : Fin 200 → ℤ) :
    trueSingleOldProfile N L d lo hi s0 lower nums =
      ∑ p ∈ primeWindow N ((N:ℝ)^(L*lo)) ((N:ℝ)^(L*hi)),
        localPrimeFactor d p * singleTest s0 lower nums
          (normalizedLog N L (fun _ : Fin 1 => p)) := by
  symm
  rw [single_window_reindex hN hL hlo hhi]
  unfold trueSingleOldProfile trueSingleTest
  apply Finset.sum_congr rfl
  intro p _
  have hp : (fun _ : Fin 1 => p 0) = p := by
    funext i
    fin_cases i
    rfl
  rw [hp]
  by_cases hx : normalizedLog N L p ∈ singleHalf lo hi
  · simp only [if_pos hx,indicator_of_mem hx]
  · simp only [if_neg hx,indicator_of_notMem hx,mul_zero]

def maskedSingleOldProfile (N : ℕ) (L : ℝ) (d : ℕ) (lo hi s0 : ℝ)
    (lower : Bool) (nums : Fin 200 → ℤ) : ℝ :=
  ∑ p ∈ primeWindow (d*N) ((N:ℝ)^(L*lo)) ((N:ℝ)^(L*hi)),
    localPrimeFactor d p * singleTest s0 lower nums
      (normalizedLog N L (fun _ : Fin 1 => p))

def maskedW1OldProfile (N : ℕ) (L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10)
    (oldH oldh : Fin 200 → ℤ) : ℝ :=
  tableFunction false oldH (W1Anchor j) +
    maskedSingleOldProfile N L d (1/W1Anchor j) (1/W1Target i)
      (W1Anchor j) true oldh/2

/-- Literal original childWindow and original inherited profile argument.
The half-open endpoints and unchanged-prefix H atom remain literal. -/
def literalW1ThetaOldProfile (N : ℕ) (Q : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10)
    (oldH oldh : Fin 200 → ℤ) : ℝ :=
  thetaAtom N Q d * tableFunction false oldH (W1Anchor j) +
    (∑ p ∈ P2EnhancedActualBuchstabTransfer.childWindow N d Q (W1Target i) (W1Anchor j),
      thetaAtom N Q (d*p) * tableFunction true oldh
        (W1Anchor j * (1-Real.log (p:ℝ)/Real.log (Q/d))))/2

theorem cutoff_eq_physical_power {N d : ℕ} {Q L s : ℝ}
    (hd : 0 < d) (hQ : Q = (d:ℝ)*(N:ℝ)^L) :
    P2EnhancedTwentyOneSameQWeighted.cutoff Q d s = (N:ℝ)^(L/s) := by
  have hres : Q/(d:ℝ) = (N:ℝ)^L := by
    rw [hQ]
    field_simp [(Nat.cast_pos.mpr hd).ne']
  unfold P2EnhancedTwentyOneSameQWeighted.cutoff
  rw [hres,← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  ring

/-- The error supplier accepts the signed, discontinuous old table test.
Its primitive bound is proved by O, rather than a profile limit premise. -/
theorem all70_masked_old_profile_passage {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (oldH oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ d : ℕ, 0 < d → d ≤ N → ∀ i : Fin 7, ∀ j : Fin 10,
        |maskedW1OldProfile N L d i j oldH oldh-W1OldIntegral i j oldH oldh| < epsilon := by
  obtain ⟨Tp,hTp⟩ := all70_true_old_h_profile hmin hmax
    (by positivity : (0:ℝ) < epsilon/2) oldh
  obtain ⟨Tm,hTm⟩ := compact_uniform_moving_prefixMask_difference hmin
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) (floorBound_nonneg oldh))
    (by positivity : (0:ℝ) < epsilon/2)
  refine ⟨max 2 (max Tp Tm),?_⟩
  intro N hN L hL d hd hdN i j
  have hN1 : 1 < N := by omega
  have hL0 : 0 < L := hmin.trans_le hL.1
  obtain ⟨hlo,hhi,hs⟩ := W1_endpoints i j
  have hm : |maskedSingleOldProfile N L d (1/W1Anchor j) (1/W1Target i)
      (W1Anchor j) true oldh-
      trueSingleOldProfile N L d (1/W1Anchor j) (1/W1Target i)
        (W1Anchor j) true oldh| < epsilon/2 := by
    rw [true_single_eq_N_window hN1 hL0 hlo hhi]
    exact hTm N (by omega) d hd hdN L _ _ hL.1 hlo _
      (fun p _ => singleTest_bound (W1Anchor j) true oldh _)
  have hp := hTp N (by omega) L hL d i j
  have ht := abs_sub_le
    (maskedSingleOldProfile N L d (1/W1Anchor j) (1/W1Target i) (W1Anchor j) true oldh)
    (trueSingleOldProfile N L d (1/W1Anchor j) (1/W1Target i) (W1Anchor j) true oldh)
    (singleOldIntegral (1/W1Anchor j) (1/W1Target i) (W1Anchor j) oldh)
  have heq : maskedW1OldProfile N L d i j oldH oldh-W1OldIntegral i j oldH oldh =
      (maskedSingleOldProfile N L d (1/W1Anchor j) (1/W1Target i) (W1Anchor j) true oldh-
        singleOldIntegral (1/W1Anchor j) (1/W1Target i) (W1Anchor j) oldh)/2 := by
    unfold maskedW1OldProfile W1OldIntegral
    ring
  rw [heq,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
  linarith

/-- Exact identification with the original d*N childWindow, at the same
Q and inherited scalar rho. No equality of N and d*N carriers is used. -/
theorem literalW1ThetaOldProfile_eq {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hA : 4 ≤ (N:ℝ)^(L/10)) (hQ : Q = (d:ℝ)*(N:ℝ)^L)
    (i : Fin 7) (j : Fin 10) (oldH oldh : Fin 200 → ℤ) :
    literalW1ThetaOldProfile N Q d i j oldH oldh =
      thetaAtom N Q d * maskedW1OldProfile N L d i j oldH oldh := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  have hNR : (1:ℝ) < N := by exact_mod_cast hN
  obtain ⟨hlo,hhi,hs⟩ := W1_endpoints i j
  have hcut (s : ℝ) : P2EnhancedTwentyOneSameQWeighted.cutoff Q d s =
      (N:ℝ)^(L*(1/s)) := by
    rw [cutoff_eq_physical_power hd hQ]
    congr 1
    ring
  have hsum :
      (∑ p ∈ P2EnhancedActualBuchstabTransfer.childWindow N d Q (W1Target i) (W1Anchor j),
        thetaAtom N Q (d*p) * tableFunction true oldh
          (W1Anchor j * (1-Real.log (p:ℝ)/Real.log (Q/d)))) =
      thetaAtom N Q d * maskedSingleOldProfile N L d (1/W1Anchor j) (1/W1Target i)
        (W1Anchor j) true oldh := by
    rw [P2EnhancedActualBuchstabTransfer.childWindow,hcut,hcut]
    unfold maskedSingleOldProfile
    rw [Finset.mul_sum]
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
    rw [thetaAtom_single (by omega) hd hpm.1 hp2 hpN hR,hlog]
    simp only [singleTest,residualSingle,max_eq_right hden,
      P2OriginalOldProfilePrimeLimits.singleRho,P5OriginalFeedbackDomains.singletonProfile]
    ring
  unfold literalW1ThetaOldProfile maskedW1OldProfile
  rw [hsum]
  ring

/-- A single threshold precedes the positive labelled family and its
moving residuals. The true-alpha hypothesis supplies d≤N, and the same
Q remains in every child Theta atom. Zero total mass needs no division. -/
theorem all70_literal_sameQ_Theta_profile_passage {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (oldH oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ),
      (∀ a ∈ S,L a ∈ Icc Lmin Lmax) → (∀ a ∈ S,0 < d a) →
      (∀ a ∈ S,Q = (d a:ℝ)*(N:ℝ)^(L a)) → (∀ a ∈ S,0 ≤ sigma a) →
      (∀ a ∈ S,2 ≤ alpha (Real.log (d a:ℝ)/Real.log (N:ℝ)) (L a)) →
      ∀ i : Fin 7, ∀ j : Fin 10,
        |(∑ a ∈ S,sigma a*literalW1ThetaOldProfile N Q (d a) i j oldH oldh)-
          (∑ a ∈ S,sigma a*thetaAtom N Q (d a))*W1OldIntegral i j oldH oldh| ≤
          epsilon*(∑ a ∈ S,sigma a*thetaAtom N Q (d a)) := by
  obtain ⟨Tp,hTp⟩ := all70_masked_old_profile_passage hmin hmax he oldH oldh
  obtain ⟨Te,hTe⟩ := compact_multiplier_error (k:=1) hmin hmax
    (by norm_num : (0:ℝ) ≤ 0) he
  refine ⟨max 4 (max Tp Te),?_⟩
  intro N hN Q ι S L d sigma hL hd hQ hsigma halpha i j
  have hN4 : 4 ≤ N := by omega
  have hN1 : 1 < N := by omega
  have hTpN : Tp ≤ N := by omega
  have hTeN : Te ≤ N := by omega
  have hLpos (a) (ha : a ∈ S) : 0 < L a := hmin.trans_le (hL a ha).1
  have hdN (a) (ha : a ∈ S) : d a ≤ N :=
    prefix_le_target_of_true_alpha hN1 (hd a ha) (hLpos a ha) (halpha a ha)
  have hw (a) (ha : a ∈ S) : 0 ≤ sigma a*thetaAtom N Q (d a) :=
    mul_nonneg (hsigma a ha) (thetaAtom_nonneg hN4 (hd a ha)
      (sameQ_residual_gt_one hN1 (hd a ha) (hLpos a ha) (hQ a ha)))
  have hp := finite_nonnegative_absolute_lift S (fun a => sigma a*thetaAtom N Q (d a))
    (fun a => maskedW1OldProfile N (L a) (d a) i j oldH oldh)
    (fun _ => W1OldIntegral i j oldH oldh) hw
    (fun a ha => (hTp N hTpN (L a) (hL a ha) (d a) (hd a ha) (hdN a ha) i j).le)
  have heq : (∑ a ∈ S,sigma a*literalW1ThetaOldProfile N Q (d a) i j oldH oldh) =
      ∑ a ∈ S,(sigma a*thetaAtom N Q (d a))*
        maskedW1OldProfile N (L a) (d a) i j oldH oldh := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [literalW1ThetaOldProfile_eq hN1 (hd a ha) (hLpos a ha)
      (hTe N hTeN (L a) (hL a ha)).1 (hQ a ha)]
    ring
  rw [heq,Finset.sum_mul]
  exact hp

end
end ImbalancedChen.P2OriginalLiteralW1OldProfile
