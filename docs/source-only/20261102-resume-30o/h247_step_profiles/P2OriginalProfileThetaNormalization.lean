import ImbalancedChen.P2OriginalBankOldProfilePassage

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact profile-weighted child Theta atoms at one Q, followed by an
absolute positive marked-family conclusion. True alpha, full/selected
squares and physical ceilings remain the explicit geometric conditions;
this file does not supply the separate old count licences.
-/
namespace ImbalancedChen.P2OriginalProfileThetaNormalization

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalOldProfilePrimeLimits
open P2OriginalPhysicalOldProfileMass P2OriginalBankOldProfilePassage
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def singleThetaOldProfile (N : ℕ) (Q L : ℝ) (d : ℕ) (lo hi s0 : ℝ)
    (lower : Bool) (nums : Fin 200 → ℤ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5),
    if normalizedLog N L p ∈ singleHalf lo hi then
      thetaAtom N Q (d*p 0) * tableFunction lower nums (singleRho s0 (normalizedLog N L p)) else 0

def pairThetaOldProfile (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters)
    (k : Fin 4) (nums : Fin 200 → ℤ) : ℝ :=
  ∑ q ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
    if normalizedLog N L q ∈ pairHalf p k then
      thetaAtom N Q (d*q 0*q 1) * tableFunction false nums (pairProfile p k (normalizedLog N L q)) else 0

theorem singleThetaOldProfile_eq {N d : ℕ} {Q L lo hi s0 : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L) (hhi : hi ≤ 1/2)
    (hA : 4 ≤ (N:ℝ)^(L/10)) (hQ : Q = (d:ℝ)*(N:ℝ)^L)
    (lower : Bool) (nums : Fin 200 → ℤ) :
    singleThetaOldProfile N Q L d lo hi s0 lower nums =
      thetaAtom N Q d * trueSingleOldProfile N L d lo hi s0 lower nums := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  unfold singleThetaOldProfile trueSingleOldProfile trueSingleTest
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 := mem_actualPrimeBoxTuples_iff.mp hp 0
  have hp2 : 2 < p 0 := by
    have hh := hA.trans hp0.2.2.1
    exact_mod_cast (show (2:ℝ) < p 0 by linarith)
  by_cases hx : normalizedLog N L p ∈ singleHalf lo hi
  · rw [if_pos hx,indicator_of_mem hx,
      thetaAtom_single (by omega) hd hp0.1 hp2 (hp0.1.coprime_iff_not_dvd.mpr hp0.2.1) hR]
    have hlog : Real.log (p 0:ℝ)/Real.log (Q/d) = normalizedLog N L p 0 := by
      rw [hQ]
      exact physical_log_ratio hN hd hL p 0
    rw [hlog]
    have hden : (1/10:ℝ) ≤ 1-normalizedLog N L p 0 := by linarith [hx.2]
    simp only [singleTest,residualSingle,max_eq_right hden]
    ring
  · simp only [if_neg hx,indicator_of_notMem hx,mul_zero]

theorem pairThetaOldProfile_eq {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hA : 4 ≤ (N:ℝ)^(L/10)) (hQ : Q = (d:ℝ)*(N:ℝ)^L)
    {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4) (nums : Fin 200 → ℤ) :
    pairThetaOldProfile N Q L d p k nums =
      thetaAtom N Q d * truePairOldProfile N L d p k nums := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  unfold pairThetaOldProfile truePairOldProfile truePairTest
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
  by_cases hx : normalizedLog N L q ∈ pairHalf p k
  · rw [if_pos hx,indicator_of_mem hx,
      thetaAtom_pair (by omega) hd hq0.1 hq1.1 hq02 hq12
        (hq0.1.coprime_iff_not_dvd.mpr hq0.2.1) (hq1.1.coprime_iff_not_dvd.mpr hq1.2.1) hR]
    have hlog (i : Fin 2) : Real.log (q i:ℝ)/Real.log (Q/d) = normalizedLog N L q i := by
      rw [hQ]
      exact physical_log_ratio hN hd hL q i
    rw [hlog 0,hlog 1]
    have hden := (pairHalf_geometry hp k hx).2.1
    simp only [pairTest,residualPair,max_eq_right
      (show (1/10:ℝ) ≤ 1-normalizedLog N L q 0-normalizedLog N L q 1 by linarith)]
    ring
  · simp only [if_neg hx,indicator_of_notMem hx,mul_zero]

def W1ThetaOldProfile (N : ℕ) (Q L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10)
    (oldH oldh : Fin 200 → ℤ) : ℝ :=
  thetaAtom N Q d * tableFunction false oldH (W1Anchor j)+
    singleThetaOldProfile N Q L d (1/W1Anchor j) (1/W1Target i) (W1Anchor j) true oldh/2

def W2ThetaOldProfile (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters)
    (oldH oldh : Fin 200 → ℤ) : ℝ :=
  (4*thetaAtom N Q d*tableFunction false oldH p.s0+
    thetaAtom N Q d*tableFunction false oldH p.phi1+
    (∑ k : Fin 3,singleThetaOldProfile N Q L d (a0 p) (singletonTop p k) p.s0 true oldh)+
    (∑ k : Fin 4,pairThetaOldProfile N Q L d p k oldH))/5

theorem W1ThetaOldProfile_eq {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (i : Fin 7) (j : Fin 10) (oldH oldh : Fin 200 → ℤ) :
    W1ThetaOldProfile N Q L d i j oldH oldh =
      thetaAtom N Q d * W1OldProfile N L d i j oldH oldh := by
  unfold W1ThetaOldProfile W1OldProfile
  rw [singleThetaOldProfile_eq hN hd hL (W1_endpoints i j).2.1 hA hQ]
  ring

theorem W2ThetaOldProfile_eq {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) {p : W2Parameters} (hp : W2Geometry p)
    (oldH oldh : Fin 200 → ℤ) :
    W2ThetaOldProfile N Q L d p oldH oldh =
      thetaAtom N Q d * W2OldProfile N L d p oldH oldh := by
  unfold W2ThetaOldProfile W2OldProfile
  simp_rw [singleThetaOldProfile_eq hN hd hL (W2_singleton_top hp _) hA hQ,
    pairThetaOldProfile_eq hN hd hL hA hQ hp]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  ring

/-- One Q for all marks, and the original positive normalizer. The
same target threshold precedes every choice of labels and weights. -/
theorem all106_sameQ_Theta_profile_passage {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (oldH oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ),
      (∀ a ∈ S,L a ∈ Icc Lmin Lmax) → (∀ a ∈ S,0 < d a) →
      (∀ a ∈ S,Q = (d a:ℝ)*(N:ℝ)^(L a)) → (∀ a ∈ S,0 ≤ sigma a) →
      (∀ i : Fin 7, ∀ j : Fin 10,
        |(∑ a ∈ S,sigma a*W1ThetaOldProfile N Q (L a) (d a) i j oldH oldh)-
          (∑ a ∈ S,sigma a*thetaAtom N Q (d a))*W1OldIntegral i j oldH oldh| ≤
          epsilon*(∑ a ∈ S,sigma a*thetaAtom N Q (d a))) ∧
      (∀ j : Fin 36,
        |(∑ a ∈ S,sigma a*W2ThetaOldProfile N Q (L a) (d a) (originalW2At j) oldH oldh)-
          (∑ a ∈ S,sigma a*thetaAtom N Q (d a))*W2OldIntegral (originalW2At j) oldH oldh| ≤
          epsilon*(∑ a ∈ S,sigma a*thetaAtom N Q (d a))) := by
  obtain ⟨Tp,hTp⟩ := all106_marked_absolute_passage hmin hmax he oldH oldh
  obtain ⟨Te,hTe⟩ := P2OriginalCompactThetaMass.compact_multiplier_error (k:=1)
    hmin hmax (by norm_num : (0:ℝ) ≤ 0) he
  refine ⟨max 4 (max Tp Te),?_⟩
  intro N hN Q ι S L d sigma hL hd hQ hsigma
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 < N := by omega
  have hTpN : Tp ≤ N := (le_max_left Tp Te).trans ((le_max_right _ _).trans hN)
  have hTeN : Te ≤ N := (le_max_right Tp Te).trans ((le_max_right _ _).trans hN)
  have hweight (a) (ha : a ∈ S) : 0 ≤ sigma a*thetaAtom N Q (d a) :=
    mul_nonneg (hsigma a ha) (thetaAtom_nonneg hN4 (hd a ha)
      (sameQ_residual_gt_one hN1 (hd a ha) (hmin.trans_le (hL a ha).1) (hQ a ha)))
  have hp := hTp N hTpN S L d (fun a => sigma a*thetaAtom N Q (d a)) hL hweight
  have hA (a) (ha : a ∈ S) : 4 ≤ (N:ℝ)^(L a/10) := (hTe N hTeN (L a) (hL a ha)).1
  constructor
  · intro i j
    have hh := hp.1 i j
    have heq : (∑ a ∈ S,sigma a*W1ThetaOldProfile N Q (L a) (d a) i j oldH oldh) =
        ∑ a ∈ S,(sigma a*thetaAtom N Q (d a))*W1OldProfile N (L a) (d a) i j oldH oldh := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [W1ThetaOldProfile_eq hN1 (hd a ha) (hmin.trans_le (hL a ha).1) (hA a ha) (hQ a ha)]
      ring
    rw [heq,Finset.sum_mul]
    exact hh
  · intro j
    have hh := hp.2 j
    have heq : (∑ a ∈ S,sigma a*W2ThetaOldProfile N Q (L a) (d a) (originalW2At j) oldH oldh) =
        ∑ a ∈ S,(sigma a*thetaAtom N Q (d a))*W2OldProfile N (L a) (d a) (originalW2At j) oldH oldh := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [W2ThetaOldProfile_eq hN1 (hd a ha) (hmin.trans_le (hL a ha).1) (hA a ha) (hQ a ha)
        (originalRepairedW2Bank_geometry _ (originalW2At_mem j))]
      ring
    rw [heq,Finset.sum_mul]
    exact hh

end
end ImbalancedChen.P2OriginalProfileThetaNormalization
