import ImbalancedChen.Part5OriginalH430SeedSingletonFeedbackMass

/-! Seven literal same-Q child payments. Zero and below-two branches keep
their original profiles, and both direct pair cutoffs remain distinct. -/
namespace ImbalancedChen.Part5OriginalH430SeedSevenPhysicalWindows
noncomputable section
open Set Finset Real
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalPhysicalOldProfileMass
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2EnhancedSeedSingletonPrimitive (parameters parameters_geometry S uStar profile cap
  seedUpper seedLower literal_bounds profile_gt_two profile_short_support_iff)
open Part5OriginalH430SeedSingletonFeedbackMass (singleMass clippedLog clipped_eq)
open Part5OriginalH430SeedPairFeedbackMass (pairMass halfSupport)
open scoped Classical BigOperators

def physicalSingle (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 3) : ℝ :=
  ∑ x∈actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5),
    if normalizedLog N L x∈singleHalf P2EnhancedSeedSingletonPrimitive.a0 (cap j) then
      thetaAtom N Q (d*x 0)*seedLower 1 (profile (normalizedLog N L x 0)) else 0

def physicalPair (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 4) : ℝ :=
  ∑ x∈actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
    if normalizedLog N L x∈pairHalf parameters j then
      thetaAtom N Q (d*x 0*x 1)*seedUpper 1 (pairProfile parameters j (normalizedLog N L x)) else 0

private theorem inactive {u : ℝ} (h : u≤uStar) : seedLower 1 (profile u)=0 := by
  rcases lt_or_eq_of_le h with hh | rfl
  · apply indicator_of_notMem
    exact fun hw => hh.not_ge ((profile_short_support_iff u).mp hw.2)
  · have he : profile uStar=1+S := by
      norm_num [profile,uStar,P2EnhancedSeedSingletonPrimitive.s0,S]
    rw [he,seedLower,indicator_of_mem (⟨by norm_num [S],le_rfl⟩ : (1+S:ℝ)∈Icc 2 (1+S))]
    simp [show S ≠ 0 by norm_num [S]]

theorem physical_single_eq {N d : ℕ} {Q L : ℝ} (hN : 1<N) (hd : 0<d)
    (hL : 0<L) (hA : 4≤(N:ℝ)^(L/10)) (hQ : Q=(d:ℝ)*(N:ℝ)^L) (j : Fin 3) :
    physicalSingle N Q L d j=thetaAtom N Q d*singleMass N L d j := by
  let lo := P2EnhancedSeedSingletonPrimitive.a0
  have hR := sameQ_residual_gt_one hN hd hL hQ
  unfold physicalSingle singleMass trueSingleTest
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  let u := normalizedLog N L x 0
  have hx0 := mem_actualPrimeBoxTuples_iff.mp hx 0
  have hp2 : 2<x 0 := by
    have hh := hA.trans hx0.2.2.1
    exact_mod_cast (show (2:ℝ)<x 0 by linarith)
  by_cases hm : normalizedLog N L x∈singleDomain uStar (cap j)
  · have hor : normalizedLog N L x∈singleHalf lo (cap j) :=
      ⟨(literal_bounds j).2.1.le.trans hm.1.le,hm.2⟩
    have hv := hm.2.le.trans (literal_bounds j).2.2.2.1
    have hs : profile u∈Icc (2:ℝ) (1+S) := ⟨(profile_gt_two hv).le,
      (profile_short_support_iff u).mpr hm.1.le⟩
    have hlog : log (x 0:ℝ)/log (Q/d)=u := by rw [hQ]; exact physical_log_ratio hN hd hL x 0
    rw [if_pos hor,indicator_of_mem hm,seedLower,indicator_of_mem hs,one_mul,
      thetaAtom_single (by omega) hd hx0.1 hp2 (hx0.1.coprime_iff_not_dvd.mpr hx0.2.1) hR,hlog]
    unfold Part5OriginalH430SeedSingletonFeedbackMass.singleTest residualSingle
    rw [clipped_eq hm.1.le hv,max_eq_right (show (1/10:ℝ)≤1-normalizedLog N L x 0 by linarith [hv])]
    ring
  · rw [indicator_of_notMem hm,mul_zero]
    by_cases hor : normalizedLog N L x∈singleHalf lo (cap j)
    · have hle : u≤uStar := le_of_not_gt (fun hu => hm ⟨hu,hor.2⟩)
      rw [if_pos hor,inactive hle,mul_zero]
    · rw [if_neg hor]

private theorem pair_above_one {j : Fin 4} {x : Coord 2} (hx : x∈pairHalf parameters j) :
    1<pairProfile parameters j x := by
  have hu : a0 parameters≤x 0 := by fin_cases j <;> exact hx.1
  have hh := (pairHalf_geometry parameters_geometry j hx).2.2.2
  have hu' : (50/227:ℝ)≤x 0 := by
    convert hu using 1 <;> norm_num [a0,parameters]
  unfold pairProfile
  split_ifs
  · change 1<(227/50:ℝ)*(1-x 0-x 1)
    linarith only [hh,hu']
  · apply (lt_div_iff₀ (show 0<x 0 by linarith)).mpr
    linarith only [hh]

theorem physical_pair_eq {N d : ℕ} {Q L : ℝ} (hN : 1<N) (hd : 0<d)
    (hL : 0<L) (hA : 4≤(N:ℝ)^(L/10)) (hQ : Q=(d:ℝ)*(N:ℝ)^L) (j : Fin 4) :
    physicalPair N Q L d j=thetaAtom N Q d*pairMass N L d j := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  unfold physicalPair pairMass truePairTest
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  have hdata (i : Fin 2) := mem_actualPrimeBoxTuples_iff.mp hx i
  have hp2 (i : Fin 2) : 2<x i := by
    have hh := hA.trans (hdata i).2.2.1
    exact_mod_cast (show (2:ℝ)<x i by linarith)
  by_cases hg : normalizedLog N L x∈pairHalf parameters j
  · rw [if_pos hg]
    by_cases hs : normalizedLog N L x∈halfSupport j
    · have hshort : pairProfile parameters j (normalizedLog N L x)∈Icc (1:ℝ) S :=
        ⟨(pair_above_one hg).le,hs.2⟩
      rw [indicator_of_mem hs,seedUpper,indicator_of_mem hshort,mul_one,
        thetaAtom_pair (by omega) hd (hdata 0).1 (hdata 1).1 (hp2 0) (hp2 1)
          ((hdata 0).1.coprime_iff_not_dvd.mpr (hdata 0).2.1)
          ((hdata 1).1.coprime_iff_not_dvd.mpr (hdata 1).2.1) hR]
      have hlog (i : Fin 2) : log (x i:ℝ)/log (Q/d)=normalizedLog N L x i := by
        rw [hQ]; exact physical_log_ratio hN hd hL x i
      rw [hlog 0,hlog 1,residualPair,max_eq_right (by linarith [(pairHalf_geometry parameters_geometry j hg).2.1])]
      ring
    · have hshort : pairProfile parameters j (normalizedLog N L x)∉Icc (1:ℝ) S :=
        fun h => hs ⟨hg,h.2⟩
      simp only [seedUpper,indicator_of_notMem hshort,indicator_of_notMem hs,mul_zero]
  · have hs : normalizedLog N L x∉halfSupport j := fun h => hg h.1
    simp only [if_neg hg,indicator_of_notMem hs,mul_zero]

def physicalFeedback (N : ℕ) (Q L : ℝ) (d : ℕ) : ℝ :=
  ((∑ j : Fin 3,physicalSingle N Q L d j)+(∑ j : Fin 4,physicalPair N Q L d j))/5

end
end ImbalancedChen.Part5OriginalH430SeedSevenPhysicalWindows
