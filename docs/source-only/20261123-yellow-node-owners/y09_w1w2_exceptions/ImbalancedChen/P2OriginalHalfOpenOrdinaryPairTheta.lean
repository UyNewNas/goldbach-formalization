import ImbalancedChen.P2OriginalW2CountTupleReindex
import ImbalancedChen.P2OriginalProfileThetaNormalization

/-! Ordinary child mass on the literal four half-open source windows.
The total level is real. Endpoint primes, including primes already in
the prefix, stay in the discrete mass until after summation. -/
namespace ImbalancedChen.P2OriginalHalfOpenOrdinaryPairTheta
noncomputable section
open Finset Set MeasureTheory Filter
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalCompactThetaMass P2OriginalHalfOpenProfileCarrier
open P2OriginalAffineProfilePassage P2OriginalClosedCellProfileAtoms
open P2OriginalOldProfilePrimeLimits P2OriginalPhysicalOldProfileMass
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2OriginalW2CountTupleReindex
open scoped Classical BigOperators Topology

def goodIntegral (a : W2Parameters) (j : Fin 4) : ℝ :=
  ∫ x in W2PairDomain a j, 1/(x 0*x 1*(1-x 0-x 1))

theorem actual_half_child_theta {N d : ℕ} {Q L : ℝ}
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (hQ : Q=(d:ℝ)*(N:ℝ)^L)
    (hA : 4≤(N:ℝ)^(L/10)) {a : W2Parameters} (ha : W2Geometry a) (j : Fin 4) :
    windowOccurrence N Q L d a j (fun p q => thetaAtom N Q (d*p*q)) =
      thetaAtom N Q d * truePairTest N L d (pairHalf a j) residualPair := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  rw [all_four_window_occurrences_reindex hN hd hL hQ ha]
  unfold truePairTest
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  have h0 := mem_actualPrimeBoxTuples_iff.mp hp 0
  have h1 := mem_actualPrimeBoxTuples_iff.mp hp 1
  have hlarge (i : Fin 2) : 2 < p i := by
    have h := hA.trans (mem_actualPrimeBoxTuples_iff.mp hp i).2.2.1
    exact_mod_cast (show (2:ℝ) < p i by linarith)
  by_cases hx : normalizedLog N L p ∈ pairHalf a j
  · rw [if_pos hx, indicator_of_mem hx, thetaAtom_pair (by omega) hd h0.1 h1.1
      (hlarge 0) (hlarge 1) (h0.1.coprime_iff_not_dvd.mpr h0.2.1)
      (h1.1.coprime_iff_not_dvd.mpr h1.2.1) hR]
    have hlog (i : Fin 2) :
        Real.log (p i : ℝ)/Real.log (Q/d) = normalizedLog N L p i := by
      rw [hQ]
      exact physical_log_ratio hN hd hL p i
    rw [hlog 0,hlog 1]
    have hden := (pairHalf_geometry ha j hx).2.1
    simp only [residualPair, max_eq_right
      (show (1/10:ℝ) ≤ 1-normalizedLog N L p 0-normalizedLog N L p 1 by linarith)]
    ring
  · simp only [if_neg hx, indicator_of_notMem hx, mul_zero]

theorem half_ordinary_limit {lo hi ε : ℝ} (hlo : 0<lo) (hhi : lo≤hi) (he : 0<ε)
    {a : W2Parameters} (ha : W2Geometry a) (j : Fin 4) :
    ∃ T : ℕ, ∀ N : ℕ, T≤N → ∀ L∈Icc lo hi, ∀ d : ℕ,
      |truePairTest N L d (pairHalf a j) residualPair-goodIntegral a j| < ε := by
  have hbound (x : Coord 2) : |residualPair x| ≤ 10 := by
    rw [abs_of_nonneg (residualPair_bounds x).1]
    exact (residualPair_bounds x).2
  obtain ⟨T1,h1⟩ := compact_uniform_sandwich hlo hhi (by norm_num : (0:ℝ)≤10)
    (half_pos he) (pairForms j) (pairBounds a j) (pairForms_ne j)
    (enumForms (controlForms 2)) (enumBounds controlBounds)
    (fun i => control_nonzero ((Fintype.equivFin _).symm i))
    (by rw [← finiteGates_enum]; exact control_in_cube 2)
    (pairHalf_sandwich a j) (fun x hx => by
      rw [← finiteGates_enum]
      exact control_contains_box (fun i =>
        ⟨(pairHalf_geometry ha j hx).1.1 i,(pairHalf_geometry ha j hx).1.2 i⟩))
    residualPair residualPair_continuous hbound
  obtain ⟨T2,h2⟩ := compact_multiplier_error (k:=2) hlo hhi (by norm_num : (0:ℝ)≤6*10)
    (half_pos he)
  have hset := sandwich_ae (pairForms j) (pairBounds a j) (pairForms_ne j) (pairHalf_sandwich a j)
  rw [← pair_as_affine] at hset
  have hI : (∫ x in pairHalf a j, residualPair x * ∏ i, 1/x i)=goodIntegral a j := by
    rw [setIntegral_congr_set hset,goodIntegral]
    exact setIntegral_congr_fun (measurableSet_W2PairDomain _ _) (fun x hx => pair_kernel ha j hx)
  refine ⟨max T1 T2,?_⟩
  intro N hN L hL d
  obtain ⟨hA,hE⟩ := h2 N ((le_max_right _ _).trans hN) L hL
  have hP := h1 N ((le_max_left _ _).trans hN) L hL
  rw [hI] at hP
  have hD := truePairTest_error d (pairHalf a j) residualPair (by norm_num : (0:ℝ)≤10) hbound hA
  exact (abs_sub_le _ (scaledPrimeSum N L (pairHalf a j) residualPair) _).trans_lt
    (by linarith only [hD,hE,hP])

/-- Threshold precedes the choice of all 36 actions, all four lanes,
the real common Q, positive prefix multiplicities, and moving levels. -/
theorem all_ordinary_good_windows {lo hi ε : ℝ} (hlo : 0<lo) (hhi : lo≤hi) (he : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → ∀ (Q : ℝ) (D : Finset ℕ) (σ L : ℕ → ℝ),
      (∀ d∈D, 0<d) → (∀ d∈D, 0≤σ d) → (∀ d∈D, L d∈Icc lo hi) →
      (∀ d∈D, Q=(d:ℝ)*(N:ℝ)^(L d)) → ∀ (a : Fin 36) (j : Fin 4),
      |(∑ d∈D, σ d * windowOccurrence N Q (L d) d (originalW2At a) j
          (fun p q => thetaAtom N Q (d*p*q))) -
        goodIntegral (originalW2At a) j * P2EnhancedTwentyOneSameQWeighted.Theta N Q D σ| ≤
        ε * P2EnhancedTwentyOneSameQWeighted.Theta N Q D σ := by
  have hall (a : Fin 36) (j : Fin 4) : ∀ᶠ N : ℕ in atTop, ∀ L∈Icc lo hi, ∀ d : ℕ,
      |truePairTest N L d (pairHalf (originalW2At a) j) residualPair-
        goodIntegral (originalW2At a) j| < ε := by
    exact eventually_atTop.mpr (half_ordinary_limit hlo hhi he
      (originalRepairedW2Bank_geometry _ (originalW2At_mem a)) j)
  obtain ⟨T1,h1⟩ := eventually_atTop.mp (eventually_all.mpr
    (fun a => eventually_all.mpr (hall a)))
  obtain ⟨T2,h2⟩ := compact_multiplier_error (k:=2) hlo hhi (by norm_num : (0:ℝ)≤0)
    (by norm_num : (0:ℝ)<1)
  refine ⟨max 4 (max T1 T2),le_max_left _ _,?_⟩
  intro N hN Q D σ L hd hσ hL hQ a j
  have h4 := (le_max_left 4 (max T1 T2)).trans hN
  have hgeo := originalRepairedW2Bank_geometry _ (originalW2At_mem a)
  have hR (d : ℕ) (hm : d∈D) := sameQ_residual_gt_one (by omega : 1<N)
    (hd d hm) (hlo.trans_le (hL d hm).1) (hQ d hm)
  have hh (d : ℕ) (hm : d∈D) := actual_half_child_theta (by omega : 1<N) (hd d hm)
    (hlo.trans_le (hL d hm).1) (hQ d hm) (h2 N (by omega) (L d) (hL d hm)).1 hgeo j
  have hsum := finite_positive_theta_error h4 Q D σ
    (fun d => truePairTest N (L d) d (pairHalf (originalW2At a) j) residualPair)
    (fun _ => goodIntegral (originalW2At a) j) hd hσ hR (fun d hm =>
      (h1 N (by omega) a j (L d) (hL d hm) d).le)
  have hleft : (∑ d∈D, σ d * windowOccurrence N Q (L d) d (originalW2At a) j
      (fun p q => thetaAtom N Q (d*p*q))) = ∑ d∈D, σ d * thetaAtom N Q d *
      truePairTest N (L d) d (pairHalf (originalW2At a) j) residualPair := by
    apply sum_congr rfl
    intro d hm
    rw [hh d hm,mul_assoc]
  have hright : goodIntegral (originalW2At a) j * P2EnhancedTwentyOneSameQWeighted.Theta N Q D σ =
      ∑ d∈D, σ d * thetaAtom N Q d * goodIntegral (originalW2At a) j := by
    rw [Theta_eq_sum_atoms,mul_comm (goodIntegral _ _),sum_mul]
  rw [hleft,hright]
  exact hsum

end
end ImbalancedChen.P2OriginalHalfOpenOrdinaryPairTheta
