import ImbalancedChen.P2OriginalPhysicalOldProfileMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original action occurrences, old-generation arrays, and positive marked
lifting. This supplies a carrier/profile passage, not an analytic upper
or lower count licence and not a numerical H247 recurrence assertion.
-/
namespace ImbalancedChen.P2OriginalBankOldProfilePassage

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalOldProfilePrimeLimits
open P2OriginalPhysicalOldProfileMass P2OriginalCompactThetaMass
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def singleOldIntegral (lo hi s0 : ℝ) (nums : Fin 200 → ℤ) : ℝ :=
  ∫ u in Ioo lo hi,tableFunction true nums (s0*(1-u))/(u*(1-u))
def pairOldIntegral (p : W2Parameters) (k : Fin 4) (nums : Fin 200 → ℤ) : ℝ :=
  ∫ x in W2PairDomain p k,tableFunction false nums (pairProfile p k x)/
    (x 0*x 1*(1-x 0-x 1))

theorem W1_endpoints (i : Fin 7) (j : Fin 10) :
    (1/5:ℝ) ≤ 1/W1Anchor j ∧ 1/W1Target i ≤ (1/2:ℝ) ∧ 0 < W1Anchor j := by
  have hj : (j.val:ℝ) ≤ 9 := by exact_mod_cast (show j.val ≤ 9 by omega)
  have ha : 0 < W1Anchor j := by unfold W1Anchor; positivity
  refine ⟨one_div_le_one_div_of_le ha ?_,?_,ha⟩
  · unfold W1Anchor; linarith
  · apply one_div_le_one_div_of_le (by norm_num)
    unfold W1Target
    linarith [show (0:ℝ) ≤ i.val from Nat.cast_nonneg _]

theorem W2_singleton_top {p : W2Parameters} (hp : W2Geometry p) (k : Fin 3) :
    singletonTop p k ≤ (1/2:ℝ) := by
  rcases hp with ⟨h0,h01,h12,h23,h3,hb,hg6,hg7,hg8⟩
  fin_cases k <;> simp only [singletonTop,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two] <;> linarith

/-- A single common threshold is chosen before the action, moving
residual, complete prefix or positive marked family is selected. -/
theorem all70_true_old_h_profile {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      ∀ i : Fin 7, ∀ j : Fin 10,
      |trueSingleOldProfile N L d (1/W1Anchor j) (1/W1Target i) (W1Anchor j) true oldh-
        singleOldIntegral (1/W1Anchor j) (1/W1Target i) (W1Anchor j) oldh| < epsilon := by
  have hfixed (ij : Fin 7 × Fin 10) : ∀ᶠ N : ℕ in atTop, ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      |trueSingleOldProfile N L d (1/W1Anchor ij.2) (1/W1Target ij.1)
          (W1Anchor ij.2) true oldh-
        singleOldIntegral (1/W1Anchor ij.2) (1/W1Target ij.1) (W1Anchor ij.2) oldh| < epsilon := by
    obtain ⟨hlo,hhi,hs⟩ := W1_endpoints ij.1 ij.2
    obtain ⟨T,hT⟩ := compact_uniform_true_single_old_profile hmin hmax he hlo hhi hs true oldh
    filter_upwards [eventually_ge_atTop T] with N hN L hL d
    have hh := hT N hN L hL d
    rw [single_profile_original_integral hlo hhi] at hh
    exact hh
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_all.mpr hfixed)
  exact ⟨T,fun N hN L hL d i j => hT N hN (i,j) L hL d⟩

theorem all36_three_true_old_h_profiles {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      ∀ j : Fin 36, ∀ k : Fin 3,
      |trueSingleOldProfile N L d (a0 (originalW2At j)) (singletonTop (originalW2At j) k)
          (originalW2At j).s0 true oldh-
        singleOldIntegral (a0 (originalW2At j)) (singletonTop (originalW2At j) k)
          (originalW2At j).s0 oldh| < epsilon := by
  have hfixed (jk : Fin 36 × Fin 3) : ∀ᶠ N : ℕ in atTop, ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      |trueSingleOldProfile N L d (a0 (originalW2At jk.1))
          (singletonTop (originalW2At jk.1) jk.2) (originalW2At jk.1).s0 true oldh-
        singleOldIntegral (a0 (originalW2At jk.1)) (singletonTop (originalW2At jk.1) jk.2)
          (originalW2At jk.1).s0 oldh| < epsilon := by
    have hp := originalRepairedW2Bank_geometry _ (originalW2At_mem jk.1)
    obtain ⟨T,hT⟩ := compact_uniform_true_single_old_profile hmin hmax he hp.1
      (W2_singleton_top hp jk.2) (W2_anchor_positive hp) true oldh
    filter_upwards [eventually_ge_atTop T] with N hN L hL d
    have hh := hT N hN L hL d
    rw [single_profile_original_integral hp.1 (W2_singleton_top hp jk.2)] at hh
    exact hh
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_all.mpr hfixed)
  exact ⟨T,fun N hN L hL d j k => hT N hN (j,k) L hL d⟩

theorem all36_four_true_old_H_profiles {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (oldH : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      ∀ j : Fin 36, ∀ k : Fin 4,
      |truePairOldProfile N L d (originalW2At j) k oldH-
        pairOldIntegral (originalW2At j) k oldH| < epsilon := by
  have hfixed (jk : Fin 36 × Fin 4) : ∀ᶠ N : ℕ in atTop, ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      |truePairOldProfile N L d (originalW2At jk.1) jk.2 oldH-
        pairOldIntegral (originalW2At jk.1) jk.2 oldH| < epsilon := by
    have hp := originalRepairedW2Bank_geometry _ (originalW2At_mem jk.1)
    obtain ⟨T,hT⟩ := compact_uniform_true_pair_old_profile hmin hmax he hp jk.2 oldH
    filter_upwards [eventually_ge_atTop T] with N hN L hL d
    have hh := hT N hN L hL d
    rw [pair_profile_original_integral hp jk.2] at hh
    exact hh
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_all.mpr hfixed)
  exact ⟨T,fun N hN L hL d j k => hT N hN (j,k) L hL d⟩

/-- These are occurrences, not a set-union of overlapping windows.
The point coefficients and divisors occur literally exactly once. -/
def W1OldProfile (N : ℕ) (L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10)
    (oldH oldh : Fin 200 → ℤ) : ℝ :=
  tableFunction false oldH (W1Anchor j) +
    trueSingleOldProfile N L d (1/W1Anchor j) (1/W1Target i) (W1Anchor j) true oldh / 2

def W1OldIntegral (i : Fin 7) (j : Fin 10) (oldH oldh : Fin 200 → ℤ) : ℝ :=
  tableFunction false oldH (W1Anchor j) +
    singleOldIntegral (1/W1Anchor j) (1/W1Target i) (W1Anchor j) oldh / 2

def W2OldProfile (N : ℕ) (L : ℝ) (d : ℕ) (p : W2Parameters)
    (oldH oldh : Fin 200 → ℤ) : ℝ :=
  (4*tableFunction false oldH p.s0+tableFunction false oldH p.phi1+
    (∑ k : Fin 3,trueSingleOldProfile N L d (a0 p) (singletonTop p k) p.s0 true oldh)+
    (∑ k : Fin 4,truePairOldProfile N L d p k oldH))/5

def W2OldIntegral (p : W2Parameters) (oldH oldh : Fin 200 → ℤ) : ℝ :=
  (4*tableFunction false oldH p.s0+tableFunction false oldH p.phi1+
    (∑ k : Fin 3,singleOldIntegral (a0 p) (singletonTop p k) p.s0 oldh)+
    (∑ k : Fin 4,pairOldIntegral p k oldH))/5

theorem W1_point_and_half (N : ℕ) (L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10)
    (oldH oldh : Fin 200 → ℤ) :
    W1OldProfile N L d i j oldH oldh-W1OldIntegral i j oldH oldh =
      (trueSingleOldProfile N L d (1/W1Anchor j) (1/W1Target i) (W1Anchor j) true oldh-
        singleOldIntegral (1/W1Anchor j) (1/W1Target i) (W1Anchor j) oldh)/2 := by
  unfold W1OldProfile W1OldIntegral
  ring

theorem W2_four_one_three_four (N : ℕ) (L : ℝ) (d : ℕ) (p : W2Parameters)
    (oldH oldh : Fin 200 → ℤ) :
    W2OldProfile N L d p oldH oldh-W2OldIntegral p oldH oldh =
      ((∑ k : Fin 3,(trueSingleOldProfile N L d (a0 p) (singletonTop p k) p.s0 true oldh-
        singleOldIntegral (a0 p) (singletonTop p k) p.s0 oldh))+
       (∑ k : Fin 4,(truePairOldProfile N L d p k oldH-pairOldIntegral p k oldH)))/5 := by
  unfold W2OldProfile W2OldIntegral
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  ring

theorem all106_old_profile_passage {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (oldH oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      (∀ i : Fin 7, ∀ j : Fin 10,
        |W1OldProfile N L d i j oldH oldh-W1OldIntegral i j oldH oldh| < epsilon) ∧
      (∀ j : Fin 36,
        |W2OldProfile N L d (originalW2At j) oldH oldh-
          W2OldIntegral (originalW2At j) oldH oldh| < epsilon) := by
  obtain ⟨T₁,h₁⟩ := all70_true_old_h_profile hmin hmax (by positivity : (0:ℝ) < epsilon/2) oldh
  obtain ⟨T₂,h₂⟩ := all36_three_true_old_h_profiles hmin hmax (by positivity : (0:ℝ) < epsilon/2) oldh
  obtain ⟨T₃,h₃⟩ := all36_four_true_old_H_profiles hmin hmax (by positivity : (0:ℝ) < epsilon/2) oldH
  refine ⟨max T₁ (max T₂ T₃),?_⟩
  intro N hN L hL d
  have hn1 : T₁ ≤ N := (le_max_left _ _).trans hN
  have hn2 : T₂ ≤ N := (le_max_left T₂ T₃).trans ((le_max_right _ _).trans hN)
  have hn3 : T₃ ≤ N := (le_max_right T₂ T₃).trans ((le_max_right _ _).trans hN)
  constructor
  · intro i j
    rw [W1_point_and_half,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact (div_lt_iff₀ (by norm_num : (0:ℝ) < 2)).mpr (by linarith [h₁ N hn1 L hL d i j])
  · intro j
    rw [W2_four_one_three_four,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 5)]
    have hsingle : |∑ k : Fin 3,(trueSingleOldProfile N L d (a0 (originalW2At j))
        (singletonTop (originalW2At j) k) (originalW2At j).s0 true oldh-
          singleOldIntegral (a0 (originalW2At j)) (singletonTop (originalW2At j) k)
            (originalW2At j).s0 oldh)| ≤ 3*(epsilon/2) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact (Finset.sum_le_sum (fun k _ => (h₂ N hn2 L hL d j k).le)).trans_eq (by simp)
    have hpair : |∑ k : Fin 4,(truePairOldProfile N L d (originalW2At j) k oldH-
        pairOldIntegral (originalW2At j) k oldH)| ≤ 4*(epsilon/2) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact (Finset.sum_le_sum (fun k _ => (h₃ N hn3 L hL d j k).le)).trans_eq (by simp)
    apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 5)).mpr
    have ht := abs_add (∑ k : Fin 3,(trueSingleOldProfile N L d (a0 (originalW2At j))
      (singletonTop (originalW2At j) k) (originalW2At j).s0 true oldh-
        singleOldIntegral (a0 (originalW2At j)) (singletonTop (originalW2At j) k)
          (originalW2At j).s0 oldh))
      (∑ k : Fin 4,(truePairOldProfile N L d (originalW2At j) k oldH-
        pairOldIntegral (originalW2At j) k oldH))
    linarith

/-- Positive arbitrary labelled families may vary AFTER the uniform
threshold. Zero total weight is paid absolutely and stays zero. -/
theorem all106_marked_absolute_passage {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (oldH oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ {ι : Type*} (S : Finset ι)
      (L : ι → ℝ) (d : ι → ℕ) (w : ι → ℝ),
      (∀ a ∈ S,L a ∈ Icc Lmin Lmax) → (∀ a ∈ S,0 ≤ w a) →
      (∀ i : Fin 7, ∀ j : Fin 10,
        |(∑ a ∈ S,w a*W1OldProfile N (L a) (d a) i j oldH oldh)-
          (∑ a ∈ S,w a*W1OldIntegral i j oldH oldh)| ≤ epsilon*(∑ a ∈ S,w a)) ∧
      (∀ j : Fin 36,
        |(∑ a ∈ S,w a*W2OldProfile N (L a) (d a) (originalW2At j) oldH oldh)-
          (∑ a ∈ S,w a*W2OldIntegral (originalW2At j) oldH oldh)| ≤ epsilon*(∑ a ∈ S,w a)) := by
  obtain ⟨T,hT⟩ := all106_old_profile_passage hmin hmax he oldH oldh
  refine ⟨T,?_⟩
  intro N hN ι S L d w hL hw
  constructor
  · intro i j
    exact finite_nonnegative_absolute_lift S w _ _ hw
      (fun a ha => ((hT N hN (L a) (hL a ha) (d a)).1 i j).le)
  · intro j
    exact finite_nonnegative_absolute_lift S w _ _ hw
      (fun a ha => ((hT N hN (L a) (hL a ha) (d a)).2 j).le)

end
end ImbalancedChen.P2OriginalBankOldProfilePassage
