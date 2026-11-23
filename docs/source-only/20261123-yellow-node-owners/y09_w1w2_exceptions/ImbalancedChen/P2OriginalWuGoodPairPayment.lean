import ImbalancedChen.P2OriginalHalfOpenOrdinaryPairTheta
import ImbalancedChen.P2OriginalWuGoodPairLabels
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairClassicalSource

/-! The good ordinary contribution on the original classical Wu boxes.
Depth, box width, convolution labels, all 36 rows and all four
half-open windows are chosen after the common threshold. -/
namespace ImbalancedChen.P2OriginalWuGoodPairPayment
noncomputable section
open Finset Set Real Filter Wu2008DoubleSieve
open Wu2008DoubleSieve.MotherPair
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalPositiveSameQMassLift (residualExponent sameQ_residualExponent)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2OriginalW2CountTupleReindex (sourceGoodOccurrence windowOccurrence)
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430OrdinaryPairCounts (ordinaryIntegral)
open P2OriginalHalfOpenOrdinaryPairTheta P2OriginalWuGoodPairLabels
open scoped Classical BigOperators Topology

private theorem ordinary_bounds (a : Fin 36) (j : Fin 4) :
    0 ≤ ordinaryIntegral a j ∧ ordinaryIntegral a j ≤ 45/4 := by
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem a)
  have hs := W2PairDomain_subset hg j
  have h := pairMass_eq_original (measurableSet_W2PairDomain _ _) hs
    (fun _ hx => (W2PairDomain_geometry hg j hx).2)
  exact ⟨(pairMass_nonneg _).trans_eq h,h.symm.le.trans (pairMass_le_45_fourths hs)⟩

private theorem levels {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2≤N) (hδ : 0<δ) (hδhi : δ<1/2) (hb : wuSourceBox k δ N i Δ V)
    {d : ℕ} (hd : d∈boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    let Q := (N:ℝ)^(1/2-δ)
    0<d ∧ residualExponent N Q d ∈ Icc (min 1 (wuLocalExponent k δ)) 1 ∧
      Q = (d:ℝ)*(N:ℝ)^(residualExponent N Q d) := by
  obtain ⟨hdpos,hlo,hR,_⟩ := gamma5Mass_support_geometry hN hδ hδhi hb hd
  let Q := (N:ℝ)^(1/2-δ)
  have hq := sameQ_residualExponent (by omega : 1<N) hdpos (zero_lt_one.trans hR)
  have hN' : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hL : (N:ℝ)^(residualExponent N Q d) = Q/d := by
    apply (eq_div_iff (Nat.cast_pos.mpr hdpos).ne').mpr
    calc
      _ = (d:ℝ)*(N:ℝ)^(residualExponent N Q d) := mul_comm _ _
      _ = Q := hq.symm
  have hQN : Q ≤ N := by
    simpa only [Q,rpow_one] using
      rpow_le_rpow_of_exponent_le hN'.le (show 1/2-δ≤1 by linarith)
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hdpos
  have hrN : Q/d ≤ N := (div_le_self (rpow_pos_of_pos (zero_lt_one.trans hN') _).le hd1).trans hQN
  refine ⟨hdpos,⟨?_,?_⟩,hq⟩
  · apply (min_le_right _ _).trans
    exact (rpow_le_rpow_left_iff hN').mp (hlo.trans_eq hL.symm)
  · apply (rpow_le_rpow_left_iff hN').mp
    simpa only [rpow_one] using hL.le.trans hrN

/-- Every single good-pair lane, with its first-prime or fixed physical
cutoff on the left. In particular the excluded fifth corner buys no
ordinary integral. -/
theorem all_classical_good_pair_counts (k : ℕ) {δ ε : ℝ}
    (hδ : 0<δ) (hδhi : δ≤1/10) (he : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N → ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ),
      wuSourceBox k δ N i Δ V → ∀ (a : Fin 36) (j : Fin 4),
      let W := convolutionWuWindows N Δ V
      let Q := (N:ℝ)^(1/2-δ)
      (∑ d∈boxConvolutionSupport W, (convolutionCoeff W d:ℝ) *
        sourceGoodOccurrence N Q (actualState N) d (originalW2At a) j) ≤
        (ordinaryIntegral a j + ε)*boxTheta N Q W := by
  have hhalf : δ<1/2 := by linarith
  let lo : ℝ := min 1 (wuLocalExponent k δ)
  have hlo : 0<lo := lt_min zero_lt_one (wuLocalExponent_pos k hδ hhalf)
  have he16 : 0<ε/16 := by positivity
  let η : ℝ := min 1 (ε/(6*(45/4+1)))
  have hη : 0<η := lt_min zero_lt_one (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηe : 6*η*(45/4+1)≤ε := by
    have h := (le_div_iff₀ (by norm_num : (0:ℝ)<6*(45/4+1))).mp
      (min_le_right (1:ℝ) (ε/(6*(45/4+1))))
    dsimp only [η]
    linarith only [h]
  have hcap : CapAdmissible 5 (49/100) :=
    ⟨by norm_num,le_rfl,by norm_num,by norm_num⟩
  obtain ⟨Tb,h4,hb⟩ := classical_mask_upper hcap (k+1) (by omega) hδ hδhi hη
    (show 0<ε/4 by positivity)
  obtain ⟨Tm,_,hm⟩ := all_ordinary_good_windows hlo (min_le_left _ _) he16
  refine ⟨max Tb Tm,h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven i Δ V hbox a j
  have hNb := (le_max_left Tb Tm).trans hN
  have hNm := (le_max_right Tb Tm).trans hN
  have h2 : 2≤N := by have := h4.trans hNb; omega
  let W := convolutionWuWindows N Δ V
  let D := boxConvolutionSupport W
  let Q := (N:ℝ)^(1/2-δ)
  let σ (d : ℕ) := (convolutionCoeff W d:ℝ)
  let L := residualExponent N Q
  let θ := boxTheta N Q W
  let X := goodLabels N δ W (originalW2At a) j
  have hbox' := wuSourceBox_mono_depth (k:=k) (l:=k+1) (by omega) hδ
    (show δ≤1 by linarith) (by omega : 1≤N) hbox
  have hlabels := goodLabels_subset_cap h2 hδ hhalf hbox a j
  have hupper := hb N hNb hEven i Δ V hbox' X hlabels
  have hcounts := marked_count_le_fixed h2 hδ hhalf hbox a j
  have hmain := marked_main_exact h2 hδ hhalf hbox a j
  have hl (d : ℕ) (hd : d∈D) := levels h2 hδ hhalf hbox hd
  have hsum := hm N hNm Q D σ L (fun d hd => (hl d hd).1)
    (fun d _ => Nat.cast_nonneg _) (fun d hd => (hl d hd).2.1)
    (fun d hd => (hl d hd).2.2) a j
  have hraw :
      gamma5ClassicalMainMass N δ W X = ∑ d∈D, σ d *
        windowOccurrence N Q (L d) d (originalW2At a) j (fun p q => thetaAtom N Q (d*p*q)) := by
    apply hmain.trans
    apply sum_congr rfl
    intro d hd
    rw [rawWindow_eq_physical (hl d hd).1 (hl d hd).2.2]
  change |(∑ d∈D, σ d * windowOccurrence N Q (L d) d (originalW2At a) j
      (fun p q => thetaAtom N Q (d*p*q)))-ordinaryIntegral a j*θ| ≤ (ε/16)*θ at hsum
  rw [←hraw] at hsum
  have hmass : gamma5ClassicalMainMass N δ W X ≤ (ordinaryIntegral a j+ε/16)*θ := by
    rw [add_mul]
    linarith only [(abs_le.mp hsum).2]
  have hθ : 0≤θ := gamma5Mass_theta_nonneg h2 hδ hhalf hbox
  have hbudget := classical_slack_budget hη hη1 he (ordinary_bounds a j).1
    (ordinary_bounds a j).2 hηe
  dsimp only
  apply hcounts.trans (hupper.trans _)
  calc
    _ ≤ (1+η)^2*((ordinaryIntegral a j+ε/16)*θ)+(ε/4)*θ :=
      add_le_add_right (mul_le_mul_of_nonneg_left hmass (sq_nonneg _)) _
    _ = ((1+η)^2*(ordinaryIntegral a j+ε/16)+ε/4)*θ := by ring
    _ ≤ (ordinaryIntegral a j+ε)*θ := mul_le_mul_of_nonneg_right hbudget hθ

end
end ImbalancedChen.P2OriginalWuGoodPairPayment
