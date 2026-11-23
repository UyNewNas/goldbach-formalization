import ImbalancedChen.P2OriginalSeedGammaRowPrices
import ImbalancedChen.P2OriginalSeedPositiveBalances
import MathlibNt.Wu2008DoubleSieve.Omega3SourceBounds
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledKernel
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalSignedSource
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPhiOmega2

/-! The original seed at 11/5 on every classical Wu source box. The
arithmetic Gamma prices and signed mother use the same convolution
multiplicities, strict count, total Q and li-normalizer. Both upper anchors
and three negative singleton counts are paid at their actual windows. -/

namespace ImbalancedChen.P2OriginalWuSeedGammaSignedCount

noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted (Phi Theta cutoff weightedQuotient localQuotient)
open P2EnhancedTwentyOneQuotientFinite (quotientLocal)
open P2EnhancedTwentyOneSourceComparison (twentyOne_source_comparison)
open P2EnhancedSwitchedTrueNormalization (trueAlpha)
open P2EnhancedBadGamma5CostTheta (convertedBad badRawCost)
open P2EnhancedGroupedTripleDictionary (words costIndex)
open P2EnhancedShortWordInclusiveMass (convertedOrdinary)
open P2SeedOmegaLiteralFunctional (switchedMass correction negative)
open P2SeedOmegaLiteralFibre (s s0 phi1 phi2 phi3 a0 a2 a3 b)
open P2EnhancedTwentyOneChildCorrection (positivePairs switchedCount localPositivePairs localSwitched)
open P2ActualSameQTwentyOnePositiveSourceBinding (actualLocalPrimeMass actual_marked_source_identity)
open Part5OriginalH430SeedConvertedMass (first_seed_after_converted ordinaryPart)
open Part5OriginalH430SignedSeedCount (signedPositive)
open P2OriginalSeedGammaRowPrices (original_seed_gamma_row_prices)
open P2OriginalSeedPositiveBalances (goodPairBalance testedFibreBalance
  positive_component_to_original_balances)
open FourthRowPhiOmega2 (J)
open scoped Classical BigOperators Interval

def fiveCounts {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  4*wuBoxPhi N δ W s0+wuBoxPhi N δ W phi1-
    wuOmega2Sum N δ s s0 W-wuOmega2Sum N δ phi2 s0 W-wuOmega2Sum N δ phi3 s0 W

theorem original_quotient_as_five_counts {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    let Q := (N:ℝ)^(1/2-δ)
    let D := boxConvolutionSupport W
    let σ := fun d => (convolutionCoeff W d : ℝ)
    weightedQuotient N Q D σ = fiveCounts N δ W+positivePairs N Q D σ+switchedCount N Q D σ := by
  dsimp only
  simp only [fiveCounts, weightedQuotient, localQuotient, quotientLocal, positivePairs,
    localPositivePairs, switchedCount, localSwitched, wuBoxPhi, convolutionSieveCount,
    boxConvolutionSupport, wuOmega2Sum, wuOmega2, fourthRowMotherSingle, wuLocalCutoff,
    cutoff, s, s0, phi1, phi2, phi3, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib,
    mul_sum, mul_left_comm]
  <;> ring

private theorem negative_reflection (x : ℝ) : fourthRowClassicalJ x s0 = negative (1/x) := by
  let F (u : ℝ) := Real.log (s0*u-1)/(u*(1-u))
  have h0 : 1/s0 = a0 := by norm_num [s0,a0]
  calc
    fourthRowClassicalJ x s0 = ∫ u in (1-1/x)..(1-a0), F u := by
      unfold fourthRowClassicalJ
      rw [h0]
    _ = ∫ u in a0..(1/x), F (1-u) :=
      (intervalIntegral.integral_comp_sub_left F (1:ℝ)).symm
    _ = negative (1/x) := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only [F]
      rw [show 1-(1-u)=u by ring, mul_comm (1-u) u]

/-- One threshold before the depth, shrinking convolution windows, label
multiplicities and seven individual Gamma rows. The last inequality
retains the four ordinary pair windows and switched prime comparison in
the manuscript's explicit positive component. -/
theorem all_classical_boxes_seed_prices_and_signed_count (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      let Q := (N : ℝ)^(1/2-δ)
      let W := convolutionWuWindows N Δ V
      let D := boxConvolutionSupport W
      let σ := fun d => (convolutionCoeff W d : ℝ)
      let θ := boxTheta N Q W
      (convertedBad N Q D σ ≤ badRawCost*θ+(ε/2)*θ) ∧
      (∀ j : Fin 7, ((words j).map (convertedOrdinary N Q D σ)).sum ≤
        switchedMass (costIndex j)*θ+((words j).length : ℝ)*((ε/28)*θ)) ∧
      5*(wuBoxPhi N δ W (11/5)-(1-1/50:ℝ)*θ) ≤
        goodPairBalance N Q D σ + testedFibreBalance N Q D σ + ε*θ := by
  have hhalf : δ < 1/2 := by linarith only [hδhi]
  let η := wuLocalExponent k δ
  have hη : 0 < η := wuLocalExponent_pos k hδ hhalf
  obtain ⟨Tg, h4, hg⟩ := original_seed_gamma_row_prices hη hε
  obtain ⟨Ts, _, hs⟩ := first_seed_after_converted hη
  have hthird : 0 < ε/3 := by positivity
  obtain ⟨Tp, _, hp⟩ := twentyOne_source_comparison
    (show 0 < η/10 by positivity) hthird
  obtain ⟨Tc, _, hc⟩ := positive_component_to_original_balances hη
    (show 0 < η/10 by positivity) hthird
  obtain ⟨Tw, _, hw⟩ := omega3_source_window_lower k hδ hhalf
  let p : SecondFunctionalParameters := ⟨s,s0,phi1,phi2,phi3⟩
  have hrow : p = SecondFunctionalParameters.row1 := by
    norm_num [p, SecondFunctionalParameters.row1, s,s0,phi1,phi2,phi3]
  have hpRow : p.MotherAdmissible := hrow.symm ▸ SecondFunctionalParameters.row1_motherAdmissible
  obtain ⟨Ta, _, ha⟩ := SecondFunctionalPhiOmega2.actual_limit_block p hpRow
    (by norm_num [p,s]) (by norm_num [p,s0]) (by norm_num [p,s0]) (k+1) (by omega)
    hδ hδhi hthird
  let T0 := max (max Tg Ts) (max Tp (max Tw Ta))
  have hT0 : Tg ≤ T0 := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨max T0 Tc, h4.trans (hT0.trans (le_max_left _ _)), ?_⟩
  intro N hNT he i Δ V hb
  have hN := (le_max_left T0 Tc).trans hNT
  have hNc := (le_max_right T0 Tc).trans hNT
  have hNg := ((le_max_left Tg Ts).trans (le_max_left (max Tg Ts) (max Tp (max Tw Ta)))).trans hN
  have hNs := ((le_max_right Tg Ts).trans (le_max_left (max Tg Ts) (max Tp (max Tw Ta)))).trans hN
  have hNpa := (le_max_right (max Tg Ts) (max Tp (max Tw Ta))).trans hN
  have hNp := (le_max_left Tp (max Tw Ta)).trans hNpa
  have hNwa := (le_max_right Tp (max Tw Ta)).trans hNpa
  have hNw := (le_max_left Tw Ta).trans hNwa
  have hNa := (le_max_right Tw Ta).trans hNwa
  have hN4 := h4.trans hNg
  have hN1 : 1 ≤ N := by omega
  let Q := (N : ℝ)^(1/2-δ)
  let W := convolutionWuWindows N Δ V
  let D := boxConvolutionSupport W
  let σ := fun d => (convolutionCoeff W d : ℝ)
  have hσ (d : ℕ) (_ : d ∈ D) : 0 ≤ σ d := Nat.cast_nonneg _
  have bounds (d : ℕ) (hd : d ∈ D) :=
    wuLocal_support_bounds hN1 hδ hhalf hb.2.2.2.2.1
      ((boxSquaredPrefixes_iff _ _).mp hb.2.2.2.2.2) hd
  have hd (d : ℕ) (hm : d ∈ D) : 0 < d := (bounds d hm).1
  have hscale (d : ℕ) (hm : d ∈ D) : (N : ℝ)^η ≤ Q/d := (bounds d hm).2.2
  have hα (d : ℕ) (hm : d ∈ D) : 2 ≤ trueAlpha N Q d :=
    SecondFunctionalCoupled.actual_phi_ge_two hN4 hδ hhalf hb hm
  have prices := hg N hNg Q D σ hd hσ hscale hα
  refine ⟨prices.1, prices.2, ?_⟩
  have hcentre := hs N hNs Q D σ hd hσ hscale hα
  have hQ : Q ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN1 : (1 : ℝ) ≤ N) (show 1/2-δ ≤ 1 by linarith)
  have floors (d : ℕ) (hm : d ∈ D) :=
    wu_buchstab_prime_window_bounds (s := 2) (t := 227/50) (by omega : 2 ≤ N)
      hδ hhalf hb le_rfl (by norm_num) (by norm_num) hm
  have hprime (d : ℕ) (hm : d ∈ D) (q : ℕ) (hq : q ∈ d.primeFactors) :
      (N : ℝ)^(η/10) ≤ q := by
    have hq' := Nat.mem_primeFactors.mp hq
    exact omega3_support_prime_lower W (fun j p hpw => by
      have hf := hw N hNw i Δ V hb j p hpw
      exact ⟨hf.1, hf.2.2⟩) hm hq'.1 hq'.2.1
  have hparent := hp N hNp he Q D σ hQ hd hσ (fun d hm => (floors d hm).2.2.1)
    hprime (fun d hm => (floors d hm).2.2.2.1)
  have hpositive := hc N hNc he Q D σ hQ hd hσ hscale hprime (fun d hm => (floors d hm).2.2.2.1)
  change 5*Phi N Q D σ (11/5) ≤ weightedQuotient N Q D σ+(ε/3)*Theta N Q D σ at hparent
  rw [original_quotient_as_five_counts N δ W, actual_marked_source_identity Q D σ hN4 he hd] at hparent
  have hbox := wuSourceBox_mono_depth (k := k) (l := k+1) (by omega) hδ
    (show δ ≤ 1 by linarith) hN1 hb
  have hs0lo : 3 ≤ s0 := by norm_num [s0]
  have hs0hi : s0 ≤ 5 := by norm_num [s0]
  have single (x : ℝ) (hx : 2 ≤ x) (hxs : x ≤ s0) (hr : 2 ≤ s0-s0/x) :
      negative (1/x) ≤ J δ x s0 := by
    rw [SecondFunctionalSignedCore.J_split hδ hhalf hx hxs hs0lo hs0hi hr, negative_reflection]
    exact le_add_of_nonneg_right (firstFunctionalGain_integral_nonneg hδ hhalf hx hxs hs0lo hs0hi)
  have hbJ : negative b ≤ J δ s s0 := by
    simpa only [show 1/s=b by norm_num [s,b]] using
      single s (by norm_num [s]) (by norm_num [s,s0]) (by norm_num [s,s0])
  have haJ : negative a2 ≤ J δ phi2 s0 := by
    simpa only [show 1/phi2=a2 by norm_num [phi2,a2]] using
      single phi2 (by norm_num [phi2]) (by norm_num [phi2,s0]) (by norm_num [phi2,s0])
  have hcJ : negative a3 ≤ J δ phi3 s0 := by
    simpa only [show 1/phi3=a3 by norm_num [phi3,a3]] using
      single phi3 (by norm_num [phi3]) (by norm_num [phi3,s0]) (by norm_num [phi3,s0])
  have h0 : wuUpperCoefficient s0 = 1+correction s0 :=
    jr1965F_normalized_innerIntegral hs0lo hs0hi
  have h1 : wuUpperCoefficient phi1 = 1+correction phi1 :=
    jr1965F_normalized_innerIntegral (by norm_num [phi1]) (by norm_num [phi1])
  have hf0 := wuImprovementLimit_nonneg true hδ hhalf
    (show 1 ≤ s0 by norm_num [s0]) (show s0 ≤ 10 by norm_num [s0])
  have hf1 := wuImprovementLimit_nonneg true hδ hhalf
    (show 1 ≤ phi1 by norm_num [phi1]) (show phi1 ≤ 10 by norm_num [phi1])
  have hfive := ha N hNa he i Δ V hbox
  change fiveCounts N δ W ≤
    (4*wuUpperCoefficient s0+wuUpperCoefficient phi1-4*wuImprovementLimit true δ s0-
      wuImprovementLimit true δ phi1-J δ s s0-J δ phi2 s0-J δ phi3 s0+ε/3)*Theta N Q D σ at hfive
  have hbound : fiveCounts N δ W ≤
      (4*(1+correction s0)+(1+correction phi1)-
        (negative b+negative a2+negative a3)+ε/3)*Theta N Q D σ := by
    apply hfive.trans
    apply mul_le_mul_of_nonneg_right
    · linarith only [h0,h1,hf0,hf1,hbJ,haJ,hcJ]
    · exact gamma5Mass_theta_nonneg (by omega : 2 ≤ N) hδ hhalf hb
  change 5*(Phi N Q D σ (11/5)-(1-1/50:ℝ)*Theta N Q D σ) ≤
    goodPairBalance N Q D σ+testedFibreBalance N Q D σ+ε*Theta N Q D σ
  unfold signedPositive at hpositive
  unfold ordinaryPart at hcentre
  linarith only [hcentre, hparent, hbound, hpositive]

end
end ImbalancedChen.P2OriginalWuSeedGammaSignedCount
