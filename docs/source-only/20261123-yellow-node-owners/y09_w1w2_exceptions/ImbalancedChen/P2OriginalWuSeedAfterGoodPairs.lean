import ImbalancedChen.P2OriginalWuGoodPairPayment
import ImbalancedChen.P2OriginalWuSeedGammaSignedCount

namespace ImbalancedChen.P2OriginalWuSeedAfterGoodPairs
noncomputable section
open Finset Wu2008DoubleSieve
open P5OriginalActionMassBound (originalW2At)
open P2OriginalW2CountTupleReindex (sourceGoodOccurrence)
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430OrdinaryPairCounts (ordinaryIntegral)
open P2OriginalSeedPositiveBalances (goodPairBalance testedFibreBalance)
open P2OriginalWuGoodPairPayment
open P2OriginalWuSeedGammaSignedCount
open scoped Classical BigOperators

theorem classical_good_balance (k : ℕ) {δ ε : ℝ}
    (hδ : 0<δ) (hδhi : δ≤1/10) (he : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N → ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ),
      wuSourceBox k δ N i Δ V →
      let W := convolutionWuWindows N Δ V
      let Q := (N:ℝ)^(1/2-δ)
      goodPairBalance N Q (boxConvolutionSupport W) (fun d => (convolutionCoeff W d:ℝ)) ≤
        ε*boxTheta N Q W := by
  obtain ⟨T,h4,hT⟩ := all_classical_good_pair_counts k hδ hδhi (show 0<ε/4 by positivity)
  refine ⟨T,h4,?_⟩
  intro N hN hEven i Δ V hb
  let W := convolutionWuWindows N Δ V
  let Q := (N:ℝ)^(1/2-δ)
  let θ := boxTheta N Q W
  let C (j : Fin 4) := ∑ d∈boxConvolutionSupport W,(convolutionCoeff W d:ℝ)*
    sourceGoodOccurrence N Q (actualState N) d (originalW2At 0) j
  have hsum : (∑ j : Fin 4, C j) ≤ ∑ j : Fin 4, (ordinaryIntegral 0 j+ε/4)*θ :=
    sum_le_sum (fun j _ => hT N hN hEven i Δ V hb 0 j)
  have htotal : (∑ j : Fin 4,(ordinaryIntegral 0 j+ε/4)*θ) =
      (∑ j : Fin 4,ordinaryIntegral 0 j)*θ+ε*θ := by
    simp only [add_mul,sum_add_distrib,←sum_mul,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  dsimp only
  unfold goodPairBalance
  simp_rw [mul_sum]
  rw [sum_comm]
  change (∑ j : Fin 4,C j) - (∑ j : Fin 4,ordinaryIntegral 0 j)*θ ≤ ε*θ
  linarith only [hsum,htotal]

/-- The 21-term seed now has only the signed prime-test comparison on
the same bad and long fibres, with the original 681/400 price. -/
theorem classical_seed_after_good_pairs (k : ℕ) {δ ε : ℝ}
    (hδ : 0<δ) (hδhi : δ≤1/10) (he : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N → ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ),
      wuSourceBox k δ N i Δ V →
      let W := convolutionWuWindows N Δ V
      let Q := (N:ℝ)^(1/2-δ)
      let θ := boxTheta N Q W
      5*(wuBoxPhi N δ W (11/5)-(1-1/50:ℝ)*θ) ≤
        testedFibreBalance N Q (boxConvolutionSupport W)
          (fun d => (convolutionCoeff W d:ℝ)) + ε*θ := by
  obtain ⟨T1,h4,h1⟩ := all_classical_boxes_seed_prices_and_signed_count k hδ hδhi (half_pos he)
  obtain ⟨T2,_,h2⟩ := classical_good_balance k hδ hδhi (half_pos he)
  refine ⟨max T1 T2,h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven i Δ V hb
  have hs := (h1 N ((le_max_left _ _).trans hN) hEven i Δ V hb).2.2
  have hg := h2 N ((le_max_right _ _).trans hN) hEven i Δ V hb
  dsimp only at hs hg ⊢
  linarith only [hs,hg]

end
end ImbalancedChen.P2OriginalWuSeedAfterGoodPairs
