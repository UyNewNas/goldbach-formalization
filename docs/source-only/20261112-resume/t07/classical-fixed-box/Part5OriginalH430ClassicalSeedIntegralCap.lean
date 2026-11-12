import ImbalancedChen.Part5OriginalH430ClassicalClampLongCredit
import ImbalancedChen.Part5OriginalH430SeedConvertedMass

/-! Raw Buchstab upper bound for the twenty original occurrences, with the
actual physical alpha at each p. The cap excludes the separately paid Γ5. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSeedIntegralCap
noncomputable section
open Finset Real Wu2008DoubleSieve
open P2EnhancedNonunitWordMass (rawScale)
open P2EnhancedNonunitLabelGeometry (ordinaryNonunitWord)
open P2EnhancedNonunitMarkedMass
open P2EnhancedSwitchedTrueNormalization (trueAlpha)
open P2SeedOmegaLiteralFunctional (switchedMass)
open Part5OriginalH430SeedLastWords (original_last_full_costs)
open P2SeedOmegaLastUnitIntegrals (unit20Mass_log_cap unit21Mass_log_cap)
open scoped Classical BigOperators

def wordsSum (F : List ℕ → ℝ) : ℝ :=
  ∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map F).sum

def cost : ℝ := ∑ j : Fin 13,switchedMass j

theorem words_mono {F G : List ℕ → ℝ}
    (h : ∀ j : Fin 13, ∀ w∈secondFunctionalMotherGammaWords (9+j.val),F w≤G w) :
    wordsSum F≤wordsSum G :=
  sum_le_sum (fun j _ => secondFunctionalMother_list_sum_mono _ F G (h j))

theorem words_add (F G : List ℕ → ℝ) :
    wordsSum (fun w => F w+G w)=wordsSum F+wordsSum G := by
  simp only [wordsSum,List.sum_map_add,sum_add_distrib]

theorem words_mul (c : ℝ) (F : List ℕ → ℝ) :
    wordsSum (fun w => c*F w)=c*wordsSum F := by
  simp only [wordsSum,List.sum_map_mul_left,mul_sum]

theorem words_const (c : ℝ) : wordsSum (fun _ => c)=20*c := by
  rw [wordsSum,P2EnhancedSwitchedUnsiftedSource.all_switched_multiplicities]
  ring

theorem words_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (F : ι → List ℕ → ℝ) :
    wordsSum (fun cs => ∑ i∈S,F i cs)=∑ i∈S,wordsSum (F i) := by
  induction S using Finset.induction_on with
  | empty => simp only [sum_empty,words_const,mul_zero]
  | @insert i S hi ih => simp only [sum_insert hi,words_add,ih]

theorem original_integral_cap {α : ℝ} (ha : 2≤α) :
    wordsSum (fun cs => nonunitIntegral cs α)≤cost := by
  apply sum_le_sum
  intro j _
  have ht := P2EnhancedGroupedTripleDictionary.original_Gamma9_to_15_literal_cap ha
  have hf := P2EnhancedFourWordCostTheta.four_word_literal_cap α
  have hl := original_last_full_costs α
  have h20 := (unit20Mass_log_cap α).1
  have h21 := (unit21Mass_log_cap α).1
  fin_cases j
  all_goals first
    | exact ht 0 | exact ht 1 | exact ht 2 | exact ht 3
    | exact ht 4 | exact ht 5 | exact ht 6
    | simpa only [secondFunctionalMotherGammaWords,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero] using hf 0
    | simpa only [secondFunctionalMotherGammaWords,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero] using hf 1
    | simpa only [secondFunctionalMotherGammaWords,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero] using hf 2
    | simpa only [secondFunctionalMotherGammaWords,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero] using hf 3
    | simpa only [secondFunctionalMotherGammaWords,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero] using
        (le_add_of_nonneg_right h20).trans hl.1
    | simpa only [secondFunctionalMotherGammaWords,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero] using
        (le_add_of_nonneg_right h21).trans hl.2

theorem all_raw_words_upper {η ε : ℝ} (hη : 0<η) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (Q : ℝ) (d : ℕ),0<d →
      (N:ℝ)^η≤Q/d → 2≤trueAlpha N Q d →
      wordsSum (ordinaryNonunitWord N Q d)≤rawScale N Q d*(cost+ε) := by
  have hall (w : thresholdWords) := original_word_upper w.val
    (threshold_word_nonempty w.property) hη (show 0<ε/20 by positivity)
  choose T hT hrow using hall
  refine ⟨max 4 (univ.sup T),le_max_left _ _,?_⟩
  intro N hN Q d hd hscale ha
  have h4 : 4≤N := (le_max_left _ _).trans hN
  have hR : 1<Q/(d:ℝ) := (one_lt_rpow
    (by exact_mod_cast (show 1<N by omega)) hη).trans_le hscale
  have hr : 0≤rawScale N Q d := div_nonneg (Nat.cast_nonneg N)
    (mul_nonneg (Nat.cast_nonneg d) (log_pos hR).le)
  have hraw := words_mono (F:=ordinaryNonunitWord N Q d)
    (G:=fun w => rawScale N Q d*(nonunitIntegral w (trueAlpha N Q d)+ε/20)) (by
      intro j w hw
      let i : thresholdWords := ⟨w,occurrence_mem_threshold hw⟩
      exact hrow i N ((le_sup (mem_univ i)).trans ((le_max_right _ _).trans hN))
        Q d hd hscale ha)
  rw [words_mul,words_add,words_const,show 20*(ε/20)=ε by ring] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left (add_le_add_right (original_integral_cap ha) _) hr)

end
end ImbalancedChen.Part5OriginalH430ClassicalSeedIntegralCap
