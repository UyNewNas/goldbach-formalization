import ImbalancedChen.P4BOriginalFiniteSignedTrim
import ImbalancedChen.P5ProperPowerActualReciprocalTail

/-! The proper-power correction at the original rank-two physical pair.
The nonnegative dyadic partition sums to one on every ordered integer
word. One of the two true coordinate occurrences supplies the reciprocal
tail, including words with two proper-power occurrences. -/
namespace ImbalancedChen.P4BOriginalFiniteProperWords
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalFiniteSignedTrim (pairLicence)
open P4BOuterRampRoughness (baseline)
open P5Z.ActualEtaPsiOccurrenceBudget (chi eta eta_bounds)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank chart_partition tupleProfile bump_bounds R R_pos)
open P5Z.LicensedOriginalIntegerProfile
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.ActualLabelledPrimeSmoothCharts (chartTerm)
open P5Z.IndependentPrimeSourceWordDictionary (wordKernel)
open Part3.OriginalProperPowerActualChart
open Part3.OriginalProperPowerChartCount (properPowers)
open Part3.AllKLambdaChartCorrection (properChartWords properChartWords_spec lambdaWord roughWord)
open Part3.AllKFamilyLambdaCorrectionBound (lambdaWord_norm_le_one roughWord_norm_le_one covered_nonnegative_sum_le)
open P5Z.ProperPowerActualReciprocalTail
open P5Z.RoughSquareWeightedBudget (logBudget harmonic_Icc_le_logBudget)
open P5Z.ProperPowerSignedMeanHBTransport (signedRow)

abbrev exponent : ℝ := 19/96

private theorem original_window_nonnegative (js ps : List ℕ) :
    ((‖tupleProfile chi js ps‖ : ℝ) : ℂ) = tupleProfile chi js ps := by
  have hm : Antitone chi := fun x y hxy =>
    sub_le_sub_left (Real.smoothTransition.monotone (sub_le_sub_right hxy 1)) 1
  have hb (x : ℝ) : 0≤chi x ∧ chi x≤1 :=
    ⟨sub_nonneg.mpr (eta_bounds x).2,sub_le_self _ (eta_bounds x).1⟩
  induction js generalizing ps with
  | nil => cases ps <;> simp [tupleProfile]
  | cons j js ih =>
    cases ps with
    | nil => simp [tupleProfile]
    | cons p ps =>
      simp only [tupleProfile,norm_mul,Complex.ofReal_mul,ih,
        P5Z.ExactOriginalSmoothDyadicPartition.psi,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (bump_bounds chi hm hb (div_nonneg (Nat.cast_nonneg p) (R_pos j).le)).1]

private theorem partition_norm {N : ℕ} {ps : List ℕ} (hps : ps∈properChartWords N 2) :
    (∑ js∈chartBank N 2,‖tupleProfile chi js ps‖)=1 := by
  have hs := P5Z.ExactOriginalSmoothDyadicPartition.words_spec (Finset.Icc 1 N) 2 ps
    (properChartWords_spec hps).1
  have hp := chart_partition chi (fun _ h => actual_chi_one h) (fun _ h => actual_chi_zero h)
    N ps (fun p hm => Finset.mem_Icc.mp (hs.2 p hm))
  rw [hs.1] at hp
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum,Complex.ofReal_one,original_window_nonnegative] using hp

def active {W : (Fin 2 → ℕ) → ℝ} (L : Licence 2 W) (N : ℕ) : Finset (List ℕ) :=
  (properChartWords N 2).filter (fun ps => listExtension L ps≠0)

private theorem word_indices {N : ℕ} {ps : List ℕ} (hp : ps∈properChartWords N 2) :
    ps.length=2 ∧ ∀ i : Fin 2,wordVector 2 ps i∈Finset.Icc 1 N := by
  have h := P5Z.ExactOriginalSmoothDyadicPartition.words_spec (Finset.Icc 1 N) 2 ps
    (properChartWords_spec hp).1
  refine ⟨h.1,?_⟩
  intro i
  have hi : i.val<ps.length := by rw [h.1]; exact i.isLt
  apply h.2
  rw [wordVector,List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem word_geometry {b kappa s : ℝ} {N : ℕ}
    (hb : 0<b) (hk : 0<kappa) (hs : 0<s) (hgap : 2*s≤baseline b kappa-exponent)
    {ps : List ℕ} (hp : ps∈active (pairLicence hb hs hgap N) N) :
    (∀ i : Fin 2,(N:ℝ)^exponent≤(wordVector 2 ps i:ℝ)) ∧
      (ps.prod:ℝ)≤Real.exp 1*(N:ℝ) := by
  let v := wordVector 2 ps
  have hps := Finset.mem_filter.mp hp
  have hlen := (word_indices hps.1).1
  have hp' : P4BArbitraryWidthUpperPairProfile.profile b kappa s N (fun i => (v i:ℝ))≠0 := by
    change integerExtension (pairLicence hb hs hgap N) v≠0
    rw [← listExtension_ofFn,ofFn_wordVector hlen]
    exact hps.2
  have hg : 2*s≤baseline b kappa-1*exponent := by simpa only [one_mul] using hgap
  have h := P4BArbitraryWidthUpperPairProfile.nonzero_data hb (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<exponent) hs hg hp'
  have hwidth := P4BArbitraryWidthUpperPairProfile.legal_width_le_one hb hk
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<exponent) hg
  have hprod : (ps.prod:ℝ)=(v 0:ℝ)*(v 1:ℝ) := by
    have he := congrArg (fun u : List ℕ => (u.prod:ℝ)) (ofFn_wordVector hlen)
    simpa only [Nat.cast_list_prod,List.map_ofFn,List.prod_ofFn,Fin.prod_univ_two,v] using he.symm
  refine ⟨fun i => by simpa only [one_mul,v] using (h.2.2.1 i).le,?_⟩
  rw [hprod]
  exact h.2.2.2.2.le.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr hwidth) (Nat.cast_nonneg _))

/-- All actual proper words are counted before any residue estimate. The
two possible marked positions only overcount their intersection. -/
theorem active_card_le {b kappa s : ℝ} {N : ℕ} (hN : 1≤N)
    (hb : 0<b) (hk : 0<kappa) (hs : 0<s) (hgap : 2*s≤baseline b kappa-exponent) :
    ((active (pairLicence hb hs hgap N) N).card:ℝ) ≤
      Real.exp 1*(N:ℝ)*(2*(reciprocalTailBudget N ((N:ℝ)^exponent)*logBudget N)) := by
  let S := active (pairLicence hb hs hgap N) N
  let A := (N:ℝ)^exponent
  have hA : 0<A := Real.rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) _
  let B := fun i : Fin 2 => S.filter (fun ps => wordVector 2 ps i∈properTail N A)
  have hB (i : Fin 2) : (∑ ps∈B i,1/(ps.prod:ℝ))≤reciprocalTailBudget N A*logBudget N := by
    let Z := fun j : Fin 2 => if j=i then properTail N A else Finset.Icc 1 N
    have h := ordered_reciprocal_le_product (B i) Z
      (fun ps hp => (word_indices (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1) (by
        intro ps hp j
        have hps := Finset.mem_filter.mp hp
        by_cases hj : j=i
        · simpa only [Z,hj,if_pos rfl] using hps.2
        · simpa only [Z,if_neg hj] using
            (word_indices (Finset.mem_filter.mp hps.1).1).2 j)
    apply h.trans
    let U := fun j : Fin 2 => if j=i then reciprocalTailBudget N A else logBudget N
    calc
      _ ≤ ∏ j : Fin 2,U j := by
        apply Finset.prod_le_prod
        · intro j hj
          exact Finset.sum_nonneg (fun _ _ => by positivity)
        · intro j hj
          by_cases he : j=i
          · simpa only [Z,U,if_pos he] using properTail_reciprocal_le hN hA
          · simpa only [Z,U,if_neg he] using harmonic_Icc_le_logBudget N
      _ = _ := by fin_cases i <;> simp [U,Fin.prod_univ_two,mul_comm]
  have hcover := covered_nonnegative_sum_le S Finset.univ B (fun ps => 1/(ps.prod:ℝ))
    (fun _ => by positivity) (by
      intro ps hp _
      have hps := (Finset.mem_filter.mp hp).1
      obtain ⟨_,i,p,t,hprime,ht,hpower,_⟩ := properChartWords_spec hps
      have hw := (word_indices hps).2 i
      have hfloor := (word_geometry hb hk hs hgap hp).1 i
      exact ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hp,Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hw,p,t,hprime,ht,hpower⟩,hfloor⟩⟩⟩)
  have hrec : (∑ ps∈S,1/(ps.prod:ℝ))≤2*(reciprocalTailBudget N A*logBudget N) := by
    apply hcover.trans
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
      using Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin 2))) (fun i _ => hB i)
  calc
    (S.card:ℝ) = ∑ _ps∈S,(1:ℝ) := by simp
    _ ≤ ∑ ps∈S,(Real.exp 1*(N:ℝ))*(1/(ps.prod:ℝ)) := by
      apply Finset.sum_le_sum
      intro ps hp
      have hi := P5Z.ExactOriginalSmoothDyadicPartition.words_spec (Finset.Icc 1 N) 2 ps
        (properChartWords_spec (Finset.mem_filter.mp hp).1).1
      have hprod : 0<ps.prod := List.prod_pos (fun m hm => (Finset.mem_Icc.mp (hi.2 m hm)).1)
      have hpos : (0:ℝ)<ps.prod := by exact_mod_cast hprod
      simpa only [div_eq_mul_inv,one_div] using
        (le_div_iff₀ hpos).mpr (by simpa only [one_mul] using (word_geometry hb hk hs hgap hp).2)
    _ = (Real.exp 1*(N:ℝ))*(∑ ps∈S,1/(ps.prod:ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)

/-- The original psi partition is nonnegative on every proper word, so
summing its widths costs exactly one. The chart-dependent rough projector
is kept inside the proper reserve until taking absolute values. -/
theorem proper_chart_sum_le {b kappa s : ℝ} (hb : 0<b) (hs : 0<s)
    (hgap : 2*s≤baseline b kappa-exponent) (K N : ℕ) (kappa0 : ℝ)
    (S : Finset ℕ) (c : ℕ → ℂ) :
    let L := pairLicence hb hs hgap N
    (∑ js∈chartBank N 2,‖properPowerReserve L K N N kappa0 S c js‖) ≤
      ∑ ps∈active L N,‖signedRow S c N ps.prod‖ := by
  let L := pairLicence hb hs hgap N
  let V := fun ps : List ℕ => if listExtension L ps≠0 then ‖signedRow S c N ps.prod‖ else 0
  have term (js ps : List ℕ) (hp : ps∈properChartWords N 2) :
      ‖lambdaWord ps*originalChart L N kappa0 js ps*
        (roughWord (P5Z.ExactOriginalSmoothDyadicPartition.beforeHBCutoff K js) ps*
          wordKernel S c N ps)‖ ≤ ‖tupleProfile chi js ps‖*V ps := by
    rw [P4BActualUpperTrimPayment.wordKernel_eq_signedRow]
    by_cases hn : listExtension L ps=0
    · simp [originalChart,chartTerm,P5Z.ActualLabelledPrimeSmoothCharts.trimmedWeight,V,hn]
    have hW : ‖(listExtension L ps:ℂ)‖≤1 := by
      have hi := (word_indices hp).1
      have he : listExtension L ps=integerExtension L (wordVector 2 ps) := by
        rw [← listExtension_ofFn,ofFn_wordVector hi]
      rw [he,Complex.norm_real,Real.norm_eq_abs]
      have h := P4BArbitraryWidthUpperPairProfile.bounds b kappa s N
        (fun i => (wordVector 2 ps i:ℝ))
      exact (abs_of_nonneg h.1).le.trans h.2
    have hEta (x : ℝ) : ‖(eta x:ℂ)‖≤1 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (eta_bounds x).1]
      exact (eta_bounds x).2
    simp only [originalChart,chartTerm,P5Z.ActualLabelledPrimeSmoothCharts.trimmedWeight,
      norm_mul,V,if_pos hn]
    calc
      _ ≤ 1*(‖tupleProfile chi js ps‖*(1*1))*(1*‖signedRow S c N ps.prod‖) := by
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · apply mul_le_mul (lambdaWord_norm_le_one _) _ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hEta _) hW (norm_nonneg _) zero_le_one) (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_right (roughWord_norm_le_one _ _) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑ js∈chartBank N 2, ∑ ps∈properChartWords N 2,‖tupleProfile chi js ps‖*V ps := by
      apply Finset.sum_le_sum
      intro js hjs
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (term js))
    _ = ∑ ps∈properChartWords N 2,V ps := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ps hp
      rw [← Finset.sum_mul,partition_norm hp,one_mul]
    _ = _ := by simp only [active,Finset.sum_filter,V,L]

end
end ImbalancedChen.P4BOriginalFiniteProperWords
