import ImbalancedChen.Part5OriginalH430ClassicalPowerProfile
import ImbalancedChen.P5IndependentTestPrimeChartUniformCutoff

/-! A single pre-HB cutoff threshold for every active original prime word.
The actual cap is 2N. Its exponent here is 1/192 so the previously proved
physical floor N^(1/96) works at this larger cap without changing the target. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalRoughFloor
noncomputable section
open Finset Real Filter
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.ActualLabelledPrimeSmoothCharts
open P5Z.ActualEtaPsiOccurrenceBudget (chi eta)
open P5Z.AdmissibleAllRankIntegerGeometricFamily (licence)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.OriginalPrimeAtlasReserveBranches (roughWord_one_on_prime_word)
open P5Z.IndependentTestPrimeChartUniformCutoff (independent_test_chart_cutoff_eventual)
open Part3.AllKLambdaChartCorrection (primeOnly)
open Part3.AllKFamilyLambdaCorrectionBound (bankWeight bankWeight_support)
open Part5OriginalH430ClassicalPowerProfile (too_short chart_live)
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open Part5OriginalH430ClassicalRadialMarkedRanks (transition_floor)
open Part5OriginalH430ClassicalSmoothNativeFamily (family)
open scoped Classical BigOperators

theorem all_prime_cutoffs :
    ∀ᶠ N : ℕ in atTop,∀ (μ : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8)
      (hc : 0<c) (hc' : c≤1/8) (k : Fin 201) (κ₀ : ℝ) (Q : Finset ℕ) (ρ : ℕ→ℂ)
      (js : List ℕ),js∈chartBank (2*N) k.val →
      roughPrimeReserve (licence (family μ hd hh hh' hc hc') N k) 200 (2*N) N κ₀ Q ρ js=0 := by
  obtain ⟨N0,H⟩ := independent_test_chart_cutoff_eventual 200 (1/192) (by norm_num)
  filter_upwards [transition_floor,eventually_ge_atTop N0,eventually_ge_atTop (2:ℕ)] with N hfloor hn h2
  have h0 : (0:ℝ)≤N := Nat.cast_nonneg _
  have hsq : 2*(N:ℝ)≤(N:ℝ)^(2:ℕ) := by
    have h2' : (2:ℝ)≤N := by exact_mod_cast h2
    simpa only [pow_two] using mul_le_mul_of_nonneg_right h2' h0
  have hsmall : ((2*N:ℕ):ℝ)^(1/192:ℝ)≤cut N := by
    push_cast
    calc
      _ ≤ ((N:ℝ)^(2:ℕ))^(1/192:ℝ) := rpow_le_rpow (by positivity) hsq (by norm_num)
      _ = _ := by
        rw [←rpow_natCast (N:ℝ) 2,←rpow_mul h0]
        norm_num [cut]
  intro μ δ h c hd hh hh' hc hc' k κ₀ Q ρ js hjs
  let A := family μ hd hh hh' hc hc'
  unfold roughPrimeReserve
  apply sum_eq_zero
  intro ps hp
  by_cases ha : originalChart (licence A N k) N κ₀ js ps=0
  · simp [ha]
  have hps := primeTuples_spec (2*N) k.val hp
  have hW := chart_live μ hd hh hh' hc hc' ha
  have hk1 : 1≤k.val := by
    by_contra hh0
    exact hW (too_short μ hd hh hh' hc hc' (by omega) hps.1)
  have hs := bankWeight_support A N k hps.1 hW
  have hpowers (p : ℕ) (hm : p∈ps) : ((2*N:ℕ):ℝ)^(1/192:ℝ)≤(p:ℝ) ∧ (p:ℝ)≤(2*N:ℕ) := by
    have low : (1/2:ℝ)*(N:ℝ)^(1/90:ℝ)≤(p:ℝ) := hs.1 p hm
    exact ⟨hsmall.trans (hfloor.trans (by linarith only [low])),by exact_mod_cast (hps.2 p hm).2.2⟩
  have hw : tupleProfile chi js ps≠0 := (mul_ne_zero_iff.mp ha).1
  have hwin := profile_nonzero_support chi (fun _ h1 => actual_chi_one h1)
    (fun _ h0 => actual_chi_zero h0) js ps hw
  have hz := H (2*N) (by omega) k.val hk1 (by have := k.isLt; omega) chi js ps
    (words_spec _ _ _ hjs).1 hwin hpowers
  have hprime : primeOnly ps := fun p hm => (hps.2 p hm).1
  rw [roughWord_one_on_prime_word _ hprime (fun p hm => hz.trans_le (hpowers p hm).1)]
  simp

end
end ImbalancedChen.Part5OriginalH430ClassicalRoughFloor

