import ImbalancedChen.P4AOriginalThirdFallbackPaidDensity
import ImbalancedChen.OrdinaryRosserFirstExitPolicy
import ImbalancedChen.ActualRosserUpperGeneralLimit

/-! The first stop of the original historical policy on its own Ico mesh.
Its ordinary plus density uses the literal floor cutoff and the old
exponent Theta−2e on the same ambient cap N. -/
namespace ImbalancedChen.P4AOriginalHistoricalFirstStop
noncomputable section
open Set Filter Topology
open scoped BigOperators Classical
open HistoricalThirdCoarse
open VariableEnvelope (extendedFirstStop extendedDistributionCap)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P5OriginalCommonPositivePresieve (normalize)
open MathlibNt.SieveTheory

abbrev step (m : ℕ) := logPrimeMeshStep 0 thirdPrefixRho m
def stop (e : ℝ) (m : ℕ) : ℝ := step m * (⌊(thirdPrefixRho - 4*e)/step m⌋₊ : ℝ)

theorem step_pos (m : ℕ) : 0 < step m := logPrimeMeshStep_pos (by norm_num [thirdPrefixRho]) m

theorem stop_bounds {e : ℝ} (he : 0 < e) (hsmall : e ≤ 1/384) (m : ℕ) :
    0 ≤ stop e m ∧ stop e m ≤ thirdPrefixRho-4*e ∧
      thirdPrefixRho-4*e-step m < stop e m ∧ stop e m < thirdPrefixRho := by
  have hd := step_pos m
  have hw : 0 ≤ thirdPrefixRho-4*e := by dsimp [thirdPrefixRho]; linarith
  have h₁ := (le_div_iff₀ hd).mp (Nat.floor_le (div_nonneg hw hd.le))
  have h₂ := (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one ((thirdPrefixRho-4*e)/step m))
  unfold stop
  refine ⟨mul_nonneg hd.le (Nat.cast_nonneg _),?_,?_,?_⟩ <;> nlinarith only [h₁,h₂,he]

theorem firstStop_log {e : ℝ} (he : 0 < e) (hsmall : e ≤ 1/384) (m : ℕ)
    (N : ℝ) (history : List ℕ) (hx : 0 ≤ primeHistoryLogCoordinates N 1 history 0) :
    firstStop e m N history ↔ primeHistoryLogCoordinates N 1 history 0 < stop e m := by
  let x := primeHistoryLogCoordinates N 1 history 0
  let d := step m
  let k := ⌊(thirdPrefixRho-4*e)/d⌋₊
  have hd : 0 < d := step_pos m
  have hw : 0 ≤ thirdPrefixRho-4*e := by dsimp [thirdPrefixRho]; linarith
  have hfull : ((m+1:ℕ):ℝ)*d = thirdPrefixRho := by
    simpa only [logPrimeMeshPoint,zero_add] using logPrimeMeshPoint_last 0 thirdPrefixRho m
  have hk : k < m+1 := (Nat.floor_lt (div_nonneg hw hd.le)).mpr
    ((div_lt_iff₀ hd).mpr (by rw [hfull]; linarith))
  change (∃ i : Fin (m+1), 0+(i.val:ℝ)*d ≤ x ∧ x < 0+((i.val+1:ℕ):ℝ)*d ∧
    0+((i.val+1:ℕ):ℝ)*d ≤ thirdPrefixRho-4*e) ↔ x < d*(k:ℝ)
  simp only [zero_add]
  constructor
  · rintro ⟨i,_,hi,hw'⟩
    have hik : i.val+1 ≤ k := (Nat.le_floor_iff (div_nonneg hw hd.le)).mpr ((le_div_iff₀ hd).mpr hw')
    exact hi.trans_le (by simpa only [mul_comm d] using
      mul_le_mul_of_nonneg_right (show ((i.val+1:ℕ):ℝ) ≤ k by exact_mod_cast hik) hd.le)
  · intro hh
    let j := ⌊x/d⌋₊
    have hj : j<k := (Nat.floor_lt (div_nonneg hx hd.le)).mpr
      ((div_lt_iff₀ hd).mpr (by simpa only [mul_comm] using hh))
    refine ⟨⟨j,hj.trans hk⟩,(le_div_iff₀ hd).mp (Nat.floor_le (div_nonneg hx hd.le)),?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one] using (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one (x/d))
    · apply (le_div_iff₀ hd).mp
      exact (show ((j+1:ℕ):ℝ) ≤ k by exact_mod_cast (show j+1≤k by omega)).trans (Nat.floor_le (div_nonneg hw hd.le))

theorem firstStop_prime {e : ℝ} (he : 0<e) (hsmall : e ≤ 1/384) {N : ℕ} (hN : 1<N)
    (m p : ℕ) (hp : 0<p) : firstStop e m (N:ℝ) [p] ↔ (p:ℝ)<(N:ℝ)^stop e m := by
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hx : 0 ≤ primeHistoryLogCoordinates (N:ℝ) 1 [p] 0 := by
    simpa [primeHistoryLogCoordinates,primeHistoryTuple] using
      div_nonneg (Real.log_nonneg (show (1:ℝ)≤p by exact_mod_cast hp)) (Real.log_pos hNr).le
  have hpow : (N:ℝ)^primeHistoryLogCoordinates (N:ℝ) 1 [p] 0=(p:ℝ) := by
    simpa [primeHistoryLogCoordinates,primeHistoryTuple,actualPrimeTupleLog] using
      actualPrimeTupleLog_rpow hN (fun _ : Fin 1 => p) (fun _ => hp) 0
  rw [firstStop_log he hsmall m (N:ℝ) [p] hx,← Real.rpow_lt_rpow_left_iff hNr,hpow]

private theorem initial_next_eq_ordinary (e : ℝ) (m N : ℕ)
    (positive : Bool) (q : ℕ) (history : List ℕ) (hne : history ≠ []) :
    initialPolicy e m (N : ℝ) positive (q :: history) =
      ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))
        positive (q :: history) := by
  simp [initialPolicy, ordinaryParityRosserPolicy,
    oddFirstExitPolicy,initial,VariableEnvelope.extendedDistributionCap,thirdPrefixTheta,hne]

theorem initial_nonempty_continuation (e : ℝ) (m N : ℕ)
    (weight : ℕ → ℝ) (remaining history : List ℕ) (positive : Bool) (mass : ℝ)
    (hne : history ≠ []) :
    firstExitRetainedPolynomial (initialPolicy e m (N : ℝ))
        weight history positive mass remaining =
      firstExitRetainedPolynomial
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)))
        weight history positive mass remaining := by
  induction remaining generalizing history positive mass with
  | nil => rfl
  | cons q qs ih =>
      simp only [firstExitRetainedPolynomial,
        initial_next_eq_ordinary e m N (!positive) q history hne]
      rw [ih history positive mass hne]
      by_cases hq : ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))
          (!positive) (q :: history) = true
      · rw [if_pos hq, if_pos hq, ih (q :: history) (!positive) (mass * weight q) (by simp)]
      · rw [if_neg hq, if_neg hq]

private theorem initial_root_on_low (e : ℝ) (m N : ℕ) (weight : ℕ → ℝ)
    (carrier : List ℕ)
    (hstop : ∀ p ∈ carrier, firstStop e m (N : ℝ) [p]) :
    firstExitRetainedPolynomial (initialPolicy e m (N : ℝ))
        weight [] true 1 carrier =
      firstExitRetainedPolynomial
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)))
        weight [] true 1 carrier := by
  revert hstop
  induction carrier with
  | nil => intro _; rfl
  | cons p ps ih =>
      intro hstop
      have hp := hstop p (by simp)
      have hps := fun q hq => hstop q (List.mem_cons_of_mem p hq)
      have htest : initialPolicy e m (N : ℝ) false [p] =
          ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)) false [p] := by
        simp [initialPolicy, ordinaryParityRosserPolicy,
          oddFirstExitPolicy,initial,VariableEnvelope.extendedDistributionCap,thirdPrefixTheta,hp]
      simp only [firstExitRetainedPolynomial, Bool.not_true, htest]
      rw [ih hps]
      by_cases ht : ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))
          false [p] = true
      · rw [if_pos ht, if_pos ht,
          initial_nonempty_continuation e m N weight ps [p] false (1 * weight p) (by simp)]
      · rw [if_neg ht, if_neg ht]

private theorem initial_root_skip_high (e : ℝ) (m N : ℕ) (weight : ℕ → ℝ)
    (high low : List ℕ)
    (hfail : ∀ p ∈ high, initialPolicy e m (N : ℝ) false [p] = false) :
    firstExitRetainedPolynomial (initialPolicy e m (N : ℝ))
        weight [] true 1 (high ++ low) =
      firstExitRetainedPolynomial (initialPolicy e m (N : ℝ))
        weight [] true 1 low := by
  revert hfail
  induction high with
  | nil => intro _; rfl
  | cons p ps ih =>
      intro hfail
      have hp := hfail p (by simp)
      simpa only [List.cons_append, firstExitRetainedPolynomial, Bool.not_true, hp,
        Bool.false_eq_true, if_false, add_zero] using
        ih (fun q hq => hfail q (List.mem_cons_of_mem p hq))

/-- The same initial policy has exactly the ordinary plus density at its
original rectangular-grid stop cutoff. The original cap is N and the full polynomial has w=0.
The old level retains both total-product and every inherited cubic test. -/
theorem initial_eq_plus {e : ℝ}
    (he0 : 0 < e) (he : e ≤ 1 / 384) {N : ℕ} (hN : 1 < N) (m : ℕ) :
    firstExitRetainedPolynomial (initialPolicy e m (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N N 0 ((N : ℝ) ^ thirdPrefixRho)) =
      actualSmallRosserPlusDensity N N
        ((N : ℝ) ^ stop e m)
        ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)) := by
  let z := (N : ℝ) ^ stop e m
  let weight := fun p : ℕ => 1 / ((p : ℝ) - 1)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hz : z ≤ (N : ℝ) ^ thirdPrefixRho :=
    Real.rpow_le_rpow_of_exponent_le hNr.le
      (stop_bounds he0 he m).2.2.2.le
  have hfail : ∀ p ∈ roughPrimeUniverse N N z ((N : ℝ) ^ thirdPrefixRho),
      initialPolicy e m (N : ℝ) false [p] = false := by
    intro p hp
    have hn : ¬firstStop e m (N : ℝ) [p] := by
      intro hs
      exact (not_lt_of_ge (mem_roughPrimeUniverse_lower hp))
        ((firstStop_prime he0 he hN m p
          (mem_roughPrimeUniverse_prime hp).pos).mp hs)
    simp [initialPolicy, oddFirstExitPolicy, hn]
  have hstop : ∀ p ∈ roughPrimeUniverse N N 0 z,
      firstStop e m (N : ℝ) [p] := by
    intro p hp
    exact (firstStop_prime he0 he hN m p
      (mem_roughPrimeUniverse_prime hp).pos).mpr (mem_roughPrimeUniverse_upper hp)
  rw [roughPrimeUniverse_split N N z ((N : ℝ) ^ thirdPrefixRho) hz,
    initial_root_skip_high e m N weight _ _ hfail,
    initial_root_on_low e m N weight _ hstop]
  simpa only [Bool.false_eq_true,if_false] using firstExitRetainedPolynomial_ordinaryParityRosser_eq_actualDensity
    false N N z ((N:ℝ)^(thirdPrefixTheta-2*e))
      (Real.one_lt_rpow hNr (by norm_num [thirdPrefixTheta] at *; linarith)) (by simp)

def factor (x : ℝ × ℝ) : ℝ := (2*Real.exp (-Real.eulerMascheroniConstant)/x.2) *
  suzukiContinuousUpperFactor (x.1/x.2)

theorem factor_continuous : ContinuousAt factor (thirdPrefixTheta,thirdPrefixRho) := by
  have hn : thirdPrefixRho ≠ 0 := by norm_num [thirdPrefixRho]
  have hr : 1 < thirdPrefixTheta/thirdPrefixRho := by norm_num [thirdPrefixTheta,thirdPrefixRho]
  exact (continuousAt_const.div continuousAt_snd hn).mul
    ((continuousOn_suzukiContinuousUpperFactor.continuousAt (Ioi_mem_nhds hr)).comp
      (continuousAt_fst.div continuousAt_snd hn))

theorem initial_approx (eta : ℝ) (heta : 0<eta) :
    ∃ E : ℝ, 0<E ∧ ∀ e : ℝ, 0<e → e<E → ∀ m : ℕ, step m≤e →
      ∀ᶠ N : ℕ in atTop, Even N →
        normalize N (rawRoot (initialPolicy e m (N:ℝ)) N) < P4ASameRhoCompact.originalOrdinaryRoot+eta := by
  obtain ⟨eps,heps,hf⟩ := Metric.continuousAt_iff.mp factor_continuous (eta/2) (half_pos heta)
  refine ⟨min (1/384) (eps/6),lt_min (by norm_num) (by positivity),?_⟩
  intro e he hE m hstep
  have hs := hE.trans_le (min_le_left _ _)
  obtain ⟨_,hu,hl,hur⟩ := stop_bounds he hs.le m
  have hsmall := hE.trans_le (min_le_right _ _)
  have hpos : 0 < stop e m := by dsimp [thirdPrefixRho] at hl; linarith
  have hprod : dist (thirdPrefixTheta-2*e,stop e m) (thirdPrefixTheta,thirdPrefixRho)<eps := by
    rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,Real.dist_eq]
    constructor <;> apply abs_lt.mpr <;> constructor <;> linarith
  have hclose := (abs_lt.mp (show |factor (thirdPrefixTheta-2*e,stop e m)-
    P4ASameRhoCompact.originalOrdinaryRoot| < eta/2 by simpa only [Real.dist_eq] using hf hprod)).2
  have hratio : 1 < (thirdPrefixTheta-2*e)/stop e m := (lt_div_iff₀ hpos).mpr (by
    dsimp [thirdPrefixRho,thirdPrefixTheta] at hu ⊢; linarith)
  have hh := tendsto_actualSmallRosserPlusDensity_general_normalized (stop e m) hpos _
    hratio id (by
      filter_upwards [(eventually_ge_atTop (2:ℕ)).filter_mono inf_le_left] with N hN
      change (N:ℝ)^stop e m ≤ (N:ℝ)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (show (1:ℝ)≤N by exact_mod_cast (show 1≤N by omega))
        (hur.le.trans (by norm_num [thirdPrefixRho] : thirdPrefixRho≤1)))
  rw [div_mul_cancel₀ _ hpos.ne'] at hh
  have hn := hh.eventually (gt_mem_nhds (by linarith only [hclose,heta] :
    factor (thirdPrefixTheta-2*e,stop e m) < P4ASameRhoCompact.originalOrdinaryRoot+eta))
  rw [Filter.eventually_inf_principal] at hn
  filter_upwards [hn,eventually_ge_atTop (2:ℕ)] with N hN h2
  intro hev
  have heq := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (initialPolicy e m (N:ℝ)) (fun _ => rfl) N N 0 (cutoff N)
  unfold normalize rawRoot
  rw [← heq,initial_eq_plus he hs.le (by omega) m]
  exact hN ⟨by omega,hev⟩

end
end ImbalancedChen.P4AOriginalHistoricalFirstStop
