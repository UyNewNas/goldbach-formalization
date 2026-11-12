import ImbalancedChen.P5OriginalPrimeChartHBWitnesses

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original active ψ profile pins every R_j to its independent PP TEST
prime slot u_i. The modulus mark t is separate: q=fullPrefix(t)*r, while
the labelled PP kernel sums u over its own carrier. This source proves a
four-slot scalar cutoff lemma only under explicit support for u. It is
not a claim that u=slots t, nor a complete all-rank PP chart bridge.
-/
namespace ImbalancedChen.P5Z.OriginalIndependentFourPrimeChartCutoff
noncomputable section
open Classical Filter
open scoped BigOperators
open ActualLabelledPrimeSmoothCharts ExactOriginalSmoothDyadicPartition
open OriginalChartRoughCutoff
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap

/-- Actual nonzero ψ, together with the physical slot floor and cap,
bounds every active R_j on the same ordered chart word. -/
theorem active_psi_scale_each (chi : ℝ → ℝ) {astar : ℝ}
    {N : ℕ} {js ps : List ℕ}
    (hwin : List.Forall₂
      (fun j p => psi chi ((p : ℝ) / R j) ≠ 0 ∧
        R j / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R j) js ps)
    (hsource : ∀ p ∈ ps,
      (N : ℝ) ^ astar ≤ (p : ℝ) ∧ (p : ℝ) ≤ N) :
    ∀ j ∈ js,
      (N : ℝ) ^ astar / 2 ≤ R j ∧ R j ≤ 2 * N := by
  induction hwin with
  | nil =>
      intro j hj
      simp at hj
  | @cons j p js ps hj htail ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · have hp := hsource p (by simp)
        constructor <;> linarith [hj.2.1,hj.2.2,hp.1,hp.2]
      · exact ih (fun q hq => hsource q (List.mem_cons_of_mem p hq)) a ha

private theorem scale_product_upper (N : ℕ) (js : List ℕ)
    (hscale : ∀ j ∈ js, R j ≤ 2 * (N : ℝ)) :
    (scales js).prod ≤ (2 * (N : ℝ)) ^ js.length := by
  induction js with
  | nil => simp [scales]
  | cons j js ih =>
      have htail : ∀ a ∈ js, R a ≤ 2 * (N : ℝ) :=
        fun a ha => hscale a (List.mem_cons_of_mem j ha)
      have hprod : 0 ≤ (scales js).prod := by
        exact (List.prod_pos (fun a ha => by
          obtain ⟨q,_,rfl⟩ := List.mem_map.mp ha
          exact R_pos q)).le
      have hB : 0 ≤ 2 * (N : ℝ) := by positivity
      calc
        (scales (j :: js)).prod = R j * (scales js).prod := by
          simp [scales]
        _ ≤ (2 * (N : ℝ)) * (2 * (N : ℝ)) ^ js.length :=
          mul_le_mul (hscale j (by simp)) (ih htail) hprod hB
        _ = (2 * (N : ℝ)) ^ (j :: js).length := by
          simp [pow_succ]; ring

private theorem scale_product_lower (N : ℕ) (js : List ℕ) {astar : ℝ}
    (hscale : ∀ j ∈ js,
      (N : ℝ) ^ astar / 2 ≤ R j) :
    ((N : ℝ) ^ astar / 2) ^ js.length ≤ (scales js).prod := by
  induction js with
  | nil => simp [scales]
  | cons j js ih =>
      have htail : ∀ a ∈ js,
          (N : ℝ) ^ astar / 2 ≤ R a :=
        fun a ha => hscale a (List.mem_cons_of_mem j ha)
      have hA : 0 ≤ (N : ℝ) ^ astar / 2 := by positivity
      have hpow : 0 ≤ ((N : ℝ) ^ astar / 2) ^ js.length :=
        pow_nonneg hA _
      calc
        ((N : ℝ) ^ astar / 2) ^ (j :: js).length =
            ((N : ℝ) ^ astar / 2) *
              ((N : ℝ) ^ astar / 2) ^ js.length := by
          simp [pow_succ]; ring
        _ ≤ R j * (scales js).prod :=
          mul_le_mul (hscale j (by simp)) (ih htail) hpow (R_pos j).le
        _ = (scales (j :: js)).prod := by simp [scales]

/-- A four-slot independent test chart gives a uniform polynomial
argument ceiling, with K chosen before its labels and test tuple. -/
theorem active_four_chart_argument_upper (chi : ℝ → ℝ)
    {N K : ℕ} {astar : ℝ} {js ps : List ℕ}
    (hlen : js.length = 4)
    (hwin : List.Forall₂
      (fun j p => psi chi ((p : ℝ) / R j) ≠ 0 ∧
        R j / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R j) js ps)
    (hsource : ∀ p ∈ ps,
      (N : ℝ) ^ astar ≤ (p : ℝ) ∧ (p : ℝ) ≤ N) :
    argument K (scales js) ≤
      (2 : ℝ) ^ (6 * K + 10) * (N : ℝ) ^ 4 := by
  have hscale := active_psi_scale_each chi hwin hsource
  have hprod := scale_product_upper N js (fun j hj => (hscale j hj).2)
  have hlenR : (scales js).length = 4 := by simp [scales,hlen]
  rw [hlen] at hprod
  have hcoeff : 0 ≤ (2 : ℝ) ^ (6 * K + 2) * (2 : ℝ) ^ 4 := by positivity
  have hh := mul_le_mul_of_nonneg_left hprod hcoeff
  rw [mul_pow] at hh
  have hexp : 6 * K + 10 = (6 * K + 2) + 4 + 4 := by omega
  have hfactor : (2 : ℝ) ^ (6 * K + 10) =
      (2 : ℝ) ^ (6 * K + 2) * (2 : ℝ) ^ 4 * (2 : ℝ) ^ 4 := by
    rw [hexp, pow_add (2 : ℝ) ((6 * K + 2) + 4) 4, pow_add (2 : ℝ) (6 * K + 2) 4]
  unfold argument
  rw [hlenR, hfactor]
  simpa only [mul_assoc] using hh

/-- The matching lower bound forces the original chart argument to
escape every fixed subpower-envelope threshold on active marks. -/
theorem active_four_chart_argument_lower (chi : ℝ → ℝ)
    {N K : ℕ} {astar : ℝ} {js ps : List ℕ}
    (hlen : js.length = 4)
    (hwin : List.Forall₂
      (fun j p => psi chi ((p : ℝ) / R j) ≠ 0 ∧
        R j / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R j) js ps)
    (hsource : ∀ p ∈ ps,
      (N : ℝ) ^ astar ≤ (p : ℝ) ∧ (p : ℝ) ≤ N) :
    (2 : ℝ) ^ (6 * K + 2) * (2 : ℝ) ^ 4 *
      ((N : ℝ) ^ astar / 2) ^ 4 ≤
      argument K (scales js) := by
  have hscale := active_psi_scale_each chi hwin hsource
  have hprod := scale_product_lower N js (fun j hj => (hscale j hj).1)
  have hlenR : (scales js).length = 4 := by simp [scales,hlen]
  rw [hlen] at hprod
  have hh := mul_le_mul_of_nonneg_left hprod
    (by positivity : 0 ≤ (2 : ℝ) ^ (6 * K + 2) * (2 : ℝ) ^ 4)
  unfold argument
  rw [hlenR]
  simpa only [mul_assoc] using hh

/-- The remaining analytic comparison is elementary once the genuine
four-prime chart argument is between its proved polynomial bounds. -/
theorem cutoff_lt_source_floor_of_scalar_threshold
    {N K : ℕ} {astar : ℝ} {js : List ℕ} (hastar : 0 < astar)
    (hN : 1 < N)
    (hhigh : argument K (scales js) ≤
      (2 : ℝ) ^ (6 * K + 10) * (N : ℝ) ^ 4)
    (hcap : (2 : ℝ) ^ (6 * K + 10) ≤ N)
    (hmin : Real.exp (Real.exp 3) ≤ argument K (scales js))
    (hsubpower :
      (argument K (scales js)) ^
        (2 / (Real.log (Real.log (argument K (scales js)))) ^ 3) ≤
      (argument K (scales js)) ^ (astar / 10)) :
    beforeHBCutoff K js < (N : ℝ) ^ astar := by
  let a := argument K (scales js)
  have ha0 : 0 < a := (Real.exp_pos _).trans_le hmin
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (Real.exp_pos 3)).trans_le hmin
  have hlog : Real.exp 3 ≤ Real.log a :=
    (Real.le_log_iff_exp_le ha0).mpr hmin
  have hll : 3 ≤ Real.log (Real.log a) :=
    (Real.le_log_iff_exp_le (Real.exp_pos 3 |>.trans_le hlog)).mpr hlog
  have hden : 0 < (Real.log (Real.log a)) ^ 3 := by positivity
  have hexp : 1 / (Real.log (Real.log a)) ^ 3 ≤
      2 / (Real.log (Real.log a)) ^ 3 := by
    apply (div_le_div_iff₀ hden hden).mpr
    nlinarith [hden]
  have hrough : roughF a ≤ a ^ (astar / 10) := by
    unfold roughF
    exact (Real.rpow_le_rpow_of_exponent_le ha1.le hexp).trans hsubpower
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hpow4 : 0 ≤ (N : ℝ) ^ 4 := by positivity
  have hargN : a ≤ (N : ℝ) ^ 5 := by
    have hh := mul_le_mul_of_nonneg_right hcap hpow4
    calc
      a ≤ (2 : ℝ) ^ (6 * K + 10) * (N : ℝ) ^ 4 := hhigh
      _ ≤ (N : ℝ) * (N : ℝ) ^ 4 := hh
      _ = (N : ℝ) ^ 5 := by ring
  have hdelta : 0 ≤ astar / 10 := by linarith [hastar]
  have hpow : a ^ (astar / 10) ≤
      (N : ℝ) ^ (astar / 2) := by
    calc
      a ^ (astar / 10) ≤
          ((N : ℝ) ^ 5) ^ (astar / 10) :=
        Real.rpow_le_rpow ha0.le hargN hdelta
      _ = (N : ℝ) ^ (astar / 2) := by
        rw [← Real.rpow_natCast (N : ℝ) 5, ← Real.rpow_mul hN0]
        congr 1
        norm_num <;> ring
  have hstrict : (N : ℝ) ^ (astar / 2) <
      (N : ℝ) ^ astar :=
    Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith [hastar])
  exact hrough.trans_le hpow |>.trans_lt hstrict

/-- For fixed four-slot rank, one N threshold precedes every chart
label and independent test tuple satisfying the stated support. This
does not identify an actual PP geometric W_N or cover all ranks. -/
theorem active_four_chart_cutoff_eventual (K : ℕ) (astar : ℝ)
    (hastar : 0 < astar) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ (chi : ℝ → ℝ) (js ps : List ℕ),
        js.length = 4 →
        List.Forall₂
          (fun j p => psi chi ((p : ℝ) / R j) ≠ 0 ∧
            R j / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R j) js ps →
        (∀ p ∈ ps,
          (N : ℝ) ^ astar ≤ (p : ℝ) ∧ (p : ℝ) ≤ N) →
        beforeHBCutoff K js < (N : ℝ) ^ astar := by
  let delta : ℝ := astar / 10
  have hd : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨X0,hX0⟩ := Filter.eventually_atTop.mp
    (OriginalPrimeChartHBWitnesses.eventually_subpower_envelope delta hd)
  let Xmin : ℝ := max (Real.exp (Real.exp 3)) X0
  have hXpos : 1 < Xmin :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 3)).trans_le (le_max_left _ _)
  have he : ∀ᶠ N : ℕ in Filter.atTop,
      1 < N ∧ (2 : ℝ) ^ (6 * K + 10) ≤ N ∧
        Xmin ≤ (N : ℝ) ^ astar / 2 := by
    have hp := ((tendsto_rpow_atTop (by linarith [hastar] :
      (0 : ℝ) < astar)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 * Xmin))
    filter_upwards [eventually_ge_atTop (max 2 (Nat.ceil ((2 : ℝ) ^ (6*K+10)))),hp]
      with N hN hpow
    have hcap : (2 : ℝ) ^ (6*K+10) ≤ N := by
      exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _ |>.trans hN))
    exact ⟨by omega,hcap,by linarith⟩
  obtain ⟨N0,hN0⟩ := Filter.eventually_atTop.mp he
  refine ⟨N0,?_⟩
  intro N hN chi js ps hlen hwin hsource
  obtain ⟨hN1,hcap,hfloor⟩ := hN0 N hN
  have hhigh := active_four_chart_argument_upper chi hlen hwin hsource
  have hlow := active_four_chart_argument_lower chi hlen hwin hsource
  let A : ℝ := (N : ℝ) ^ astar / 2
  have hA1 : 1 ≤ A := hXpos.le.trans hfloor
  have hA0 : 0 ≤ A := by linarith
  have hA4 : A ≤ A ^ 4 := by
    have hA3 : 1 ≤ A ^ 3 := one_le_pow₀ hA1
    calc
      A = A * 1 := by ring
      _ ≤ A * A ^ 3 := mul_le_mul_of_nonneg_left hA3 hA0
      _ = A ^ 4 := by ring
  have hcoeff : 1 ≤ (2 : ℝ) ^ (6*K+2) * (2 : ℝ) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 2 ^ (6*K+2) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ 2 ^ (4 : ℕ) := by norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  have hargmin : Xmin ≤ argument K (scales js) := by
    calc
      Xmin ≤ A := hfloor
      _ ≤ A ^ 4 := hA4
      _ ≤ (2 : ℝ) ^ (6*K+2) * (2 : ℝ) ^ 4 * A ^ 4 := by
        have hh := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hA0 4)
        nlinarith [hh]
      _ ≤ argument K (scales js) := hlow
  have hsub := (hX0 _ ((le_max_right _ _).trans hargmin)).2
  exact cutoff_lt_source_floor_of_scalar_threshold hastar hN1 hhigh hcap
    ((le_max_left _ _).trans hargmin) hsub

end
end ImbalancedChen.P5Z.OriginalIndependentFourPrimeChartCutoff


