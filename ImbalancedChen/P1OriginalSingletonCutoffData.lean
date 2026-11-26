import ImbalancedChen.P5OriginalPrimeChartHBWitnesses

/-!
The existing active-psi scale lemma and the six repaired uniform-cutoff
supplier declarations, with original namespaces and statements preserved.
Four Lean API adaptations repair their existing proof expressions.
The two later grouped/selected-W interfaces remain in a historical postimage.
This source adoption adds no cutoff argument or arithmetic estimate.
-/

namespace ImbalancedChen.P5Z.OriginalIndependentFourPrimeChartCutoff
noncomputable section
open Classical Filter
open scoped BigOperators
open ActualLabelledPrimeSmoothCharts ExactOriginalSmoothDyadicPartition
open OriginalChartRoughCutoff

local notation "R" => ExactOriginalSmoothDyadicPartition.R

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
  rw [List.forall₂_map_right_iff] at hwin
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


end
end ImbalancedChen.P5Z.OriginalIndependentFourPrimeChartCutoff

namespace ImbalancedChen.P5Z.IndependentTestPrimeChartUniformCutoff
noncomputable section
open Classical Filter
open scoped BigOperators
open ExactOriginalSmoothDyadicPartition OriginalChartRoughCutoff
open OriginalIndependentFourPrimeChartCutoff

local notation "R" => ExactOriginalSmoothDyadicPartition.R

private theorem scales_prod_upper (N : ℕ) (js : List ℕ)
    (h : ∀ j ∈ js, R j ≤ 2 * (N : ℝ)) :
    (scales js).prod ≤ (2 * (N : ℝ)) ^ js.length := by
  induction js with
  | nil => simp [scales]
  | cons j js ih =>
      have ht : ∀ a ∈ js, R a ≤ 2 * (N : ℝ) :=
        fun a ha => h a (List.mem_cons_of_mem j ha)
      have hprod : 0 ≤ (scales js).prod := by
        exact (List.prod_pos (fun a ha => by
          obtain ⟨a0,_,rfl⟩ := List.mem_map.mp ha
          exact R_pos a0)).le
      calc
        (scales (j :: js)).prod = R j * (scales js).prod := by simp [scales]
        _ ≤ (2 * (N : ℝ)) * (2 * (N : ℝ)) ^ js.length :=
          mul_le_mul (h j (by simp)) (ih ht) hprod (by positivity)
        _ = (2 * (N : ℝ)) ^ (j :: js).length := by
          simp [pow_succ]; ring

private theorem scales_prod_lower (N : ℕ) (astar : ℝ) (js : List ℕ)
    (h : ∀ j ∈ js, (N : ℝ) ^ astar / 2 ≤ R j) :
    ((N : ℝ) ^ astar / 2) ^ js.length ≤ (scales js).prod := by
  induction js with
  | nil => simp [scales]
  | cons j js ih =>
      have ht : ∀ a ∈ js, (N : ℝ) ^ astar / 2 ≤ R a :=
        fun a ha => h a (List.mem_cons_of_mem j ha)
      have hA : 0 ≤ (N : ℝ) ^ astar / 2 := by positivity
      calc
        ((N : ℝ) ^ astar / 2) ^ (j :: js).length =
            ((N : ℝ) ^ astar / 2) *
              ((N : ℝ) ^ astar / 2) ^ js.length := by
          simp [pow_succ]; ring
        _ ≤ R j * (scales js).prod :=
          mul_le_mul (h j (by simp)) (ih ht) (pow_nonneg hA _) (R_pos j).le
        _ = (scales (j :: js)).prod := by simp [scales]

/-- All chart ranks in the fixed bank have one polynomial argument cap.
This uses actual same-word psi windows, not just chartBank membership. -/
theorem active_chart_argument_upper
    (K : ℕ) (chi : ℝ → ℝ) {N k : ℕ} {astar : ℝ}
    {js ps : List ℕ} (hN : 1 ≤ N) (hk : k ≤ K)
    (hlen : js.length = k)
    (hwin : List.Forall₂
      (fun j p => psi chi ((p : ℝ) / R j) ≠ 0 ∧
        R j / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R j) js ps)
    (hsource : ∀ p ∈ ps,
      (N : ℝ) ^ astar ≤ (p : ℝ) ∧ (p : ℝ) ≤ N) :
    argument K (scales js) ≤
      (2 : ℝ) ^ (8 * K + 2) * (N : ℝ) ^ K := by
  have hscale := active_psi_scale_each chi hwin hsource
  have hprod := scales_prod_upper N js (fun j hj => (hscale j hj).2)
  rw [hlen] at hprod
  have hlenR : (scales js).length = k := by simp [scales,hlen]
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase : (1 : ℝ) ≤ 4 * N := by nlinarith
  have hpowk : (4 * (N : ℝ)) ^ k ≤ (4 * (N : ℝ)) ^ K :=
    pow_le_pow_right₀ hbase hk
  have hcoeff : 0 ≤ (2 : ℝ) ^ (6 * K + 2) := by positivity
  have hfirst : argument K (scales js) ≤
      (2 : ℝ) ^ (6 * K + 2) * (4 * (N : ℝ)) ^ k := by
    unfold argument
    rw [hlenR]
    have hh := mul_le_mul_of_nonneg_left hprod
      (by positivity : 0 ≤ (2 : ℝ) ^ k)
    have hp : (2 : ℝ) ^ k * (2 * (N : ℝ)) ^ k =
        (4 * (N : ℝ)) ^ k := by
      rw [← mul_pow, show (2 : ℝ) * (2 * N) = 4 * N by ring]
    exact mul_le_mul_of_nonneg_left (hh.trans_eq hp) hcoeff
  calc
    argument K (scales js) ≤
        (2 : ℝ) ^ (6 * K + 2) * (4 * (N : ℝ)) ^ k := hfirst
    _ ≤ (2 : ℝ) ^ (6 * K + 2) * (4 * (N : ℝ)) ^ K :=
      mul_le_mul_of_nonneg_left hpowk hcoeff
    _ = (2 : ℝ) ^ (8 * K + 2) * (N : ℝ) ^ K := by
      have he : 8 * K + 2 = (6 * K + 2) + 2 * K := by omega
      have hfour : (2 : ℝ) ^ (2*K) = (4 : ℝ) ^ K := (pow_mul _ _ _).trans
        (congrArg (fun z : ℝ => z^K) (by norm_num : (2 : ℝ)^2=4))
      have hconstant : (2 : ℝ) ^ (8*K+2) = (2 : ℝ) ^ (6*K+2) * (4 : ℝ)^K := by
        rw [he, pow_add (2 : ℝ) (6*K+2) (2*K), hfour]
      rw [mul_pow,hconstant]
      ring

/-- For nonempty test words, the argument escapes every fixed analytic
subpower threshold as the source prime floor grows. -/
theorem active_chart_argument_lower
    (K : ℕ) (chi : ℝ → ℝ) {N k : ℕ} {astar : ℝ}
    {js ps : List ℕ} (hk : 1 ≤ k) (hlen : js.length = k)
    (hwin : List.Forall₂
      (fun j p => psi chi ((p : ℝ) / R j) ≠ 0 ∧
        R j / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R j) js ps)
    (hsource : ∀ p ∈ ps,
      (N : ℝ) ^ astar ≤ (p : ℝ) ∧ (p : ℝ) ≤ N)
    (hA : 1 ≤ (N : ℝ) ^ astar / 2) :
    (N : ℝ) ^ astar / 2 ≤ argument K (scales js) := by
  have hscale := active_psi_scale_each chi hwin hsource
  have hprod := scales_prod_lower N astar js (fun j hj => (hscale j hj).1)
  let A : ℝ := (N : ℝ) ^ astar / 2
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hAk : A ≤ A ^ k := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hm : 1 ≤ A ^ m := one_le_pow₀ hA
    calc
      A = A * 1 := by ring
      _ ≤ A * A ^ m := mul_le_mul_of_nonneg_left hm hA0
      _ = A ^ (m+1) := by rw [pow_succ]; ring
  have hcoeff : 1 ≤ (2 : ℝ) ^ (6*K+2) * (2 : ℝ) ^ k := by
    have h1 : (1 : ℝ) ≤ 2 ^ (6*K+2) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  calc
    A ≤ A ^ k := hAk
    _ ≤ (2 : ℝ) ^ (6*K+2) * (2 : ℝ) ^ k * A ^ k := by
      have hh := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hA0 k)
      nlinarith [hh]
    _ ≤ argument K (scales js) := by
      unfold argument
      rw [show (scales js).length = k by simp [scales,hlen]]
      have hh : ((2 : ℝ) ^ (6*K+2) * (2 : ℝ) ^ k) * A^k ≤
          ((2 : ℝ) ^ (6*K+2) * (2 : ℝ) ^ k) * (scales js).prod :=
        mul_le_mul_of_nonneg_left (by simpa only [hlen] using hprod) (by positivity)
      simpa only [mul_assoc] using hh

/-- The analytic conversion uses the bank-wide exponent K+1. -/
theorem uniform_chart_cutoff_of_scalar_threshold
    (K N : ℕ) (astar : ℝ) (hastar : 0 < astar)
    (hN : 1 < N) (js : List ℕ)
    (hhigh : argument K (scales js) ≤
      (2 : ℝ) ^ (8*K+2) * (N : ℝ) ^ K)
    (hcap : (2 : ℝ) ^ (8*K+2) ≤ N)
    (hmin : Real.exp (Real.exp 3) ≤ argument K (scales js))
    (hsubpower :
      (argument K (scales js)) ^
        (2 / (Real.log (Real.log (argument K (scales js)))) ^ 3) ≤
      (argument K (scales js)) ^ (astar / (2 * (K + 1)))) :
    beforeHBCutoff K js < (N : ℝ) ^ astar := by
  let a := argument K (scales js)
  have ha0 : 0 < a := (Real.exp_pos _).trans_le hmin
  have ha1 : 1 < a :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 3)).trans_le hmin
  have hlog : Real.exp 3 ≤ Real.log a :=
    (Real.le_log_iff_exp_le ha0).mpr hmin
  have hll : 3 ≤ Real.log (Real.log a) :=
    (Real.le_log_iff_exp_le ((Real.exp_pos 3).trans_le hlog)).mpr hlog
  have hden : 0 < (Real.log (Real.log a)) ^ 3 := by positivity
  have hexp : 1 / (Real.log (Real.log a)) ^ 3 ≤
      2 / (Real.log (Real.log a)) ^ 3 := by
    apply (div_le_div_iff₀ hden hden).mpr
    nlinarith [hden]
  have hrough : roughF a ≤ a ^ (astar / (2 * (K + 1))) := by
    unfold roughF
    exact (Real.rpow_le_rpow_of_exponent_le ha1.le hexp).trans hsubpower
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hargN : a ≤ (N : ℝ) ^ (K+1) := by
    have hh := mul_le_mul_of_nonneg_right hcap
      (by positivity : 0 ≤ (N : ℝ) ^ K)
    calc
      a ≤ (2 : ℝ) ^ (8*K+2) * (N : ℝ) ^ K := hhigh
      _ ≤ (N : ℝ) * (N : ℝ) ^ K := hh
      _ = (N : ℝ) ^ (K+1) := by rw [pow_succ]; ring
  have hdelta : 0 ≤ astar / (2 * (K + 1)) := by positivity
  have hpow : a ^ (astar / (2 * (K + 1))) ≤
      (N : ℝ) ^ (astar / 2) := by
    calc
      a ^ (astar / (2 * (K + 1))) ≤
          ((N : ℝ) ^ (K+1)) ^ (astar / (2 * (K+1))) :=
        Real.rpow_le_rpow ha0.le hargN hdelta
      _ = (N : ℝ) ^ (astar / 2) := by
        rw [← Real.rpow_natCast (N : ℝ) (K+1), ← Real.rpow_mul hN0]
        congr 1
        push_cast
        have hK : (K : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hK] <;> ring
  have hstrict : (N : ℝ) ^ (astar / 2) < (N : ℝ) ^ astar :=
    Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith [hastar])
  exact (hrough.trans hpow).trans_lt hstrict

/-- A single N0 chosen before rank, original chart labels, prime word,
coefficient mark and HB occurrence works for every 1<=k<=K. -/
theorem independent_test_chart_cutoff_eventual
    (K : ℕ) (astar : ℝ) (hastar : 0 < astar) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K)
        (chi : ℝ → ℝ) (js ps : List ℕ),
        js.length = k →
        List.Forall₂
          (fun j p => psi chi ((p : ℝ) / R j) ≠ 0 ∧
            R j / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R j) js ps →
        (∀ p ∈ ps, (N : ℝ) ^ astar ≤ (p : ℝ) ∧ (p : ℝ) ≤ N) →
        beforeHBCutoff K js < (N : ℝ) ^ astar := by
  let delta : ℝ := astar / (2 * (K + 1))
  have hd : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨X0,hX0⟩ := Filter.eventually_atTop.mp
    (OriginalPrimeChartHBWitnesses.eventually_subpower_envelope delta hd)
  let Xmin : ℝ := max (Real.exp (Real.exp 3)) X0
  have hX1 : 1 < Xmin :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 3)).trans_le (le_max_left _ _)
  have he : ∀ᶠ N : ℕ in Filter.atTop,
      1 < N ∧ (2 : ℝ) ^ (8*K+2) ≤ N ∧
        Xmin ≤ (N : ℝ) ^ astar / 2 := by
    have hp := ((tendsto_rpow_atTop hastar).comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (2 * Xmin))
    filter_upwards [eventually_ge_atTop
      (max 2 (Nat.ceil ((2 : ℝ) ^ (8*K+2)))),hp] with N hN hpow
    change 2 * Xmin ≤ (N : ℝ) ^ astar at hpow
    have hcap : (2 : ℝ) ^ (8*K+2) ≤ N := by
      exact (Nat.le_ceil _).trans
        (by exact_mod_cast (le_max_right _ _ |>.trans hN))
    exact ⟨by omega,hcap,by linarith⟩
  obtain ⟨N0,hN0⟩ := Filter.eventually_atTop.mp he
  refine ⟨N0,?_⟩
  intro N hN k hk1 hkK chi js ps hlen hwin hsource
  obtain ⟨hN1,hcap,hfloor⟩ := hN0 N hN
  have hhigh := active_chart_argument_upper K chi hN1.le hkK hlen hwin hsource
  have hA : 1 ≤ (N : ℝ) ^ astar / 2 := hX1.le.trans hfloor
  have hlow := active_chart_argument_lower K chi hk1 hlen hwin hsource hA
  have hmin : Real.exp (Real.exp 3) ≤ argument K (scales js) :=
    (le_max_left _ _).trans (hfloor.trans hlow)
  have hsub := (hX0 _ ((le_max_right _ _).trans (hfloor.trans hlow))).2
  exact uniform_chart_cutoff_of_scalar_threshold K N astar hastar hN1 js
    hhigh hcap hmin hsub


end
end ImbalancedChen.P5Z.IndependentTestPrimeChartUniformCutoff
