import ImbalancedChen.P1OriginalFourthSmallRemainderBound
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Uniform original-coarse fourth small-prime remainder

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The original Fin4 carrier, target deletion, common PLUS cutoff and original
old/new levels are retained. The parameter L is chosen here, rather than
left as a budget premise: L = 3 log log N. This gives an eventual O(a)
bound uniform in the enumeration cap. In particular its even-target limsup
vanishes as a decreases to zero. The initial d=1, empty-history tree is
unchanged; this module only estimates the remainder in its exact dictionary.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open Filter Topology
open P1OriginalCoarseContinuation

namespace P1OriginalFourthUniformSmallRemainder

/-- The actual even-target asymptotic filter. -/
abbrev evenTargets : Filter ℕ :=
  atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}

private theorem evenTargets_neBot : NeBot evenTargets := by
  have hd : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have he : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop
      (Filter.principal {N : ℕ | 0 < N ∧ Even N}) := by
    apply tendsto_principal.2
    exact Eventually.of_forall (fun n => ⟨by omega, ⟨n + 1, by omega⟩⟩)
  exact (tendsto_inf.2 ⟨hd, he⟩).neBot

/-- Pure scalar budgets for the explicit moving parameter. There are no
prime-distribution or signed-remainder hypotheses in this statement. -/
theorem eventually_moving_budgets (C omega a : ℝ)
    (homega : 0 < omega) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop,
      let L := 3 * Real.log (Real.log (N : ℝ))
      2 ≤ N ∧ 2 ≤ L ∧ L ^ 13 ≤ omega * Real.log (N : ℝ) ∧
        Real.exp 1 ≤ omega * Real.log (N : ℝ) ∧
        Real.log (2 : ℝ) * Real.log (3 : ℝ) ≤
          a * Real.log (N : ℝ) * (Real.log (3 : ℝ) - Real.log (2 : ℝ)) ∧
        ((C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) *
          (Real.log (N : ℝ) / Real.log 3) ≤ 1 ∧
        1 / Real.log (N : ℝ) ≤ a := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun N : ℕ => 3 * Real.log (Real.log (N : ℝ)))
      atTop atTop := (Real.tendsto_log_atTop.comp hlog).const_mul_atTop (by norm_num)
  have hp : Tendsto (fun x : ℝ => (3 * Real.log x) ^ 13 / x)
      atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => (Real.log x) ^ 13 / x)
        atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 13 one_ne_zero
    convert h.const_mul ((3 : ℝ) ^ 13) using 1 <;> simp only [mul_zero]
    funext x
    ring
  have hpower := (hp.comp hlog).eventually (gt_mem_nhds homega)
  have hexp : Tendsto (fun N : ℕ =>
      (C / (Real.log 4 * Real.log 3)) / Real.log (N : ℝ)) atTop (𝓝 0) :=
    hlog.const_div_atTop _
  have hgap : 0 < Real.log (3 : ℝ) - Real.log (2 : ℝ) := by
    exact sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))
  have hscale : Tendsto (fun N : ℕ => a * Real.log (N : ℝ) *
      (Real.log (3 : ℝ) - Real.log (2 : ℝ))) atTop atTop :=
    (hlog.const_mul_atTop (mul_pos ha hgap)).congr (fun N => by ring)
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hL.eventually (eventually_ge_atTop 2), hpower,
    (hlog.const_mul_atTop homega).eventually (eventually_ge_atTop (Real.exp 1)),
    hscale.eventually (eventually_ge_atTop (Real.log (2 : ℝ) * Real.log (3 : ℝ))),
    hexp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (hlog.const_div_atTop (1 : ℝ)).eventually (gt_mem_nhds ha)]
    with N hN hLN hpN heN hsN hxN hiN
  have hx : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have heq :
      ((C / Real.log 4) * Real.log (N : ℝ) *
        Real.exp (-(3 * Real.log (Real.log (N : ℝ))))) *
          (Real.log (N : ℝ) / Real.log 3) =
        (C / (Real.log 4 * Real.log 3)) / Real.log (N : ℝ) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx]
    field_simp [hx.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne',
      (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne']
    <;> ring
  refine ⟨hN, hLN, ?_, heN, hsN, ?_, hiN.le⟩
  · exact ((div_lt_iff₀ hx).mp hpN).le
  · rw [heq]
    exact hxN.le

/-- A fixed positive prefix interval has an eventual bound independent of
the small terminal cutoff and the enumeration cap. -/
private theorem eventually_prefix_cube_le (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 ≤
        (|Real.log ((19 / 96 : ℝ) / omega)| + 1) ^ 3 := by
  have h := (tendsto_actualPrimeReciprocalMass homega homegaRho).eventually
    (gt_mem_nhds (show Real.log ((19 / 96 : ℝ) / omega) <
      |Real.log ((19 / 96 : ℝ) / omega)| + 1 by
        linarith [le_abs_self (Real.log ((19 / 96 : ℝ) / omega))]))
  filter_upwards [h] with N hN
  have hM : 0 ≤ actualPrimeReciprocalMass N omega (19 / 96 : ℝ) := by
    unfold actualPrimeReciprocalMass
    apply Finset.sum_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
    positivity
  exact pow_le_pow_left₀ hM hN.le 3

/-- A genuine O(a) estimate for the literal signed original smallRemainder.
The constant precedes a, N, and cap. Every analytic moving-L budget has
been discharged, and no desired mean or tail bound is an input. -/
theorem exists_eventually_original_smallRemainder_abs_le_linear
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    ∃ D : ℝ, 0 < D ∧ ∀ a : ℝ, 0 < a → 2 * a ≤ omega →
      ∀ᶠ N : ℕ in atTop, Even N → ∀ cap : ℕ,
        |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N cap| ≤ D * a := by
  obtain ⟨C, K, hC, hK, hsource⟩ :=
    P1OriginalFourthSmallRemainderBound.exists_original_smallRemainder_abs_le
  let B := (|Real.log ((19 / 96 : ℝ) / omega)| + 1) ^ 3
  let A := 2 * C / omega ^ 2 + 1
  let T := 4 + 6 * K * (1 / Real.log 3 + 1)
  let q : ℝ := (selectedFourthCells e chi m omega J4).card
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hT : 0 < T := by
    dsimp [T]
    have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hK0 : 0 < K := by linarith
    positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  refine ⟨(q + 1) * A * B * T, by positivity, ?_⟩
  intro a ha haomega
  filter_upwards [eventually_moving_budgets C omega a homega ha,
    eventually_prefix_cube_le omega homega homegaRho] with N hb hprefix hEven cap
  dsimp only at hb
  obtain ⟨hN, hL, hpower, hlog, hscale, hexp, hinv⟩ := hb
  have hraw := hsource e chi m omega a homega ha haomega J4 cap4 hcheck
    N cap hN hEven (3 * Real.log (Real.log (N : ℝ))) hL hpower hlog hscale hexp
  have hterm : 4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ)) ≤ T * a := by
    dsimp [T]
    have hm := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 6 * K by linarith)
    nlinarith
  have hterm0 : 0 ≤ 4 * a + 6 * K *
      (a / Real.log 3 + 1 / Real.log (N : ℝ)) := by
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hK0 : 0 < K := by linarith
    positivity
  calc
    _ ≤ q * A * (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
        (4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ))) := hraw
    _ ≤ q * A * B * (T * a) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hprefix (mul_nonneg hq hA.le)
      · exact hterm
      · exact hterm0
      · positivity
    _ ≤ ((q + 1) * A * B * T) * a := by
      have hpos : 0 ≤ A * B * T * a := by positivity
      nlinarith

/-- Uniformity is preserved for an arbitrary enumeration-cap function. -/
theorem exists_original_smallRemainder_limsup_le_linear
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    ∃ D : ℝ, 0 < D ∧ ∀ a : ℝ, 0 < a → 2 * a ≤ omega →
      ∀ cap : ℕ → ℕ,
        0 ≤ limsup (fun N : ℕ =>
          |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N)|)
            evenTargets ∧
        limsup (fun N : ℕ =>
          |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N)|)
            evenTargets ≤ D * a := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_eventually_original_smallRemainder_abs_le_linear
      e chi m omega homega homegaRho J4 cap4 hcheck
  refine ⟨D, hD, ?_⟩
  intro a ha haomega cap
  letI : NeBot evenTargets := evenTargets_neBot
  have hb : ∀ᶠ N : ℕ in evenTargets,
      |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N)| ≤ D * a := by
    filter_upwards [(hbound a ha haomega).filter_mono inf_le_left,
      (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
        (Filter.eventually_mem_principal _).filter_mono inf_le_right)] with N hn he
    exact hn he.2 (cap N)
  have hnonneg : ∀ N : ℕ,
      0 ≤ |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N)| :=
    fun N => abs_nonneg _
  exact ⟨le_limsup_of_frequently_le (Eventually.of_forall hnonneg).frequently
      (isBoundedUnder_of_eventually_le hb),
    limsup_le_of_le (isCoboundedUnder_le_of_le evenTargets hnonneg) hb⟩

/-- The requested order of limits: first the limsup over even N, then
a decreases to zero. The cap function is arbitrary, and δ is uniform in it. -/
theorem original_smallRemainder_limsup_cutoff_zero
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta → ∀ cap : ℕ → ℕ,
        0 ≤ limsup (fun N : ℕ =>
          |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N)|)
            evenTargets ∧
        limsup (fun N : ℕ =>
          |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N)|)
            evenTargets < epsilon := by
  obtain ⟨D, hD, hbound⟩ := exists_original_smallRemainder_limsup_le_linear
    e chi m omega homega homegaRho J4 cap4 hcheck
  intro epsilon hepsilon
  refine ⟨min (omega / 2) (epsilon / D), lt_min (by positivity) (by positivity), ?_⟩
  intro a ha hadelta cap
  have haomega : 2 * a ≤ omega := by
    have := lt_of_lt_of_le hadelta (min_le_left _ _)
    linarith
  have hsmall : D * a < epsilon := by
    have h := lt_of_lt_of_le hadelta (min_le_right _ _)
    have := (lt_div_iff₀ hD).mp h
    nlinarith
  exact ⟨(hbound a ha haomega cap).1,
    (hbound a ha haomega cap).2.trans_lt hsmall⟩

/-- Filter form of the original iterated small-cutoff limit. -/
theorem tendsto_original_smallRemainder_limsup_cutoff_zero
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) (cap : ℕ → ℕ) :
    Tendsto (fun a : ℝ => limsup (fun N : ℕ =>
      |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N)|)
        evenTargets) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
  apply Metric.tendsto_nhdsWithin_nhds.2
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hbound⟩ := original_smallRemainder_limsup_cutoff_zero
    e chi m omega homega homegaRho J4 cap4 hcheck epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro a ha hadist
  have ha0 : 0 < a := ha
  have haDelta : a < delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ha0] using hadist
  obtain ⟨hlo, hhi⟩ := hbound a ha0 haDelta cap
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hlo] using hhi

end P1OriginalFourthUniformSmallRemainder
end
end ImbalancedChen
