import ImbalancedChen.P5U7PrimeTwoCutoffLipschitz

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Arbitrary-cutoff prime logarithmic row, bound to the actual clamped row.
The existing evaluated d..(1-t)/2 primitive is reused twice: full row minus
the actual tail. No duplicate antiderivative or fixed-cutoff wrapper.
All log arguments and closed endpoints are proved before evaluation.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

def p5U7PrimeCutoffLogRow (eta t : ℝ) : ℝ :=
  Real.log ((1-2*t)/(t*(1+eta))) / (t*(1-t))

theorem p5U7PrimeCutoffLog_geometry {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    0 < (1-2*t)/(t*(1+eta)) ∧ 0 < t*(1-t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have he1 : 0 < 1+eta := by linarith
  exact ⟨div_pos (by linarith [ht.2]) (mul_pos ht0 he1),
    mul_pos ht0 (by linarith [ht.2])⟩

/-- The logarithmic sign is the exact actual cutoff-support condition. -/
theorem p5U7PrimeCutoffLog_arg_ge_one_iff {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    1 ≤ (1-2*t)/(t*(1+eta)) ↔ t ≤ (1-t)/(2+eta) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have he1 : 0 < 1+eta := by linarith
  have he2 : 0 < 2+eta := by linarith
  constructor
  · intro h
    have hm := (one_le_div (mul_pos ht0 he1)).mp h
    exact (le_div_iff₀ he2).mpr (by nlinarith only [hm])
  · intro h
    have hm := (le_div_iff₀ he2).mp h
    exact (one_le_div (mul_pos ht0 he1)).mpr (by nlinarith only [hm])

/-- Exact arbitrary-cutoff row evaluation on its full CLOSED active band.
The endpoint c_eta=t is included and gives a genuine zero-width row. -/
theorem p5U7PrimeCutoffRow_eq_log_active {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3))
    (htc : t ≤ (1-t)/(2+eta)) :
    p5U7PrimeCutoffRow eta t = p5U7PrimeCutoffLogRow eta t := by
  let c : ℝ := (1-t)/(2+eta)
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : t < 1 := by linarith [ht.2]
  have hA : 0 < 1-t := sub_pos.mpr ht1
  have he1 : 0 < 1+eta := by linarith
  have he2 : 0 < 2+eta := by linarith
  have hc0 : 0 < c := ht0.trans_le htc
  have hcU : c ≤ (1-t)/2 := p5U7PrimeCutoff_cap_le heta ht
  have hprefix : p5U7PrimeCutoffRow eta t =
      ∫ u in t..c, p5U7ComponentPrimeKernel t u := by
    change (∫ u in t..max t c, p5U7PrimeEtaExtension ![t,u]) = _
    rw [max_eq_right htc]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le htc] at hu
    exact p5U7PrimeEtaExtension_eq_triangle ⟨ht.1,hu.1,hu.2.trans hcU⟩
  have hcont := p5U7ComponentPrimeKernel_row_continuousOn ht
  have hp : IntervalIntegrable (p5U7ComponentPrimeKernel t) volume t c :=
    ContinuousOn.intervalIntegrable_of_Icc htc
      (hcont.mono (fun u hu => ⟨hu.1,hu.2.trans hcU⟩))
  have htailInt : IntervalIntegrable (p5U7ComponentPrimeKernel t) volume c ((1-t)/2) :=
    ContinuousOn.intervalIntegrable_of_Icc hcU
      (hcont.mono (fun u hu => ⟨htc.trans hu.1,hu.2⟩))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hp htailInt
  have hfull := p5U7ComponentPrimeRow_eq_log ht
  change (∫ u in t..((1-t)/2), p5U7ComponentPrimeKernel t u) =
    Real.log ((1-2*t)/t)/(t*(1-t)) at hfull
  have htail := currentChenUpsilon9Harmonic_inner_integral ht0 ht1 hc0 hcU
  rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le hcU] at htail
  change (∫ u in c..((1-t)/2), p5U7ComponentPrimeKernel t u) =
    Real.log ((1-t-c)/c)/(t*(1-t)) at htail
  have hratio : (1-t-c)/c = 1+eta := by
    dsimp only [c]
    field_simp [he2.ne',hA.ne']
    <;> ring
  rw [hratio] at htail
  have hR : 0 < (1-2*t)/t := div_pos (by linarith [ht.2]) ht0
  have hlog : Real.log ((1-2*t)/t)-Real.log (1+eta) =
      Real.log ((1-2*t)/(t*(1+eta))) := by
    rw [← Real.log_div hR.ne' he1.ne']
    congr 1
    field_simp [ht0.ne',he1.ne']
    <;> ring
  calc
    p5U7PrimeCutoffRow eta t =
        (∫ u in t..((1-t)/2), p5U7ComponentPrimeKernel t u) -
          ∫ u in c..((1-t)/2), p5U7ComponentPrimeKernel t u := by
      rw [hprefix]
      linarith only [hadd]
    _ = Real.log ((1-2*t)/t)/(t*(1-t)) - Real.log (1+eta)/(t*(1-t)) := by
      rw [hfull,htail]
    _ = (Real.log ((1-2*t)/t)-Real.log (1+eta))/(t*(1-t)) := (sub_div _ _ _).symm
    _ = p5U7PrimeCutoffLogRow eta t := by rw [hlog]; rfl

/-- Empty rows remain an explicit zero branch. -/
theorem p5U7PrimeCutoffRow_eq_log_ite {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    p5U7PrimeCutoffRow eta t =
      if t ≤ (1-t)/(2+eta) then p5U7PrimeCutoffLogRow eta t else 0 := by
  by_cases htc : t ≤ (1-t)/(2+eta)
  · rw [if_pos htc]
    exact p5U7PrimeCutoffRow_eq_log_active heta ht htc
  · rw [if_neg htc]
    simp only [p5U7PrimeCutoffRow,max_eq_left (lt_of_not_ge htc).le,
      intervalIntegral.integral_same]

/-- At the support wall the logarithm and the clamped integral both vanish. -/
theorem p5U7PrimeCutoffLogRow_eq_zero_at_wall {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3))
    (hwall : t = (1-t)/(2+eta)) :
    p5U7PrimeCutoffLogRow eta t = 0 ∧ p5U7PrimeCutoffRow eta t = 0 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have he1 : 0 < 1+eta := by linarith
  have he2 : 0 < 2+eta := by linarith
  have hm : t*(2+eta) = 1-t := (eq_div_iff he2.ne').mp hwall
  have harg : (1-2*t)/(t*(1+eta)) = 1 := by
    apply (div_eq_one_iff_eq (mul_pos ht0 he1).ne').mpr
    nlinarith only [hm]
  have hz : p5U7PrimeCutoffLogRow eta t = 0 := by
    rw [p5U7PrimeCutoffLogRow,harg,Real.log_one,zero_div]
  exact ⟨hz,(p5U7PrimeCutoffRow_eq_log_active heta ht hwall.le).trans hz⟩

/-- Positive-part form keeps the inactive zero branch and the closed wall. -/
theorem p5U7PrimeCutoffRow_eq_log_positive_part {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    p5U7PrimeCutoffRow eta t = max 0 (p5U7PrimeCutoffLogRow eta t) := by
  have hg := p5U7PrimeCutoffLog_geometry heta ht
  by_cases htc : t ≤ (1-t)/(2+eta)
  · have harg := (p5U7PrimeCutoffLog_arg_ge_one_iff heta ht).mpr htc
    have hlog : 0 ≤ p5U7PrimeCutoffLogRow eta t :=
      div_nonneg (Real.log_nonneg harg) hg.2.le
    rw [max_eq_right hlog]
    exact p5U7PrimeCutoffRow_eq_log_active heta ht htc
  · have harg : (1-2*t)/(t*(1+eta)) < 1 :=
      lt_of_not_ge (fun h => htc ((p5U7PrimeCutoffLog_arg_ge_one_iff heta ht).mp h))
    have hlog : p5U7PrimeCutoffLogRow eta t ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hg.1.le harg.le) hg.2.le
    rw [max_eq_left hlog,p5U7PrimeCutoffRow_eq_log_ite heta ht,if_neg htc]
end
end ImbalancedChen
