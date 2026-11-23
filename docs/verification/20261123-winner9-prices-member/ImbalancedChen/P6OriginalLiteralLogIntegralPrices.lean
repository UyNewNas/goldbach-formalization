import ImbalancedChen.P6OriginalLogPolynomialRows

namespace ImbalancedChen.P6OriginalLiteralLogIntegralPrices

noncomputable section
open MeasureTheory Set P6OriginalLogPolynomialBound P6OriginalLogPolynomialPrices
open scoped Interval

def coord (l r t : ℝ) := (r-t)/(r-l)
def value (w : LogRow) (x : ℝ) :=
  Real.log (((w.a:ℝ)+x*(w.b:ℝ))/((w.c:ℝ)+x*(w.d:ℝ))) / ev w.den x

private theorem coordinate_mem {l r t : ℝ} (hlr : l < r) (ht : t ∈ Icc l r) :
    coord l r t ∈ Icc (0:ℝ) 1 := by
  have hw := sub_pos.mpr hlr
  exact ⟨div_nonneg (sub_nonneg.mpr ht.2) hw.le, (div_le_iff₀ hw).mpr (by linarith [ht.1])⟩

private theorem positive_guards (w : LogRow) (hv : w.Valid) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    0 < (w.a:ℝ)+x*w.b ∧ 0 < (w.c:ℝ)+x*w.d ∧ 0 < ev w.den x := by
  obtain ⟨ha,hb,hd,_⟩ := hv
  have h (p : Coeffs) (hp : 0 < lower p) : 0 < ev p x :=
    (show (0:ℝ) < (lower p:ℝ) by exact_mod_cast hp).trans_le (lower_le_ev _ hx)
  exact ⟨by simpa [ev] using h _ ha, by simpa [ev] using h _ hb, h _ hd⟩

private theorem continuous_value (w : LogRow) (hv : w.Valid) :
    ContinuousOn (value w) (Icc (0:ℝ) 1) := by
  have ca (a b : ℚ) : ContinuousOn (fun x : ℝ => (a:ℝ)+x*b) (Icc 0 1) :=
    (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
  apply ContinuousOn.div _ (ev_continuous _).continuousOn (fun x hx => (positive_guards w hv hx).2.2.ne')
  exact ((ca w.a w.b).div (ca w.c w.d) (fun x hx => (positive_guards w hv hx).2.1.ne')).log
    (fun x hx => (div_pos (positive_guards w hv hx).1 (positive_guards w hv hx).2.1).ne')

private theorem value_nonneg (w : LogRow) (hv : w.Valid)
    (h0 : w.c ≤ w.a) (h1 : w.c+w.d ≤ w.a+w.b) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    0 ≤ value w x := by
  have h0' : (w.c:ℝ) ≤ w.a := by exact_mod_cast h0
  have h1' : (w.c:ℝ)+w.d ≤ w.a+w.b := by exact_mod_cast h1
  have hca : (w.c:ℝ)+x*w.d ≤ w.a+x*w.b := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr h0'),
      mul_nonneg hx.1 (sub_nonneg.mpr h1')]
  have hp := positive_guards w hv hx
  exact div_nonneg (Real.log_nonneg ((one_le_div hp.2.1).mpr hca)) hp.2.2.le

private theorem integral_price (w : LogRow) (hv : w.Valid) {l r : ℝ} (hlr : l < r) :
    (∫ t in l..r, value w (coord l r t)) ≤ (r-l)*(average w.p:ℝ) := by
  have hc : Continuous (coord l r) := (continuous_const.sub continuous_id).div_const _
  have hf := (continuous_value w hv).comp hc.continuousOn (fun t ht => coordinate_mem hlr ht)
  refine (intervalIntegral.integral_mono_on hlr.le (hf.intervalIntegrable_of_Icc hlr.le)
    (((ev_continuous w.p).comp hc).intervalIntegrable l r)
    (fun t ht => w.bound hv (coordinate_mem hlr ht))).trans_eq ?_
  exact integral_reverse_polynomial w.p hlr

private theorem product_price (w1 w2 : LogRow) (h1 : w1.Valid) (h2 : w2.Valid)
    (h10 : w1.c ≤ w1.a) (h11 : w1.c+w1.d ≤ w1.a+w1.b)
    (h20 : w2.c ≤ w2.a) (h21 : w2.c+w2.d ≤ w2.a+w2.b)
    {l r : ℝ} (hlr : l<r) :
    (∫ t in l..r, value w1 (coord l r t)*value w2 (coord l r t)) ≤
      (r-l)*(average (mul w1.p w2.p):ℝ) := by
  have hc : Continuous (coord l r) := (continuous_const.sub continuous_id).div_const _
  have hf := ((continuous_value w1 h1).mul (continuous_value w2 h2)).comp
    hc.continuousOn (fun t ht => coordinate_mem hlr ht)
  have hu {t : ℝ} (ht : t ∈ Icc l r) : value w1 (coord l r t)*value w2 (coord l r t) ≤
      ev (mul w1.p w2.p) (coord l r t) := by
    have hz := coordinate_mem hlr ht
    rw [ev_mul]
    exact mul_le_mul (w1.bound h1 hz) (w2.bound h2 hz) (value_nonneg w2 h2 h20 h21 hz)
      ((value_nonneg w1 h1 h10 h11 hz).trans (w1.bound h1 hz))
  refine (intervalIntegral.integral_mono_on hlr.le (hf.intervalIntegrable_of_Icc hlr.le)
    (((ev_continuous _).comp hc).intervalIntegrable l r) (fun _ ht => hu ht)).trans_eq ?_
  exact integral_reverse_polynomial _ hlr

private theorem ninth_value (t : ℝ) : value ninth (coord (19/125) (59/250) t) =
    Real.log ((1-t-59/250)/(59/250))/(t*(1-t)) := by
  have hA : (ninth.a:ℝ)+(coord (19/125) (59/250) t)*ninth.b = 1-t-59/250 := by norm_num [ninth, coord] <;> ring
  have hB : (ninth.c:ℝ)+(coord (19/125) (59/250) t)*ninth.d = 59/250 := by norm_num [ninth, coord] <;> ring
  have hD : ev ninth.den (coord (19/125) (59/250) t) = t*(1-t) := by norm_num [ninth, coord, ev] <;> ring
  unfold value
  rw [hA,hB,hD]

private theorem eighth_value (t : ℝ) : value eighth (coord (417/5000) (1/3) t) =
    Real.log ((2-3*t)/(1))/(t*(1-t)) := by
  have hA : (eighth.a:ℝ)+(coord (417/5000) (1/3) t)*eighth.b = 2-3*t := by norm_num [eighth, coord] <;> ring
  have hB : (eighth.c:ℝ)+(coord (417/5000) (1/3) t)*eighth.d = 1 := by norm_num [eighth, coord] <;> ring
  have hD : ev eighth.den (coord (417/5000) (1/3) t) = t*(1-t) := by norm_num [eighth, coord, ev] <;> ring
  unfold value
  rw [hA,hB,hD]

private theorem seventhPrime_value (t : ℝ) : value seventhPrime (coord (59/250) (1/3) t) =
    Real.log ((1-2*t)/(t))/(t*(1-t)) := by
  have hA : (seventhPrime.a:ℝ)+(coord (59/250) (1/3) t)*seventhPrime.b = 1-2*t := by norm_num [seventhPrime, coord] <;> ring
  have hB : (seventhPrime.c:ℝ)+(coord (59/250) (1/3) t)*seventhPrime.d = t := by norm_num [seventhPrime, coord] <;> ring
  have hD : ev seventhPrime.den (coord (59/250) (1/3) t) = t*(1-t) := by norm_num [seventhPrime, coord, ev] <;> ring
  unfold value
  rw [hA,hB,hD]

private theorem correctionFirst_value (t : ℝ) : value correctionFirst (coord (2) (132/59) t) =
    Real.log ((t-1)/(1))/(t) := by
  have hA : (correctionFirst.a:ℝ)+(coord (2) (132/59) t)*correctionFirst.b = t-1 := by norm_num [correctionFirst, coord] <;> ring
  have hB : (correctionFirst.c:ℝ)+(coord (2) (132/59) t)*correctionFirst.d = 1 := by norm_num [correctionFirst, coord] <;> ring
  have hD : ev correctionFirst.den (coord (2) (132/59) t) = t := by norm_num [correctionFirst, coord, ev] <;> ring
  unfold value
  rw [hA,hB,hD]

private theorem correctionSecond_value (t : ℝ) : value correctionSecond (coord (2) (132/59) t) =
    Real.log ((1-59/250)/((59/250)*(t+1)))/(1) := by
  have hA : (correctionSecond.a:ℝ)+(coord (2) (132/59) t)*correctionSecond.b = 1-59/250 := by norm_num [correctionSecond, coord] <;> ring
  have hB : (correctionSecond.c:ℝ)+(coord (2) (132/59) t)*correctionSecond.d = (59/250)*(t+1) := by norm_num [correctionSecond, coord] <;> ring
  have hD : ev correctionSecond.den (coord (2) (132/59) t) = 1 := by norm_num [correctionSecond, coord, ev] <;> ring
  unfold value
  rw [hA,hB,hD]

theorem ninth_literal_integral :
    (∫ t in (19/125:ℝ)..(59/250:ℝ), Real.log ((1-t-59/250)/(59/250))/(t*(1-t))) ≤
      4816743300211123/10000000000000000 := by
  have h := integral_price ninth ninth_valid (l:=19/125) (r:=59/250) (by norm_num)
  simp_rw [ninth_value] at h
  have hp : ((59/250:ℚ)-(19/125))*average ninth.p ≤ 4816743300211123/10000000000000000 := by decide +kernel
  exact h.trans (by simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    using (Rat.cast_le (K:=ℝ)).mpr hp)

theorem eighth_literal_integral :
    (∫ t in (417/5000:ℝ)..(1/3:ℝ), Real.log ((2-3*t)/(1))/(t*(1-t))) ≤
      5999905266705567/10000000000000000 := by
  have h := integral_price eighth eighth_valid (l:=417/5000) (r:=1/3) (by norm_num)
  simp_rw [eighth_value] at h
  have hp : ((1/3:ℚ)-(417/5000))*average eighth.p ≤ 5999905266705567/10000000000000000 := by decide +kernel
  exact h.trans (by simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    using (Rat.cast_le (K:=ℝ)).mpr hp)

theorem seventhPrime_literal_integral :
    (∫ t in (59/250:ℝ)..(1/3:ℝ), Real.log ((1-2*t)/(t))/(t*(1-t))) ≤
      2042785889856317/10000000000000000 := by
  have h := integral_price seventhPrime seventhPrime_valid (l:=59/250) (r:=1/3) (by norm_num)
  simp_rw [seventhPrime_value] at h
  have hp : ((1/3:ℚ)-(59/250))*average seventhPrime.p ≤ 2042785889856317/10000000000000000 := by decide +kernel
  exact h.trans (by simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    using (Rat.cast_le (K:=ℝ)).mpr hp)

theorem correction_literal_integral :
    (∫ t in (2:ℝ)..(132/59:ℝ),
      (Real.log (t-1)/t)*Real.log ((1-59/250)/((59/250)*(t+1)))) ≤
      3133582170107/10000000000000000 := by
  have h := product_price correctionFirst correctionSecond correctionFirst_valid correctionSecond_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (l:=2) (r:=132/59) (by norm_num)
  simp_rw [correctionFirst_value, correctionSecond_value, div_one] at h
  have hp : ((132/59:ℚ)-2)*average (mul correctionFirst.p correctionSecond.p) ≤
      3133582170107/10000000000000000 := by decide +kernel
  exact h.trans (by simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    using (Rat.cast_le (K:=ℝ)).mpr hp)

end
end ImbalancedChen.P6OriginalLiteralLogIntegralPrices
