import ImbalancedChen.P2SecondStripRationalEnclosure

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

The lower numerator L=s*f on [4,5] is propagated from the genuine source
equation L(s)-L(4)=integral_3^(s-1) F(u) du.  The actual second-strip H=s*F
bounds give rational-function bounds for F, with explicit primitives.
The resulting rational node and whole-cell f enclosures have no target
node or table-semantic premise.  H and L retain their distinct meanings.
The two preceding drafts must be staged under ImbalancedChen to compile.
-/

namespace ImbalancedChen.P2ThirdStripRationalEnclosure

noncomputable section

open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open P2ContinuousSieveRational P2SecondStripRationalEnclosure

def logTwoUpper : ℚ := 693148 / 1000000

private theorem logTwoUpper_eq : (logTwoUpper : ℝ) = (693148 : ℝ) / 1000000 := by
  norm_num [logTwoUpper]

private theorem log_lower_rational_function {x : ℝ} (hx : 1 ≤ x) :
    2 * ((x - 1) / (x + 1)) ≤ Real.log x := by
  let z : ℝ := (x - 1) / (x + 1)
  have hxp : 0 < x + 1 := by linarith
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hxp.le
  have hz1 : z < 1 := by
    apply (div_lt_iff₀ hxp).2
    linarith
  have heq : (1 + z) / (1 - z) = x := by
    apply (div_eq_iff (by linarith : 1 - z ≠ 0)).2
    dsimp [z]
    field_simp [ne_of_gt hxp]
    <;> ring
  have h := Real.sum_range_le_log_div hz0 hz1 1
  rw [heq] at h
  norm_num [Finset.sum_range_succ] at h
  dsimp [z] at h
  linarith only [h]

def lowKernel (u : ℝ) : ℝ :=
  4 / (u - 1) - (1 + 2 * (logTwoUpper : ℝ)) / u - 8 / u ^ 2

def highKernel (u : ℝ) : ℝ :=
  1 + (2 * (logTwoUpper : ℝ) - 6) / u + 8 / u ^ 2

def lowPrimitive (u : ℝ) : ℝ :=
  4 * Real.log (u - 1) - (1 + 2 * (logTwoUpper : ℝ)) * Real.log u + 8 / u

def highPrimitive (u : ℝ) : ℝ :=
  u + (2 * (logTwoUpper : ℝ) - 6) * Real.log u - 8 / u

/-- Actual F on [3,4], using the previously proved H enclosure rather
than a newly assumed F node.  Both kernels are integrated below. -/
theorem actual_upper_second_strip_kernel_bounds {u : ℝ}
    (hu3 : 3 ≤ u) (hu4 : u ≤ 4) :
    lowKernel u ≤ upper u ∧ upper u ≤ highKernel u := by
  have hu0 : 0 < u := by linarith
  have hu1 : u - 1 ≠ 0 := by linarith
  obtain ⟨hHlo, hHhi⟩ := H_second_strip_closed_bounds hu3 hu4
  have hlog := log_lower_rational_function (x := u - 1) (by linarith)
  rw [show u - 1 - 1 = u - 2 by ring,
    show u - 1 + 1 = u by ring] at hlog
  have hc : Real.log 2 ≤ (logTwoUpper : ℝ) := by
    rw [logTwoUpper_eq]
    exact log_two_bounds.2
  have hlowNumer : 4 * ((u - 2) / u) - 2 * (logTwoUpper : ℝ) +
      4 / (u - 1) - 1 ≤ H u := by
    linarith only [hHlo, hlog, hc]
  have hhighNumer : H u ≤ u - 2 - 4 * ((u - 2) / u) +
      2 * (logTwoUpper : ℝ) := by
    linarith only [hHhi, hlog, hc]
  have hHdiv : H u / u = upper u := by
    dsimp [H]
    field_simp [ne_of_gt hu0]
  constructor
  · calc
      lowKernel u = (4 * ((u - 2) / u) - 2 * (logTwoUpper : ℝ) +
          4 / (u - 1) - 1) / u := by
        dsimp [lowKernel]
        field_simp [ne_of_gt hu0, hu1]
        <;> ring
      _ ≤ H u / u := div_le_div_of_nonneg_right hlowNumer hu0.le
      _ = upper u := hHdiv
  · calc
      upper u = H u / u := hHdiv.symm
      _ ≤ (u - 2 - 4 * ((u - 2) / u) + 2 * (logTwoUpper : ℝ)) / u :=
        div_le_div_of_nonneg_right hhighNumer hu0.le
      _ = highKernel u := by
        dsimp [highKernel]
        field_simp [ne_of_gt hu0]
        <;> ring

private theorem kernel_continuousOn {b : ℝ} (hb : 3 ≤ b) :
    ContinuousOn lowKernel (Icc 3 b) ∧ ContinuousOn highKernel (Icc 3 b) := by
  have hid : ContinuousOn (fun u : ℝ => u) (Icc 3 b) := continuousOn_id
  have hsub := hid.sub continuousOn_const
  have hn0 : ∀ u ∈ Icc (3 : ℝ) b, u ≠ 0 := by
    intro u hu
    linarith [hu.1]
  have hn1 : ∀ u ∈ Icc (3 : ℝ) b, u - 1 ≠ 0 := by
    intro u hu
    linarith [hu.1]
  have hpow : ∀ u ∈ Icc (3 : ℝ) b, u ^ 2 ≠ 0 :=
    fun u hu => pow_ne_zero 2 (hn0 u hu)
  exact ⟨((continuousOn_const.div hsub hn1).sub
    (continuousOn_const.div hid hn0)).sub (continuousOn_const.div (hid.pow 2) hpow),
    (continuousOn_const.add (continuousOn_const.div hid hn0)).add
      (continuousOn_const.div (hid.pow 2) hpow)⟩

private theorem hasDerivAt_lowPrimitive {u : ℝ} (hu : 1 < u) :
    HasDerivAt lowPrimitive (lowKernel u) u := by
  have hn0 : u ≠ 0 := by linarith
  have hn1 : u - 1 ≠ 0 := by linarith
  have hlog1 := ((hasDerivAt_id u).sub_const 1).log hn1
  have hlog0 := Real.hasDerivAt_log hn0
  have hquot := (hasDerivAt_const u (8 : ℝ)).div (hasDerivAt_id u) hn0
  have h := ((hlog1.const_mul 4).sub
    (hlog0.const_mul (1 + 2 * (logTwoUpper : ℝ)))).add hquot
  apply h.congr_deriv
  dsimp [lowKernel]
  field_simp [hn0, hn1]
  <;> ring

private theorem hasDerivAt_highPrimitive {u : ℝ} (hu : 1 < u) :
    HasDerivAt highPrimitive (highKernel u) u := by
  have hn0 : u ≠ 0 := by linarith
  have hlog0 := Real.hasDerivAt_log hn0
  have hquot := (hasDerivAt_const u (8 : ℝ)).div (hasDerivAt_id u) hn0
  have h := ((hasDerivAt_id u).add
    (hlog0.const_mul (2 * (logTwoUpper : ℝ) - 6))).sub hquot
  apply h.congr_deriv
  dsimp [highKernel]
  field_simp [hn0]
  <;> ring

/-- Exact primitive evaluation of both new rational kernels. -/
theorem integrated_kernel_bounds {b : ℝ} (hb : 3 ≤ b) :
    (∫ u in (3 : ℝ)..b, lowKernel u) = lowPrimitive b - lowPrimitive 3 ∧
      (∫ u in (3 : ℝ)..b, highKernel u) = highPrimitive b - highPrimitive 3 := by
  have hdlo : ∀ u ∈ uIcc (3 : ℝ) b,
      HasDerivAt lowPrimitive (lowKernel u) u := by
    intro u hu
    rw [uIcc_of_le hb] at hu
    exact hasDerivAt_lowPrimitive (by linarith [hu.1])
  have hdhi : ∀ u ∈ uIcc (3 : ℝ) b,
      HasDerivAt highPrimitive (highKernel u) u := by
    intro u hu
    rw [uIcc_of_le hb] at hu
    exact hasDerivAt_highPrimitive (by linarith [hu.1])
  obtain ⟨hcl, hcu⟩ := kernel_continuousOn hb
  exact ⟨intervalIntegral.integral_eq_sub_of_hasDerivAt hdlo
      (hcl.intervalIntegrable_of_Icc hb),
    intervalIntegral.integral_eq_sub_of_hasDerivAt hdhi (hcu.intervalIntegrable_of_Icc hb)⟩

/-- The actual third-strip lower numerator follows from the actual
delayed F integral and the genuine initial value L(4)=log(3). -/
theorem L_third_strip_closed_bounds {s : ℝ} (hs4 : 4 ≤ s) (hs5 : s ≤ 5) :
    (2 + 2 * (logTwoUpper : ℝ)) * Real.log 3 + 4 * Real.log (s - 2) -
        (1 + 2 * (logTwoUpper : ℝ)) * Real.log (s - 1) -
        4 * Real.log 2 + 8 / (s - 1) - 8 / 3 ≤ L s ∧
      L s ≤ (7 - 2 * (logTwoUpper : ℝ)) * Real.log 3 + s - 4 +
        (2 * (logTwoUpper : ℝ) - 6) * Real.log (s - 1) - 8 / (s - 1) + 8 / 3 := by
  have hb : (3 : ℝ) ≤ s - 1 := by linarith
  have hfmono : AntitoneOn upper (uIcc (3 : ℝ) (s - 1)) := by
    rw [uIcc_of_le hb]
    intro u hu v hv huv
    exact upper_antitone (by change 2 ≤ u; linarith [hu.1])
      (by change 2 ≤ v; linarith [hv.1]) huv
  have hf := hfmono.intervalIntegrable
  obtain ⟨hcl, hcu⟩ := kernel_continuousOn hb
  have hlo := intervalIntegral.integral_mono_on hb (hcl.intervalIntegrable_of_Icc hb)
    hf (fun u hu => (actual_upper_second_strip_kernel_bounds hu.1
      (by linarith [hu.2])).1)
  have hhi := intervalIntegral.integral_mono_on hb hf (hcu.intervalIntegrable_of_Icc hb)
    (fun u hu => (actual_upper_second_strip_kernel_bounds hu.1
      (by linarith [hu.2])).2)
  have heq := L_sub_delayed (x := (4 : ℝ)) (by norm_num) hs4
  have hint : (∫ u in (3 : ℝ)..(s - 1), H u / u) =
      ∫ u in (3 : ℝ)..(s - 1), upper u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hb] at hu
    have hn : u ≠ 0 := by linarith [hu.1]
    simp [H, hn]
  have hseed : L 4 = Real.log 3 := by
    simpa using (L_eq_log (s := (4 : ℝ)) (by norm_num) (by norm_num))
  norm_num only [show (4 : ℝ) - 1 = 3 by norm_num] at heq
  rw [hint, hseed] at heq
  obtain ⟨hil, hiu⟩ := integrated_kernel_bounds hb
  rw [hil] at hlo
  rw [hiu] at hhi
  dsimp [lowPrimitive, highPrimitive] at hlo hhi
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num] at hlo hhi
  constructor <;> nlinarith only [hlo, hhi, heq]

def thirdLLower (n : ℕ) (q : ℚ) : ℚ :=
  (2 + 2 * logTwoUpper) * logLower n 4 + 4 * logLower n (q - 1) -
    (1 + 2 * logTwoUpper) * logUpper n q - 4 * logTwoUpper + 8 / (q - 1) - 8 / 3

def thirdLUpper (n : ℕ) (q : ℚ) : ℚ :=
  (7 - 2 * logTwoUpper) * logUpper n 4 + q - 4 +
    (2 * logTwoUpper - 6) * logLower n q - 8 / (q - 1) + 8 / 3

/-- The integrated new-strip supplier gives pure rational L nodes. -/
theorem L_third_strip_rational_bounds (n : ℕ) (q : ℚ)
    (hq4 : 4 ≤ q) (hq5 : q ≤ 5) :
    (thirdLLower n q : ℝ) ≤ L (q : ℝ) ∧
      L (q : ℝ) ≤ (thirdLUpper n q : ℝ) := by
  have hq4R : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq4
  have hq5R : (q : ℝ) ≤ 5 := by exact_mod_cast hq5
  obtain ⟨hlo, hhi⟩ := L_third_strip_closed_bounds hq4R hq5R
  obtain ⟨h3lo, h3hi⟩ := log_bounds n 4 (by norm_num)
  obtain ⟨hqlo, hqhi⟩ := log_bounds n q (by linarith)
  have hm := (log_bounds n (q - 1) (by linarith)).1
  have harg : ((q - 1 : ℚ) : ℝ) - 1 = (q : ℝ) - 2 := by
    push_cast
    <;> ring
  rw [harg] at hm
  norm_num only [show (4 : ℝ) - 1 = 3 by norm_num] at h3lo h3hi
  have hc : Real.log 2 ≤ (logTwoUpper : ℝ) := by
    rw [logTwoUpper_eq]
    exact log_two_bounds.2
  dsimp [thirdLLower, thirdLUpper]
  push_cast
  rw [logTwoUpper_eq] at hlo hhi hc ⊢
  constructor <;> linarith only [hlo, hhi, h3lo, h3hi, hqlo, hqhi, hm, hc]

/-- Division by the new endpoint gives the actual normalized f, not F. -/
theorem lower_third_strip_rational_bounds (n : ℕ) (q : ℚ)
    (hq4 : 4 ≤ q) (hq5 : q ≤ 5) :
    ((thirdLLower n q / q : ℚ) : ℝ) ≤ lower (q : ℝ) ∧
      lower (q : ℝ) ≤ ((thirdLUpper n q / q : ℚ) : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by linarith)
  have heq : L (q : ℝ) / (q : ℝ) = lower (q : ℝ) := by
    dsimp [L]
    field_simp [ne_of_gt hqpos]
  obtain ⟨hl, hu⟩ := L_third_strip_rational_bounds n q hq4 hq5
  constructor
  · simpa only [Rat.cast_div, heq] using div_le_div_of_nonneg_right hl hqpos.le
  · simpa only [Rat.cast_div, heq] using div_le_div_of_nonneg_right hu hqpos.le

/-- Direct interface to original lower-factor grid nodes from 4 through 5. -/
theorem original_third_strip_lower_node_bounds (n i : ℕ)
    (hi4 : 65536 ≤ i) (hi5 : i ≤ 81920) :
    ((thirdLLower n ((i : ℚ) / 16384) / ((i : ℚ) / 16384) : ℚ) : ℝ) ≤
        lower ((i : ℝ) / 16384) ∧
      lower ((i : ℝ) / 16384) ≤
        ((thirdLUpper n ((i : ℚ) / 16384) / ((i : ℚ) / 16384) : ℚ) : ℝ) := by
  have hi4Q : (65536 : ℚ) ≤ (i : ℚ) := by exact_mod_cast hi4
  have hi5Q : (i : ℚ) ≤ (81920 : ℚ) := by exact_mod_cast hi5
  have hq4 : (4 : ℚ) ≤ (i : ℚ) / 16384 := by linarith
  have hq5 : (i : ℚ) / 16384 ≤ (5 : ℚ) := by linarith
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
    lower_third_strip_rational_bounds n ((i : ℚ) / 16384) hq4 hq5

/-- Rational endpoints certify the actual lower factor throughout a new
third-strip cell, including cells crossing arbitrary original grid nodes. -/
theorem lower_third_strip_cell_bounds (n : ℕ) (a b : ℚ) (s : ℝ)
    (ha : 4 ≤ a) (hb : b ≤ 5) (has : (a : ℝ) ≤ s) (hsb : s ≤ (b : ℝ)) :
    ((thirdLLower n a / a : ℚ) : ℝ) ≤ lower s ∧
      lower s ≤ ((thirdLUpper n b / b : ℚ) : ℝ) := by
  have hab : a ≤ b := by exact_mod_cast (has.trans hsb)
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 2 ≤ a by linarith)
  have hl := (lower_third_strip_rational_bounds n a ha (hab.trans hb)).1
  have hu := (lower_third_strip_rational_bounds n b (ha.trans hab) hb).2
  exact ⟨hl.trans (lower_monotone haR (haR.trans has) has),
    (lower_monotone (haR.trans has) (haR.trans (has.trans hsb)) hsb).trans hu⟩

end

end ImbalancedChen.P2ThirdStripRationalEnclosure
