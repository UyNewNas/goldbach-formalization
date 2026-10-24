import ImbalancedChen.P2ContinuousSieveRational

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

A new integrated rule for the literal Suzuki upper numerator on [3,4].
Its actual delayed source f(t-1) is bounded by explicit rational functions,
whose primitives are evaluated exactly.  Rational logarithm certificates
then give rational H/F/D nodes and whole-cell bounds.  There is no target
node, table-validity, desired increment, or final quadrature premise.

The preceding draft must be staged as ImbalancedChen.P2ContinuousSieveRational
when compilation resumes.  These are new conservative strip enclosures;
they do not certify the sharper stored 112-bit table.
-/

namespace ImbalancedChen.P2SecondStripRationalEnclosure

noncomputable section

open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open P2ContinuousSieveRational

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

def lowKernel (t : ℝ) : ℝ := 2 / (t - 1) - 4 / (t - 1) ^ 2
def highKernel (t : ℝ) : ℝ := 1 - 2 / (t - 1)
def lowPrimitive (t : ℝ) : ℝ := 2 * Real.log (t - 1) + 4 / (t - 1)
def highPrimitive (t : ℝ) : ℝ := t - 2 * Real.log (t - 1)

/-- Signed comparison for the actual source, valid at both strip endpoints. -/
theorem actual_delayed_lower_bounds {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    lowKernel t ≤ lower (t - 1) ∧ lower (t - 1) ≤ highKernel t := by
  have htpos : 0 < t - 1 := by linarith
  have hloglo := log_lower_rational_function (x := t - 2) (by linarith)
  rw [show t - 2 + 1 = t - 1 by ring] at hloglo
  have hloghi := Real.log_le_sub_one_of_pos (by linarith : 0 < t - 2)
  have hlow := div_le_div_of_nonneg_right hloglo htpos.le
  have hhigh := div_le_div_of_nonneg_right hloghi htpos.le
  rw [lower_eq_log (by linarith : 2 ≤ t - 1) (by linarith : t - 1 ≤ 4)]
  have harg : t - 1 - 1 = t - 2 := by ring
  rw [harg]
  constructor
  · convert hlow using 1 <;> dsimp [lowKernel] <;>
      field_simp [ne_of_gt htpos] <;> ring
  · convert hhigh using 1 <;> dsimp [highKernel] <;>
      field_simp [ne_of_gt htpos] <;> ring

private theorem lowKernel_continuousOn {s : ℝ} (hs : 3 ≤ s) :
    ContinuousOn lowKernel (Icc 3 s) := by
  have hd : ContinuousOn (fun t : ℝ => t - 1) (Icc 3 s) :=
    continuousOn_id.sub continuousOn_const
  have hn : ∀ t ∈ Icc (3 : ℝ) s, t - 1 ≠ 0 := by
    intro t ht
    linarith [ht.1]
  exact (continuousOn_const.div hd hn).sub
    (continuousOn_const.div (hd.pow 2) (fun t ht => pow_ne_zero 2 (hn t ht)))

private theorem highKernel_continuousOn {s : ℝ} (hs : 3 ≤ s) :
    ContinuousOn highKernel (Icc 3 s) := by
  have hd : ContinuousOn (fun t : ℝ => t - 1) (Icc 3 s) :=
    continuousOn_id.sub continuousOn_const
  exact continuousOn_const.sub (continuousOn_const.div hd (by
    intro t ht
    linarith [ht.1]))

private theorem hasDerivAt_lowPrimitive {t : ℝ} (ht : 1 < t) :
    HasDerivAt lowPrimitive (lowKernel t) t := by
  have hn : t - 1 ≠ 0 := by linarith
  have hd := (hasDerivAt_id t).sub_const 1
  have hlog := hd.log hn
  have hquot := (hasDerivAt_const t (4 : ℝ)).div hd hn
  have h := (hlog.const_mul 2).add hquot
  apply h.congr_deriv
  dsimp [lowKernel]
  field_simp [hn]
  <;> ring

private theorem hasDerivAt_highPrimitive {t : ℝ} (ht : 1 < t) :
    HasDerivAt highPrimitive (highKernel t) t := by
  have hn : t - 1 ≠ 0 := by linarith
  have hlog := ((hasDerivAt_id t).sub_const 1).log hn
  have h := (hasDerivAt_id t).sub (hlog.const_mul 2)
  apply h.congr_deriv
  dsimp [highKernel]
  field_simp [hn]
  <;> ring

/-- Exact integrated rational-function minorant for the second strip. -/
theorem integral_lowKernel {s : ℝ} (hs : 3 ≤ s) :
    (∫ t in (3 : ℝ)..s, lowKernel t) =
      2 * Real.log (s - 1) + 4 / (s - 1) - 2 * Real.log 2 - 2 := by
  have hd : ∀ t ∈ uIcc (3 : ℝ) s,
      HasDerivAt lowPrimitive (lowKernel t) t := by
    intro t ht
    rw [uIcc_of_le hs] at ht
    exact hasDerivAt_lowPrimitive (by linarith [ht.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((lowKernel_continuousOn hs).intervalIntegrable_of_Icc hs)]
  norm_num [lowPrimitive]
  <;> ring

/-- Exact integrated rational-function majorant for the second strip. -/
theorem integral_highKernel {s : ℝ} (hs : 3 ≤ s) :
    (∫ t in (3 : ℝ)..s, highKernel t) =
      s - 3 - 2 * Real.log (s - 1) + 2 * Real.log 2 := by
  have hd : ∀ t ∈ uIcc (3 : ℝ) s,
      HasDerivAt highPrimitive (highKernel t) t := by
    intro t ht
    rw [uIcc_of_le hs] at ht
    exact hasDerivAt_highPrimitive (by linarith [ht.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((highKernel_continuousOn hs).intervalIntegrable_of_Icc hs)]
  norm_num [highPrimitive]
  <;> ring

/-- The actual delay equation yields new closed enclosures on the whole
second strip.  The seed H(3)=1 is proved from the literal source. -/
theorem H_second_strip_closed_bounds {s : ℝ} (hs3 : 3 ≤ s) (hs4 : s ≤ 4) :
    2 * Real.log (s - 1) - 2 * Real.log 2 + 4 / (s - 1) - 1 ≤ H s ∧
      H s ≤ s - 2 - 2 * Real.log (s - 1) + 2 * Real.log 2 := by
  have hf := (shifted_factors_integrable (x := (3 : ℝ)) (by norm_num) hs3).2
  have hl := (lowKernel_continuousOn hs3).intervalIntegrable_of_Icc hs3
  have hu := (highKernel_continuousOn hs3).intervalIntegrable_of_Icc hs3
  have hlo := intervalIntegral.integral_mono_on hs3 hl hf (fun t ht =>
    (actual_delayed_lower_bounds ht.1 (ht.2.trans hs4)).1)
  have hhi := intervalIntegral.integral_mono_on hs3 hf hu (fun t ht =>
    (actual_delayed_lower_bounds ht.1 (ht.2.trans hs4)).2)
  have heq := H_sub (x := (3 : ℝ)) (by norm_num) hs3
  have hseed : H 3 = 1 := H_eq_one (by norm_num) (by norm_num)
  rw [integral_lowKernel hs3] at hlo
  rw [integral_highKernel hs3] at hhi
  rw [hseed] at heq
  constructor <;> linarith only [hlo, hhi, heq]

/-- A new rational lower H-node generated by the integrated delayed rule. -/
def secondHLower (n : ℕ) (q : ℚ) : ℚ :=
  2 * logLower n q - 2 * logUpper n 3 + 4 / (q - 1) - 1

/-- A new rational upper H-node generated by the integrated delayed rule. -/
def secondHUpper (n : ℕ) (q : ℚ) : ℚ :=
  q - 2 - 2 * logLower n q + 2 * logUpper n 3

/-- Pure rational endpoints for every literal H-node in [3,4]. -/
theorem H_second_strip_rational_bounds (n : ℕ) (q : ℚ)
    (hq3 : 3 ≤ q) (hq4 : q ≤ 4) :
    (secondHLower n q : ℝ) ≤ H (q : ℝ) ∧
      H (q : ℝ) ≤ (secondHUpper n q : ℝ) := by
  have hq3R : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hq4R : (q : ℝ) ≤ 4 := by exact_mod_cast hq4
  obtain ⟨hlo, hhi⟩ := H_second_strip_closed_bounds hq3R hq4R
  obtain ⟨hqlo, _hqhi⟩ := log_bounds n q (by linarith)
  have htwo := (log_bounds n 3 (by norm_num)).2
  norm_num at htwo
  dsimp [secondHLower, secondHUpper]
  push_cast
  constructor <;> linarith only [hlo, hhi, hqlo, htwo]

/-- Rational F-nodes obtained by division by the positive new endpoint. -/
theorem upper_second_strip_rational_bounds (n : ℕ) (q : ℚ)
    (hq3 : 3 ≤ q) (hq4 : q ≤ 4) :
    ((secondHLower n q / q : ℚ) : ℝ) ≤ upper (q : ℝ) ∧
      upper (q : ℝ) ≤ ((secondHUpper n q / q : ℚ) : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by linarith)
  have heq : H (q : ℝ) / (q : ℝ) = upper (q : ℝ) := by
    dsimp [H]
    field_simp [ne_of_gt hqpos]
  obtain ⟨hl, hu⟩ := H_second_strip_rational_bounds n q hq3 hq4
  constructor
  · simpa only [Rat.cast_div, heq] using div_le_div_of_nonneg_right hl hqpos.le
  · simpa only [Rat.cast_div, heq] using div_le_div_of_nonneg_right hu hqpos.le

/-- Direct supplier for the original 16384-grid H endpoints through 4.
The hypotheses are only the integer range of the node, not its semantics. -/
theorem original_second_strip_H_node_bounds (n i : ℕ)
    (hi3 : 49152 ≤ i) (hi4 : i ≤ 65536) :
    (secondHLower n ((i : ℚ) / 16384) : ℝ) ≤ H ((i : ℝ) / 16384) ∧
      H ((i : ℝ) / 16384) ≤ (secondHUpper n ((i : ℚ) / 16384) : ℝ) := by
  have hi3Q : (49152 : ℚ) ≤ (i : ℚ) := by exact_mod_cast hi3
  have hi4Q : (i : ℚ) ≤ (65536 : ℚ) := by exact_mod_cast hi4
  have hq3 : (3 : ℚ) ≤ (i : ℚ) / 16384 := by linarith
  have hq4 : (i : ℚ) / 16384 ≤ (4 : ℚ) := by linarith
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
    H_second_strip_rational_bounds n ((i : ℚ) / 16384) hq3 hq4

/-- Every real point of the second-strip cell has a rational F enclosure.
Only its rational endpoints are used by the supplier. -/
theorem upper_second_strip_cell_bounds (n : ℕ) (a b : ℚ) (s : ℝ)
    (ha : 3 ≤ a) (hb : b ≤ 4) (has : (a : ℝ) ≤ s) (hsb : s ≤ (b : ℝ)) :
    ((secondHLower n b / b : ℚ) : ℝ) ≤ upper s ∧
      upper s ≤ ((secondHUpper n a / a : ℚ) : ℝ) := by
  have hab : a ≤ b := by exact_mod_cast (has.trans hsb)
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 2 ≤ a by linarith)
  have hl := (upper_second_strip_rational_bounds n b (ha.trans hab) hb).1
  have hu := (upper_second_strip_rational_bounds n a ha (hab.trans hb)).2
  exact ⟨hl.trans (upper_antitone (haR.trans has) (haR.trans (has.trans hsb)) hsb),
    (upper_antitone haR (haR.trans has) has).trans hu⟩

/-- New D-cell bounds through 4, using the integrated F rule and the
independently certified literal f strip; no new D-node is assumed. -/
theorem D_second_strip_cell_bounds (n : ℕ) (a b : ℚ) (s : ℝ)
    (ha : 3 ≤ a) (hb : b ≤ 4) (has : (a : ℝ) ≤ s) (hsb : s ≤ (b : ℝ)) :
    ((secondHLower n b / b - logUpper n b / b : ℚ) : ℝ) ≤ D s ∧
      D s ≤ ((secondHUpper n a / a - logLower n a / a : ℚ) : ℝ) := by
  obtain ⟨hFl, hFu⟩ := upper_second_strip_cell_bounds n a b s ha hb has hsb
  obtain ⟨hfl, hfu⟩ := lower_rational_cell_bounds n a b s (by linarith) hb has hsb
  rw [D_eq_upper_sub_lower]
  push_cast at hFl hFu hfl hfu ⊢
  constructor <;> linarith only [hFl, hFu, hfl, hfu]

end

end ImbalancedChen.P2SecondStripRationalEnclosure
