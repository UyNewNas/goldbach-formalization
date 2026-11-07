import ImbalancedChen.P2HistoricLogPointInterpreter

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Local error and width propagation for the literal Q80 historical logarithm.
The imported interpreter already binds Python bit_length, both signed shift
branches, the 32 rounded odd terms, and the tail divisor 65 to log(q/Q).
This module adds the previously absent quantitative operation layer. Every
division incurs less than one Q80 ulp per endpoint, uniformly in its signed
integer numerator. Width propagation refers to the actual integer states.

The total logarithm width has an abs(sourceShift) factor multiplying LOG2
width. We do not assert a q-independent total error or identify this Q80
backend with the separate P=2^160/W=2^224 backend. A sharp numerical global
bound requires further source-state endpoint estimates, not a replay.
-/

namespace ImbalancedChen.Certificates.P2HistoricLogWidthPropagation

noncomputable section
open scoped BigOperators
open P2HistoricQ80DefectLookup P2HistoricLogPointInterpreter

def ulp : ℝ := 1 / (Q : ℝ)
def width (x : I80) : ℝ := decode x.hi - decode x.lo

theorem ulp_pos : 0 < ulp := one_div_pos.mpr Q_real_pos

theorem decode_add (a b : ℤ) : decode (a+b) = decode a + decode b := by
  simp only [decode, Int.cast_add, add_div]

theorem decode_mul_int (a b : ℤ) : decode (a*b) = (a : ℝ)*decode b := by
  simp only [decode, Int.cast_mul]
  ring

theorem width_add (x y : I80) : width (x.add y) = width x + width y := by
  simp only [width, I80.add, decode_add]
  ring

theorem width_raw (n : ℤ) : width (I80.raw n) = 0 := by
  simp [width, I80.raw]

theorem width_nonneg {x : I80} (hx : x.lo ≤ x.hi) : 0 ≤ width x := by
  apply sub_nonneg.mpr
  exact div_le_div_of_nonneg_right (by exact_mod_cast hx) Q_real_pos.le

/-- Signed floor division loses less than one integer unit, for every n. -/
theorem ediv_error (n d : ℤ) (hd : 0 < d) :
    0 ≤ (n : ℝ)/(d : ℝ) - (n/d : ℤ) ∧
      (n : ℝ)/(d : ℝ) - (n/d : ℤ) < 1 := by
  have hl := Int.floor_le ((n : ℝ)/(d : ℝ))
  have hu := Int.lt_floor_add_one ((n : ℝ)/(d : ℝ))
  rw [Int.floor_div_cast_of_nonneg hd.le, Int.floor_intCast] at hl hu
  constructor <;> linarith

/-- The exact ceildiv operation has the opposite directed one-unit error. -/
theorem ceilDiv_error (n d : ℤ) (hd : 0 < d) :
    0 ≤ (ceilDiv n d : ℝ) - (n : ℝ)/(d : ℝ) ∧
      (ceilDiv n d : ℝ) - (n : ℝ)/(d : ℝ) < 1 := by
  have hh := ediv_error (-n) d hd
  simp only [Int.cast_neg, neg_div] at hh
  simp only [ceilDiv, Int.cast_neg]
  constructor <;> linarith

theorem ediv_decode_error (n d : ℤ) (hd : 0 < d) :
    0 ≤ ((n : ℝ)/(d : ℝ))/(Q : ℝ) - decode (n/d) ∧
      ((n : ℝ)/(d : ℝ))/(Q : ℝ) - decode (n/d) < ulp := by
  have hh := ediv_error n d hd
  have he : ((n : ℝ)/(d : ℝ))/(Q : ℝ) - decode (n/d) =
      ((n : ℝ)/(d : ℝ) - (n/d : ℤ))/(Q : ℝ) := by
    unfold decode
    ring
  rw [he]
  exact ⟨div_nonneg hh.1 Q_real_pos.le,
    (div_lt_div_iff_of_pos_right Q_real_pos).mpr hh.2⟩

theorem ceilDiv_decode_error (n d : ℤ) (hd : 0 < d) :
    0 ≤ decode (ceilDiv n d) - ((n : ℝ)/(d : ℝ))/(Q : ℝ) ∧
      decode (ceilDiv n d) - ((n : ℝ)/(d : ℝ))/(Q : ℝ) < ulp := by
  have hh := ceilDiv_error n d hd
  have he : decode (ceilDiv n d) - ((n : ℝ)/(d : ℝ))/(Q : ℝ) =
      ((ceilDiv n d : ℝ) - (n : ℝ)/(d : ℝ))/(Q : ℝ) := by
    unfold decode
    ring
  rw [he]
  exact ⟨div_nonneg hh.1 Q_real_pos.le,
    (div_lt_div_iff_of_pos_right Q_real_pos).mpr hh.2⟩

theorem product_lower_error (a b : ℤ) :
    0 ≤ decode a * decode b - decode (a*b/(Q : ℤ)) ∧
      decode a * decode b - decode (a*b/(Q : ℤ)) < ulp := by
  have hh := ediv_decode_error (a*b) (Q : ℤ) Q_int_pos
  have he : (((a*b : ℤ) : ℝ)/(Q : ℝ))/(Q : ℝ) =
      decode a * decode b := by
    simp only [decode, Int.cast_mul]
    ring
  rwa [he] at hh

theorem product_upper_error (a b : ℤ) :
    0 ≤ decode (ceilDiv (a*b) (Q : ℤ)) - decode a * decode b ∧
      decode (ceilDiv (a*b) (Q : ℤ)) - decode a * decode b < ulp := by
  have hh := ceilDiv_decode_error (a*b) (Q : ℤ) Q_int_pos
  have he : (((a*b : ℤ) : ℝ)/(Q : ℝ))/(Q : ℝ) =
      decode a * decode b := by
    simp only [decode, Int.cast_mul]
    ring
  rwa [he] at hh

/-- Literal positiveMul adds less than two ulps to the product width.
No hidden exact-arithmetic replacement of either rounded power is made. -/
theorem positiveMul_width (x y : I80) :
    width (positiveMul x y) <
      decode x.hi * width y + decode y.lo * width x + 2*ulp := by
  have hl := (product_lower_error x.lo y.lo).2
  have hu := (product_upper_error x.hi y.hi).2
  change decode (ceilDiv (x.hi*y.hi) (Q : ℤ)) -
    decode (x.lo*y.lo/(Q : ℤ)) < _
  dsimp only [width]
  nlinarith only [hl,hu]

/-- Uniform propagation from genuine endpoint caps. A and B are caps on
the actual integer state, rather than premises about the resulting log. -/
theorem positiveMul_width_le {x y : I80} {A B : ℝ}
    (hx : x.lo ≤ x.hi) (hy : y.lo ≤ y.hi)
    (hA : decode x.hi ≤ A) (hB : decode y.lo ≤ B) :
    width (positiveMul x y) ≤ A*width y + B*width x + 2*ulp := by
  have h1 := mul_le_mul_of_nonneg_right hA (width_nonneg hy)
  have h2 := mul_le_mul_of_nonneg_right hB (width_nonneg hx)
  exact (positiveMul_width x y).le.trans (by linarith)

/-- Every odd-term division adds less than two ulps, independently of n
and of the signs of the encoded endpoints. -/
theorem divNat_width (x : I80) {n : ℕ} (hn : 0 < n) :
    width (divNat x n) < width x/(n : ℝ) + 2*ulp := by
  have hni : (0 : ℤ) < n := by exact_mod_cast hn
  have hl := (ediv_decode_error x.lo (n : ℤ) hni).2
  have hu := (ceilDiv_decode_error x.hi (n : ℤ) hni).2
  have hel : ((x.lo : ℝ)/(n : ℝ))/(Q : ℝ) = decode x.lo/(n : ℝ) := by
    unfold decode
    ring
  have heh : ((x.hi : ℝ)/(n : ℝ))/(Q : ℝ) = decode x.hi/(n : ℝ) := by
    unfold decode
    ring
  simp only [Int.cast_natCast] at hl hu
  rw [hel] at hl
  rw [heh] at hu
  change decode (ceilDiv x.hi (n : ℤ)) - decode (x.lo/(n : ℤ)) < _
  rw [width, sub_div]
  linarith

/-- Exact width decomposition along the actual state recursion. -/
theorem oddLoop_total_width (square : I80) (ul uh : ℤ) (n : ℕ) :
    width (oddLoop square ul uh n).total =
      ∑ j ∈ Finset.range n,
        width (divNat (oddLoop square ul uh j).power (2*j+1)) := by
  induction n with
  | zero => simp [oddLoop, oddStart, width_raw]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simpa only [oddLoop, oddStep, width_add, ih]

/-- Uniform local rounding loss over all n odd divisions is at most
2*n ulps; the remaining terms are widths of the actual rounded powers. -/
theorem oddLoop_total_width_le (square : I80) (ul uh : ℤ) (n : ℕ) :
    width (oddLoop square ul uh n).total ≤
      ∑ j ∈ Finset.range n,
        (width (oddLoop square ul uh j).power / ((2*j+1 : ℕ) : ℝ) + 2*ulp) := by
  rw [oddLoop_total_width]
  apply Finset.sum_le_sum
  intro j hj
  exact (divNat_width _ (by omega : 0 < 2*j+1)).le

def sourceTail (ul uh : ℤ) : ℤ :=
  let square := oddSquare ul uh
  let state := oddLoop square ul uh 32
  ceilDiv (2*state.power.hi*(Q : ℤ)) (65*((Q : ℤ)-square.hi))

/-- The tail remains its literal integer expression, including divisor 65. -/
theorem atanhBounds_width (ul uh : ℤ) :
    width (atanhBounds ul uh) =
      2*width (oddLoop (oddSquare ul uh) ul uh 32).total +
        decode (sourceTail ul uh) := by
  simp only [width, atanhBounds, sourceTail, decode_add, decode_mul_int,
    Int.cast_ofNat]
  ring

/-- Negative shifts reverse endpoints, hence the absolute value. -/
theorem integerScale_width (x : I80) (k : ℤ) :
    width (integerScale x k) = |(k : ℝ)|*width x := by
  by_cases hk : 0 ≤ k
  · have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk
    simp only [integerScale, if_pos hk, width, decode_mul_int,
      abs_of_nonneg hkr]
    ring
  · have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hk)
    simp only [integerScale, if_neg hk, width, decode_mul_int,
      abs_of_nonpos hkr]
    ring

theorem logPointFromReduction_width (k rl rh : ℤ) :
    width (logPointFromReduction k rl rh) =
      width (reducedLogBounds rl rh) + |(k : ℝ)|*width logTwoBounds := by
  rw [logPointFromReduction, width_add, integerScale_width]

theorem logPoint_width_of_ne {q : ℤ} (hq : q ≠ (Q : ℤ)) :
    width (logPoint q) =
      width (reducedLogBounds (P2HistoricLogRangeReduction.sourceRL q)
        (P2HistoricLogRangeReduction.sourceRH q)) +
      |(P2HistoricLogRangeReduction.sourceShift q : ℝ)|*width logTwoBounds := by
  rw [logPoint, if_neg hq, logPointFromReduction_width]

/-- Directed true-log errors are bounded by the propagated actual width. -/
theorem logPoint_endpoint_errors {q : ℤ} (hq : 0 < q) :
    (0 ≤ Real.log ((q : ℝ)/(Q : ℝ)) - decode (logPoint q).lo ∧
      Real.log ((q : ℝ)/(Q : ℝ)) - decode (logPoint q).lo ≤ width (logPoint q)) ∧
    (0 ≤ decode (logPoint q).hi - Real.log ((q : ℝ)/(Q : ℝ)) ∧
      decode (logPoint q).hi - Real.log ((q : ℝ)/(Q : ℝ)) ≤ width (logPoint q)) := by
  obtain ⟨hl,hu⟩ := (contains_iff _ _).1 (logPoint_contains hq)
  dsimp only [width]
  constructor <;> constructor <;> linarith

end
end ImbalancedChen.Certificates.P2HistoricLogWidthPropagation
