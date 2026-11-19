import ImbalancedChen.P1OriginalFourthRowGap

/-! The manuscript's four separate floors on each literal rectangle.
The unrounded expression is written in physical rational coordinates;
the affine/coordinate denominators cancel to the producer's 16 D
times the integer gap and the product of the four integer widths. -/
namespace ImbalancedChen.P1OriginalFourthRowQ80Integral
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness P2OriginalFourthCapProducerInterface
open P1OriginalFourthN8193 P1OriginalFourthFourSubintervals P1OriginalFourthRowSubintervals
open P1OriginalFourthCornerIntegration P1OriginalFourthRowGap
open P5OriginalFourthFifthSourceInputs P1OriginalFourthAllRowsAdmission
open OriginalU2CoupledRecurrenceSourceOnly (upper)

def volumeQ (r : FourthWireRow) : ℚ := ∏ i, r.toProducerRow.upper i-r.toProducerRow.lower i
def productQ (r : FourthWireRow) : ℚ := ∏ i, r.toProducerRow.upper i
def unitExpr (lookup : ℕ → ℕ) (r : FourthWireRow) (k : Fin 4) : ℚ :=
  volumeQ r*((averageUnits r:ℚ)/6553600)/productQ r *
    (lookup (ceilIndex (argument r k)):ℚ)/
      (qBlend (R0 r) (R1 r) k.val * qBlend (R0 r) (R1 r) (k.val+1))
def rowUnits (lookup : ℕ → ℕ) (r : FourthWireRow) : ℤ := ∑ k, ⌊unitExpr lookup r k⌋
def density (r : FourthWireRow) (t : Point) : ℝ :=
  4*(upper ((oldCap t-total t)/t 3)-upper ((r.toProducerRow.candidate t-total t)/t 3))/
    (t 0*t 1*t 2*(t 3)^2)
def weightSum (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) : ℝ :=
  ∑ k, segmentWeight (R0 r:ℝ) (R1 r:ℝ) (rowIndex r hr) k
def factor (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) : ℝ :=
  4/(∏ i, right r i)*weightSum r hr
def limitingRowIntegral (r : FourthWireRow) : ℝ := ∫ t in box r, density r t

private theorem coord_pos (r : FourthWireRow) (hr : r ∈ originalFourthWireRows)
    (t : Point) (ht : t ∈ r.toProducerRow.box) (i : Fin 4) : 0 < t i := by
  have h := r.toProducerRow.ordered (all_original_rows_geometry r hr) t ht
  fin_cases i <;> linarith only [h.2.1,h.2.2,h.1.2.1,h.1.2.2.1]

theorem right_pos (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) (i : Fin 4) : 0 < right r i :=
  coord_pos r hr (right r) ⟨fun i => (width r hr i).le,fun _ => le_rfl⟩ i

theorem weightSum_nonneg (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) : 0 ≤ weightSum r hr := by
  obtain ⟨h0,h01,_⟩ := R_range r hr
  have h0R : (0:ℝ) < (R0 r:ℝ) := by exact_mod_cast h0
  have h01R : (R0 r:ℝ) ≤ (R1 r:ℝ) := by exact_mod_cast h01
  apply Finset.sum_nonneg
  intro k _
  have hl := h0R.trans_le (blend_bounds h01R (show k.val ≤ 4 by omega)).1
  have hu := h0R.trans_le (blend_bounds h01R (show k.val+1 ≤ 4 by omega)).1
  exact div_nonneg (credit_nonneg _) (by positivity)

theorem factor_nonneg (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) : 0 ≤ factor r hr :=
  mul_nonneg (div_nonneg (by norm_num) (Finset.prod_nonneg (fun i _ => (right_pos r hr i).le)))
    (weightSum_nonneg r hr)

theorem density_integrable (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) :
    IntegrableOn (density r) (box r) := by
  have hc : ContinuousOn (density r) (Icc (left r) (right r)) := by
    intro t ht
    have hg := r.toProducerRow.residual_range (all_original_rows_geometry r hr) t ht
    have hx := coord_pos r hr t ht
    have hs : Continuous total := by unfold total; fun_prop
    have h0 := (upper_differentiable hg.1).continuousAt.comp
      ((old_continuous.sub hs).continuousAt.div (continuous_apply (3:Fin 4)).continuousAt (hx 3).ne')
    have h1 := (upper_differentiable (hg.1.trans hg.2.1)).continuousAt.comp
      (((candidate_continuous r).sub hs).continuousAt.div (continuous_apply (3:Fin 4)).continuousAt (hx 3).ne')
    have hd : Continuous (fun u : Point => u 0*u 1*u 2*(u 3)^2) := by fun_prop
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_const.mul (h0.sub h1)).div hd.continuousAt
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (hx 0).ne' (hx 1).ne') (hx 2).ne') (pow_ne_zero 2 (hx 3).ne'))
  exact (hc.integrableOn_compact isCompact_Icc).mono_set (box_subset r)

theorem gap_times_factor_le (r : FourthWireRow) (hr : r ∈ originalFourthWireRows)
    (t : Point) (ht : t ∈ r.toProducerRow.box) : gap r t*factor r hr ≤ density r t := by
  have hg : 0 ≤ gap r t := sub_nonneg.mpr (r.toProducerRow.geometry_sound
    (all_original_rows_geometry r hr) t ht).2.1.le
  have hp (i : Fin 4) := coord_pos r hr t ht i
  have hden : (∏ i, t i) ≤ ∏ i, right r i :=
    Finset.prod_le_prod (fun i _ => (hp i).le) (fun i _ => ht.2 i)
  have hh := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hg)
    (Finset.prod_pos (fun i _ => hp i)) hden
  have h := mul_le_mul_of_nonneg_right hh (weightSum_nonneg r hr)
  calc
    _ = (4*gap r t/(∏ i, right r i))*weightSum r hr := by unfold factor; ring
    _ ≤ _ := h
    _ = (4*gap r t/(t 0*t 1*t 2*t 3))*weightSum r hr := by
      simp [Fin.prod_univ_succ,mul_assoc]
    _ ≤ _ := original_row_density r hr t ht

theorem unitExpr_cast (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) (k : Fin 4) :
    (unitExpr stored r k:ℝ)/2^80 =
      (vol (left r) (right r)*((averageUnits r:ℝ)/6553600)) *
        (4/(∏ i, right r i))*segmentWeight (R0 r:ℝ) (R1 r:ℝ) (rowIndex r hr) k := by
  have hV : (volumeQ r:ℝ) = vol (left r) (right r) := by simp [volumeQ,vol,left,right]
  have hP : (productQ r:ℝ) = (∏ i, right r i) := by simp [productQ,right]
  obtain ⟨h0,h01,_⟩ := R_range r hr
  have h0R : (0:ℝ) < (R0 r:ℝ) := by exact_mod_cast h0
  have h01R : (R0 r:ℝ) ≤ (R1 r:ℝ) := by exact_mod_cast h01
  have hL := h0R.trans_le (blend_bounds h01R (show k.val ≤ 4 by omega)).1
  have hU := h0R.trans_le (blend_bounds h01R (show k.val+1 ≤ 4 by omega)).1
  have hD : 0 < (∏ i, right r i) := Finset.prod_pos (fun i _ => right_pos r hr i)
  simp only [unitExpr,Rat.cast_div,Rat.cast_mul,Rat.cast_intCast,Rat.cast_ofNat,Rat.cast_natCast,
    hV,hP,qBlend_cast,segmentWeight,credit,rowIndex]
  field_simp [hD.ne',hL.ne',hU.ne'] <;> ring

/-- All original per-row floors, compared to the true fourth density
on their own half-open physical rectangles. -/
theorem original_row_floor (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) :
    (rowUnits stored r:ℝ)/2^80 ≤ limitingRowIntegral r := by
  have hQ : 0 ≤ (2:ℝ)^80 := by positivity
  have hf (k : Fin 4) : ((⌊unitExpr stored r k⌋:ℤ):ℝ)/2^80 ≤ (unitExpr stored r k:ℝ)/2^80 :=
    div_le_div_of_nonneg_right (by exact_mod_cast (Int.floor_le (unitExpr stored r k))) hQ
  have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun k _ => hf k)
  simp only [unitExpr_cast r hr] at h1
  rw [← Finset.sum_div,← Finset.mul_sum] at h1
  have hs : (rowUnits stored r:ℝ)/2^80 ≤
      (vol (left r) (right r)*((averageUnits r:ℝ)/6553600))*factor r hr := by
    simpa only [rowUnits,Int.cast_sum,weightSum,factor,mul_assoc] using h1
  have hg := mul_le_mul_of_nonneg_right (original_average_gap r hr) (factor_nonneg r hr)
  have hd := setIntegral_mono_on ((gap_integrable r).mul_const (factor r hr)) (density_integrable r hr)
    (measurableSet_logPrimeBox (left r) (right r)) (fun t ht => gap_times_factor_le r hr t (box_subset r ht))
  rw [integral_mul_const] at hd
  exact hs.trans (hg.trans hd)

end
end ImbalancedChen.P1OriginalFourthRowQ80Integral
