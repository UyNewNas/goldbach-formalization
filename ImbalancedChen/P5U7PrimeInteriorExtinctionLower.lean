import ImbalancedChen.P5U7PrimeQuadraticExtinction

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A genuine shrinking interior interval for the actual prime cutoff near
extinction, and an explicit lower log-row amplitude. The logarithm lower
bound is the proved primary one_sub_inv_le_log_of_pos; positivity and all
support/denominator comparisons are supplied from the actual geometry.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

def p5U7PrimeExtinctionInteriorEnd (eta : ℝ) : ℝ :=
  (59/250 : ℝ)+((59/250 : ℝ)^2/2)*((73/59 : ℝ)-eta)

theorem p5U7PrimeExtinction_support_width_lower {eta : ℝ}
    (heta : 0 ≤ eta) (hetaH : eta ≤ (73/59 : ℝ)) :
    (59/250 : ℝ)^2*((73/59 : ℝ)-eta) ≤ 1/(3+eta)-(59/250 : ℝ) := by
  have he3 : 0 < 3+eta := by linarith
  have hdelta : 0 ≤ (73/59 : ℝ)-eta := sub_nonneg.mpr hetaH
  have hid : 1/(3+eta)-(59/250 : ℝ) =
      ((59/250 : ℝ)*((73/59 : ℝ)-eta))/(3+eta) := by
    field_simp [he3.ne']
    <;> ring
  rw [hid]
  have hh := div_le_div_of_nonneg_left
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 59/250) hdelta) he3
    (show 3+eta ≤ (250/59 : ℝ) by nlinarith only [hetaH])
  convert hh using 1 <;> ring

/-- Half the explicit support-width lower reserve supplies a real closed
interior interval, valid even at the degenerate extinction endpoint. -/
theorem p5U7PrimeExtinction_interior_interval {eta : ℝ}
    (heta : 0 ≤ eta) (hetaH : eta ≤ (73/59 : ℝ)) :
    (59/250 : ℝ) ≤ p5U7PrimeExtinctionInteriorEnd eta ∧
      p5U7PrimeExtinctionInteriorEnd eta ≤ 1/(3+eta) ∧
      1/(3+eta) ≤ (1/3 : ℝ) := by
  have hdelta : 0 ≤ (73/59 : ℝ)-eta := sub_nonneg.mpr hetaH
  have hl := p5U7PrimeExtinction_support_width_lower heta hetaH
  have hu := p5U7PrimeExtinction_support_width heta hetaH
  dsimp only [p5U7PrimeExtinctionInteriorEnd]
  have hnonneg : 0 ≤ ((59/250 : ℝ)^2/2)*((73/59 : ℝ)-eta) := by positivity
  exact ⟨by linarith only [hnonneg],by nlinarith only [hl,hdelta],hu.2.1⟩

/-- Matching positive lower amplitude on the actual shrinking interior.
The fixed valid left neighborhood is H-1<=eta<=H, H=73/59. -/
theorem p5U7PrimeExtinction_interior_log_lower {eta t : ℝ}
    (hetaL : (73/59 : ℝ)-1 ≤ eta) (hetaH : eta ≤ (73/59 : ℝ))
    (ht : t ∈ Icc (59/250 : ℝ) (p5U7PrimeExtinctionInteriorEnd eta)) :
    ((59/250 : ℝ)^2/2)*((73/59 : ℝ)-eta) ≤ p5U7PrimeCutoffLogRow eta t := by
  have heta : 0 ≤ eta := by linarith only [hetaL]
  have hdelta : 0 ≤ (73/59 : ℝ)-eta := sub_nonneg.mpr hetaH
  have he3 : 0 < 3+eta := by linarith
  have he1 : 0 < 1+eta := by linarith
  have hi := p5U7PrimeExtinction_interior_interval heta hetaH
  have htI : t ∈ Icc (59/250 : ℝ) (1/3) := ⟨ht.1,ht.2.trans (hi.2.1.trans hi.2.2)⟩
  have ht0 : 0 < t := by linarith [ht.1]
  have hg := p5U7PrimeCutoffLog_geometry heta htI
  let R : ℝ := (1-2*t)/(t*(1+eta))
  let D : ℝ := ((59/250 : ℝ)^2/2)*((73/59 : ℝ)-eta)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hgap : D ≤ 1/(3+eta)-t := by
    have hw := p5U7PrimeExtinction_support_width_lower heta hetaH
    dsimp only [p5U7PrimeExtinctionInteriorEnd] at ht
    dsimp only [D]
    nlinarith only [hw,ht.2]
  have hres : (59/250 : ℝ)^2*((73/59 : ℝ)-eta) ≤ 1-t*(3+eta) := by
    have hmul := mul_le_mul_of_nonneg_left hgap he3.le
    have hbase := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ 3+eta by linarith) hD
    have heq : (3+eta)*(1/(3+eta)-t) = 1-t*(3+eta) := by
      field_simp [he3.ne']
      <;> ring
    rw [heq] at hmul
    dsimp only [D] at hbase hmul
    nlinarith only [hbase,hmul]
  have hqpos : 0 < t*(1+eta) := mul_pos ht0 he1
  have hqUpper : t*(1+eta) ≤ 1 := by
    have hh := mul_le_mul htI.2 (show 1+eta ≤ (3 : ℝ) by nlinarith only [hetaH])
      he1.le (by norm_num : (0 : ℝ) ≤ 1/3)
    nlinarith only [hh]
  have hqLower : (59/250 : ℝ)*(73/59 : ℝ) ≤ t*(1+eta) :=
    mul_le_mul ht.1 (by linarith only [hetaL]) (by norm_num) ht0.le
  have hRupper : R ≤ 2 := by
    apply (div_le_iff₀ hqpos).mpr
    nlinarith only [hqLower,ht.1]
  have hRpos : 0 < R := hg.1
  have hid : R-1 = (1-t*(3+eta))/(t*(1+eta)) := by
    dsimp only [R]
    field_simp [hqpos.ne']
    <;> ring
  have hv : (59/250 : ℝ)^2*((73/59 : ℝ)-eta) ≤ R-1 := by
    rw [hid]
    apply (le_div_iff₀ hqpos).mpr
    have hh := mul_le_mul_of_nonneg_left hqUpper
      (show 0 ≤ (59/250 : ℝ)^2*((73/59 : ℝ)-eta) by positivity)
    nlinarith only [hh,hres]
  have hv0 : 0 ≤ R-1 := (by positivity : 0 ≤ (59/250 : ℝ)^2*((73/59 : ℝ)-eta)).trans hv
  have hlog : (R-1)/R ≤ Real.log R := by
    have hh := Real.one_sub_inv_le_log_of_pos hRpos
    have heq : (R-1)/R = 1-R⁻¹ := by field_simp [hRpos.ne']; ring
    rwa [← heq] at hh
  have hhalf : (R-1)/2 ≤ (R-1)/R :=
    div_le_div_of_nonneg_left hv0 hRpos hRupper
  have hamp : D ≤ Real.log R := by
    dsimp only [D]
    nlinarith only [hv,hhalf,hlog]
  have hdenUpper : t*(1-t) ≤ 1 := by nlinarith [sq_nonneg t,htI.2]
  have hdenScale := mul_le_mul_of_nonneg_left hdenUpper hD
  change D ≤ Real.log R/(t*(1-t))
  exact (le_div_iff₀ hg.2).mpr (by nlinarith only [hdenScale,hamp])
end
end ImbalancedChen

