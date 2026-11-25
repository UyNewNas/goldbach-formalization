import ImbalancedChen.P2OriginalCompactQ80Leaf

/-!
SOURCE ONLY / UNCOMPILED.
Uniform original Jensen logarithm-division guards from the actual raw box.
No logarithm-width estimate or positive rounded log endpoint is assumed.
Integer width>=1 and raw upper<=rho imply log(I(hi/lo)).lo>=2^40;
therefore both log denominators and the rounded squared-log denominator are
strictly positive. The proof follows the first source atanh summand and the
literal bit-length branch, not a different logarithm implementation.
-/
namespace ImbalancedChen.P2OriginalCompactQ80LogGuardsSourceOnly

noncomputable section
open Certificates.P2HistoricQ80DefectLookup
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open P2OriginalCompactQ80LeafSourceOnly

def logMinimum : ℤ := 2^40
def rawLogBump : ℤ := 2^42

theorem logMinimum_positive : 0 < logMinimum := by norm_num [logMinimum]

theorem logLoop_total_ge_initial (sq : I80) (ul uh : ℤ) (n : ℕ)
    (hul : 0 ≤ ul) (hsq : 0 ≤ sq.lo) (hn : 1 ≤ n) :
    ul ≤ (logLoop sq ul uh n).total.lo := by
  revert hn
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
      intro hn
      cases n with
      | zero => simp [logLoop,logStep,I80.add,I80.raw]
      | succ m =>
          have hp := (logLoop_lower_nonnegative sq ul uh (m+1) hul hsq).1
          have hadd : (logLoop sq ul uh (m+1)).total.lo ≤
              (logLoop sq ul uh (m+1)).total.lo+
                (logLoop sq ul uh (m+1)).power.lo/((2*(m+1)+1 : ℕ) : ℤ) :=
            le_add_of_nonneg_right (Int.ediv_nonneg hp (by positivity))
          exact (ih (by omega)).trans hadd

theorem atanh_lower_ge_initial (ul uh : ℤ) (hul : 0 ≤ ul) :
    ul ≤ (atanhBounds ul uh).lo := by
  have hs : 0 ≤ (logSquare ul uh).lo :=
    Int.ediv_nonneg (mul_nonneg hul hul) scale_pos.le
  have ht := logLoop_total_ge_initial (logSquare ul uh) ul uh 32 hul hs (by omega)
  change ul ≤ 2*(logLoop (logSquare ul uh) ul uh 32).total.lo
  omega

theorem logTwo_lower_ge_minimum : logMinimum ≤ logTwo.lo := by
  have hq : logMinimum*3 ≤ scale := by norm_num [logMinimum,scale]
  have hl : logMinimum ≤ scale/3 := Int.le_ediv_of_mul_le (by norm_num) hq
  exact hl.trans (atanh_lower_ge_initial (scale/3) (up scale 3)
    (Int.ediv_nonneg scale_pos.le (by norm_num)))

/-- A sufficient raw argument margin, supplied below for every source box. -/
theorem logPoint_lower_ge_minimum (q : ℤ) (hq : scale+rawLogBump ≤ q) :
    logMinimum ≤ (logPoint q).lo := by
  have hB : 0 < rawLogBump := by norm_num [rawLogBump]
  have hqQ : scale ≤ q := by omega
  have hp : 0 < q := scale_pos.trans_le hqQ
  have hne : q ≠ scale := by omega
  have hk := sourceShift_nonnegative hqQ
  have hguards := Certificates.P2HistoricLogRangeReduction.source_endpoint_guards hp
  have hrL : scale ≤ Certificates.P2HistoricLogRangeReduction.sourceRL q := hguards.1
  have hrH : scale ≤ Certificates.P2HistoricLogRangeReduction.sourceRH q := hguards.1.trans hguards.2.1
  have hu : 0 ≤ (Certificates.P2HistoricLogRangeReduction.sourceRL q-scale)*scale/
      (Certificates.P2HistoricLogRangeReduction.sourceRH q+scale) :=
    Int.ediv_nonneg (mul_nonneg (sub_nonneg.mpr hrL) scale_pos.le)
      (by linarith only [hrH,scale_pos])
  by_cases hk0 : Certificates.P2HistoricLogRangeReduction.sourceShift q = 0
  · have he : Certificates.P2HistoricLogRangeReduction.binaryExponent q = 80 := by
      unfold Certificates.P2HistoricLogRangeReduction.sourceShift at hk0
      omega
    have hq2 : q < 2*scale := by
      have hh := (Certificates.P2HistoricLogRangeReduction.binaryExponent_bounds hp).2
      rw [he] at hh
      have hhZ : (q.toNat : ℤ) < (2 : ℤ)^81 := by exact_mod_cast hh
      rw [Int.toNat_of_nonneg hp.le] at hhZ
      simpa only [scale,show (81 : ℕ)=80+1 by omega,pow_succ,mul_comm] using hhZ
    have hdelta : 4*logMinimum ≤ q-scale := by
      have heB : rawLogBump = 4*logMinimum := by norm_num [rawLogBump,logMinimum]
      rw [heB] at hq
      omega
    have hden : 0 < q+scale := by omega
    have hnum : logMinimum*(q+scale) ≤ (q-scale)*scale := by
      calc
        logMinimum*(q+scale) ≤ logMinimum*(3*scale) :=
          mul_le_mul_of_nonneg_left (by omega) logMinimum_positive.le
        _ ≤ (4*logMinimum)*scale := by nlinarith only [logMinimum_positive,scale_pos]
        _ ≤ (q-scale)*scale := mul_le_mul_of_nonneg_right hdelta scale_pos.le
    have hul : logMinimum ≤ (q-scale)*scale/(q+scale) := Int.le_ediv_of_mul_le hden hnum
    have hlo := hul.trans (atanh_lower_ge_initial ((q-scale)*scale/(q+scale))
      (up ((q-scale)*scale) (q+scale)) (logMinimum_positive.le.trans hul))
    simpa [logPoint,hne,hk0,Certificates.P2HistoricLogRangeReduction.sourceRL,
      Certificates.P2HistoricLogRangeReduction.sourceRH,I80.add] using hlo
  · have hk1 : 1 ≤ Certificates.P2HistoricLogRangeReduction.sourceShift q := by omega
    have htwo := logTwo_lower_ge_minimum
    have ht0 : 0 ≤ logTwo.lo := logMinimum_positive.le.trans htwo
    have hscaled : logMinimum ≤ Certificates.P2HistoricLogRangeReduction.sourceShift q*logTwo.lo :=
      htwo.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hk1 ht0)
    have ha0 := atanh_lower_nonnegative
      ((Certificates.P2HistoricLogRangeReduction.sourceRL q-scale)*scale/
        (Certificates.P2HistoricLogRangeReduction.sourceRH q+scale))
      (up ((Certificates.P2HistoricLogRangeReduction.sourceRH q-scale)*scale)
        (Certificates.P2HistoricLogRangeReduction.sourceRL q+scale)) hu
    simp only [logPoint,if_neg hne,if_pos hk,I80.add]
    linarith only [hscaled,ha0]

theorem ratio_point_raw_margin (box : RawBox) (g : Geometry box) (i : Fin 3) :
    scale+rawLogBump ≤ (I80.point ((box.2 i : ℚ)/(box.1 i : ℚ))).lo := by
  have hl := g.raw_positive i
  have hwidth : box.1 i+1 ≤ box.2 i := by have h := g.width i; omega
  have hupper : box.1 i ≤ rhoInteger := (g.width i).le.trans (g.upper i)
  have hB0 : 0 ≤ rawLogBump := by norm_num [rawLogBump]
  have hBbound : rawLogBump*rhoInteger ≤ scale := by norm_num [rawLogBump,rhoInteger,scale]
  have hB : rawLogBump*box.1 i ≤ scale :=
    (mul_le_mul_of_nonneg_left hupper hB0).trans hBbound
  have hcross : (scale+rawLogBump)*box.1 i ≤ box.2 i*scale := by
    calc
      (scale+rawLogBump)*box.1 i = box.1 i*scale+rawLogBump*box.1 i := by ring
      _ ≤ box.1 i*scale+scale := add_le_add_left hB _
      _ = (box.1 i+1)*scale := by ring
      _ ≤ box.2 i*scale := mul_le_mul_of_nonneg_right hwidth scale_pos.le
  change scale+rawLogBump ≤ ⌊((box.2 i : ℚ)/(box.1 i : ℚ))*(Q : ℚ)⌋
  apply Int.le_floor.mpr
  have hlQ : (0 : ℚ) < box.1 i := by exact_mod_cast hl
  change ((scale+rawLogBump : ℤ) : ℚ) ≤ ((box.2 i : ℚ)/(box.1 i : ℚ))*(scale : ℚ)
  have he : ((box.2 i : ℚ)/(box.1 i : ℚ))*(scale : ℚ) =
      ((box.2 i : ℚ)*(scale : ℚ))/(box.1 i : ℚ) := by ring
  rw [he]
  apply (le_div_iff₀ hlQ).2
  exact_mod_cast hcross

theorem logarithmicWidth_lower_ge_minimum (box : RawBox) (g : Geometry box) (i : Fin 3) :
    logMinimum ≤ (logarithmicWidth (box.1 i) (box.2 i)).lo :=
  logPoint_lower_ge_minimum _ (ratio_point_raw_margin box g i)

theorem logarithmicWidth_lower_positive (box : RawBox) (g : Geometry box) (i : Fin 3) :
    0 < (logarithmicWidth (box.1 i) (box.2 i)).lo :=
  logMinimum_positive.trans_le (logarithmicWidth_lower_ge_minimum box g i)

theorem logarithmicWidth_square_lower_positive (box : RawBox) (g : Geometry box) (i : Fin 3) :
    0 < ((logarithmicWidth (box.1 i) (box.2 i)).mul
      (logarithmicWidth (box.1 i) (box.2 i))).lo := by
  let lx := logarithmicWidth (box.1 i) (box.2 i)
  have hB : logMinimum ≤ lx.lo := logarithmicWidth_lower_ge_minimum box g i
  have hlo : 0 ≤ lx.lo := logMinimum_positive.le.trans hB
  have hc := (logarithmicWidth_contains _ _ (g.raw_positive i) (g.width i).le).1
  have hval := ((contains_iff lx _).1 hc).1.trans ((contains_iff lx _).1 hc).2
  have hord : lx.lo ≤ lx.hi := by
    have hh := (div_le_div_iff_of_pos_right scale_real_pos).1 hval
    exact_mod_cast hh
  have hscale : scale = logMinimum*logMinimum := by norm_num [scale,logMinimum]
  have hll : scale ≤ lx.lo*lx.lo := by
    rw [hscale]
    exact mul_le_mul hB hB logMinimum_positive.le hlo
  have hlh : scale ≤ lx.lo*lx.hi := hll.trans (mul_le_mul_of_nonneg_left hord hlo)
  have hhl : scale ≤ lx.hi*lx.lo := by simpa only [mul_comm] using hlh
  have hhh : scale ≤ lx.hi*lx.hi :=
    hlh.trans (mul_le_mul_of_nonneg_right hord (hlo.trans hord))
  have hdiv (n : ℤ) (hn : scale ≤ n) : (1 : ℤ) ≤ n/(Q : ℤ) :=
    Int.le_ediv_of_mul_le scale_pos (by simpa only [one_mul] using hn)
  have hmin : (1 : ℤ) ≤ min (min (lx.lo*lx.lo/(Q : ℤ)) (lx.lo*lx.hi/(Q : ℤ)))
      (min (lx.hi*lx.lo/(Q : ℤ)) (lx.hi*lx.hi/(Q : ℤ))) :=
    le_min (le_min (hdiv _ hll) (hdiv _ hlh)) (le_min (hdiv _ hhl) (hdiv _ hhh))
  rw [I80.mul_lo_integer]
  exact (by norm_num : (0 : ℤ)<1).trans_le hmin

end
end ImbalancedChen.P2OriginalCompactQ80LogGuardsSourceOnly
