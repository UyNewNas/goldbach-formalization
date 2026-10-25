import ImbalancedChen.P2HistoricReducedParameterWidth

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

For j<=32 the dyadic ceiling Q/2^(2*j+1) is an integer. Therefore every
literal ceil-divided upper power remains below that dyadic ceiling. This
is an induction on the source operation tree, not evaluation of its state.
At j=32 the exponent is 65, exactly the exponent used by the original
tail with divisor 65. The tail is nonnegative and at most 2^11 Q80 units.
No actual rounded producer outputs are computed or taken as hypotheses.
-/

namespace ImbalancedChen.Certificates.P2HistoricLogDyadicPowerTail

noncomputable section
open P2HistoricQ80DefectLookup P2HistoricLogPointInterpreter
open P2HistoricLogWidthPropagation P2HistoricReducedParameterWidth

def dyadicPowerCeiling (j : ℕ) : ℤ := (2 : ℤ)^(79-2*j)

theorem dyadicPowerCeiling_nonneg (j : ℕ) : 0 ≤ dyadicPowerCeiling j := by
  unfold dyadicPowerCeiling
  positivity

theorem dyadicPowerCeiling_zero : dyadicPowerCeiling 0 = (Q : ℤ)/2 := by
  norm_num [dyadicPowerCeiling,Q]

theorem dyadicPowerCeiling_succ {j : ℕ} (hj : j < 32) :
    4*dyadicPowerCeiling (j+1) = dyadicPowerCeiling j := by
  have he : 79-2*j = (79-2*(j+1))+2 := by omega
  unfold dyadicPowerCeiling
  rw [he,pow_add]
  norm_num
  ring

theorem dyadicPowerCeiling_32 : dyadicPowerCeiling 32 = (2 : ℤ)^15 := by
  unfold dyadicPowerCeiling
  congr 1

/-- The quarter cap includes the literal upward rounding of uh*uh/Q. -/
theorem oddSquare_hi_quarter {ul uh : ℤ}
    (hu0 : 0 ≤ uh) (hu : uh ≤ (Q : ℤ)/2) :
    0 ≤ (oddSquare ul uh).hi ∧ (oddSquare ul uh).hi ≤ (Q : ℤ)/4 := by
  let half : ℤ := (Q : ℤ)/2
  let quarter : ℤ := (Q : ℤ)/4
  have hh0 : 0 ≤ half := by norm_num [half,Q]
  have hqQ : quarter*(Q : ℤ) = half*half := by norm_num [quarter,half,Q]
  constructor
  · exact ceilDiv_nonnegative (mul_nonneg hu0 hu0) Q_int_pos
  · apply ceilDiv_le _ _ _ Q_int_pos
    have hsq := mul_le_mul hu hu hu0 hh0
    simpa only [hqQ] using hsq

theorem oddLoop_power_hi_nonneg {ul uh : ℤ} (hu : 0 ≤ uh) (n : ℕ) :
    0 ≤ (oddLoop (oddSquare ul uh) ul uh n).power.hi := by
  have hs : 0 ≤ (oddSquare ul uh).hi :=
    ceilDiv_nonnegative (mul_nonneg hu hu) Q_int_pos
  induction n with
  | zero => exact hu
  | succ n ih =>
      exact ceilDiv_nonnegative (mul_nonneg ih hs) Q_int_pos

/-- Genuine operation-tree induction. Divisibility, rather than omission
of the ceiling error, makes the exact dyadic upper bound possible. -/
theorem oddLoop_power_hi_le_dyadic {ul uh : ℤ}
    (hu0 : 0 ≤ uh) (hu : uh ≤ (Q : ℤ)/2) :
    ∀ n : ℕ, n ≤ 32 →
      (oddLoop (oddSquare ul uh) ul uh n).power.hi ≤ dyadicPowerCeiling n := by
  obtain ⟨hs0,hs⟩ := oddSquare_hi_quarter (ul := ul) hu0 hu
  have hquarter : 4*((Q : ℤ)/4) = (Q : ℤ) := by norm_num [Q]
  intro n
  induction n with
  | zero =>
      intro hn
      simpa only [oddLoop,oddStart,dyadicPowerCeiling_zero] using hu
  | succ n ih =>
      intro hn
      have hn32 : n < 32 := by omega
      have hp := ih (by omega : n ≤ 32)
      have he := dyadicPowerCeiling_succ hn32
      have hp' : (oddLoop (oddSquare ul uh) ul uh n).power.hi ≤
          4*dyadicPowerCeiling (n+1) := by simpa only [he] using hp
      change ceilDiv
        ((oddLoop (oddSquare ul uh) ul uh n).power.hi*(oddSquare ul uh).hi)
        (Q : ℤ) ≤ dyadicPowerCeiling (n+1)
      apply ceilDiv_le _ _ _ Q_int_pos
      have hm : 0 ≤ 4*dyadicPowerCeiling (n+1) := by
        exact mul_nonneg (by norm_num) (dyadicPowerCeiling_nonneg _)
      have hprod := mul_le_mul hp' hs hs0 hm
      have heq : (4*dyadicPowerCeiling (n+1))*((Q : ℤ)/4) =
          dyadicPowerCeiling (n+1)*(Q : ℤ) := by
        calc
          _ = dyadicPowerCeiling (n+1)*(4*((Q : ℤ)/4)) := by ring
          _ = _ := by rw [hquarter]
      exact hprod.trans_eq heq

theorem oddLoop_power_hi_32 {ul uh : ℤ}
    (hu0 : 0 ≤ uh) (hu : uh ≤ (Q : ℤ)/2) :
    (oddLoop (oddSquare ul uh) ul uh 32).power.hi ≤ (2 : ℤ)^15 := by
  simpa only [dyadicPowerCeiling_32] using
    oddLoop_power_hi_le_dyadic hu0 hu 32 (by omega)

theorem sourceTail_nonneg {ul uh : ℤ}
    (hu0 : 0 ≤ uh) (hu : uh ≤ (Q : ℤ)/2) :
    0 ≤ sourceTail ul uh := by
  obtain ⟨hs0,hs⟩ := oddSquare_hi_quarter (ul := ul) hu0 hu
  have hquarter : (Q : ℤ)/4 < (Q : ℤ) := by norm_num [Q]
  have hd : 0 < 65*((Q : ℤ)-(oddSquare ul uh).hi) := by omega
  have hp := oddLoop_power_hi_nonneg (ul := ul) hu0 32
  exact ceilDiv_nonnegative
    (mul_nonneg (mul_nonneg (by norm_num) hp) Q_int_pos.le) hd

/-- The denominator is positive with its original direction: increasing
square.hi makes the tail larger. The literal integer tail is bounded here. -/
theorem sourceTail_le_two_pow_eleven {ul uh : ℤ}
    (hu0 : 0 ≤ uh) (hu : uh ≤ (Q : ℤ)/2) :
    sourceTail ul uh ≤ (2 : ℤ)^11 := by
  obtain ⟨hs0,hs⟩ := oddSquare_hi_quarter (ul := ul) hu0 hu
  have hquarter : (Q : ℤ)/4 < (Q : ℤ) := by norm_num [Q]
  have hd : 0 < 65*((Q : ℤ)-(oddSquare ul uh).hi) := by omega
  have hp := oddLoop_power_hi_32 (ul := ul) hu0 hu
  change ceilDiv (2*(oddLoop (oddSquare ul uh) ul uh 32).power.hi*(Q : ℤ))
    (65*((Q : ℤ)-(oddSquare ul uh).hi)) ≤ (2 : ℤ)^11
  apply ceilDiv_le _ _ _ hd
  have hnum := mul_le_mul_of_nonneg_right hp Q_int_pos.le
  have hden := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℤ) ≤ (2 : ℤ)^11*65)
  have hpure : 2*(2 : ℤ)^15*(Q : ℤ) ≤
      (2 : ℤ)^11*65*((Q : ℤ)-(Q : ℤ)/4) := by norm_num [Q]
  nlinarith only [hnum,hden,hpure]

def sourcePower (q : ℤ) (n : ℕ) : I80 :=
  (oddLoop (oddSquare (sourceParameter q).lo (sourceParameter q).hi)
    (sourceParameter q).lo (sourceParameter q).hi n).power

/-- The actual original positive integer query supplies all cap inputs. -/
theorem sourcePower_hi_bounds {q : ℤ} (hq : 0 < q) (n : ℕ) (hn : n ≤ 32) :
    0 ≤ (sourcePower q n).hi ∧ (sourcePower q n).hi ≤ dyadicPowerCeiling n := by
  obtain ⟨hl,ho,hu,hs⟩ := sourceParameter_caps hq
  have hu0 : 0 ≤ (sourceParameter q).hi := hl.trans ho
  exact ⟨oddLoop_power_hi_nonneg hu0 n, oddLoop_power_hi_le_dyadic hu0 hu n hn⟩

theorem actual_sourceTail_bounds {q : ℤ} (hq : 0 < q) :
    0 ≤ sourceTail (sourceParameter q).lo (sourceParameter q).hi ∧
      sourceTail (sourceParameter q).lo (sourceParameter q).hi ≤ (2 : ℤ)^11 := by
  obtain ⟨hl,ho,hu,hs⟩ := sourceParameter_caps hq
  have hu0 : 0 ≤ (sourceParameter q).hi := hl.trans ho
  exact ⟨sourceTail_nonneg hu0 hu,sourceTail_le_two_pow_eleven hu0 hu⟩

/-- The scaled tail payment belongs to Q80, not to P=2^160 or W=2^224. -/
theorem actual_sourceTail_decode_bounds {q : ℤ} (hq : 0 < q) :
    0 ≤ decode (sourceTail (sourceParameter q).lo (sourceParameter q).hi) ∧
      decode (sourceTail (sourceParameter q).lo (sourceParameter q).hi) ≤
        ((2 : ℤ)^11 : ℝ)*ulp := by
  obtain ⟨hl,hu⟩ := actual_sourceTail_bounds hq
  constructor
  · exact div_nonneg (by exact_mod_cast hl) Q_real_pos.le
  · have hh := div_le_div_of_nonneg_right
      (show (sourceTail (sourceParameter q).lo (sourceParameter q).hi : ℝ) ≤
        ((2 : ℤ)^11 : ℝ) by exact_mod_cast hu) Q_real_pos.le
    simpa only [decode,ulp,mul_one_div] using hh

end
end ImbalancedChen.Certificates.P2HistoricLogDyadicPowerTail
