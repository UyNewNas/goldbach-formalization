import ImbalancedChen.ActualThirdOriginalPositive256Log

/-!
SOURCEONLY / HOLD_ELABORATION / OPEN30.
Original positive256 log divisor guards on the literal above-mu coordinate
grid D=48000*2^24. P160, all256 loop operations, integer floor/UP and the
original four-product multiplication are inherited without alteration.
The proof uses the first rounded series term; later lower terms are >=0.
The auxiliary2^80 threshold is exactly sqrt(P160), not a new precision or
algorithmic constant. It supplies BOTH rawln.lo>0 and (rawln*rawln).lo>0.
-/

namespace ImbalancedChen.OriginalThirdPositiveLogSourceOnly
noncomputable section
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly

private theorem loop_power_hi_nonneg (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ (loop z n).1.hi := by
  have h : 0 ≤ value (loop z n).1.hi :=
    (pow_nonneg hz (n+1)).trans (loop_sound z n).1.2
  exact value_le_iff.mp (by simpa only [value_zero] using h)

private theorem loop_power_lo_nonneg (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ (loop z n).1.lo := by
  have hzlo : 0 ≤ (ofReal z).lo :=
    Int.floor_nonneg.mpr (mul_nonneg hz P160_real_pos.le)
  have hzhi : 0 ≤ (ofReal z).hi := by
    simpa only [loop] using loop_power_hi_nonneg z hz 0
  induction n with
  | zero => exact hzlo
  | succ n ih =>
    have hpowerhi := loop_power_hi_nonneg z hz n
    have hfour : 0 ≤ fourLo (loop z n).1 (ofReal z) := by
      exact le_min (le_min (mul_nonneg ih hzlo) (mul_nonneg ih hzhi))
        (le_min (mul_nonneg hpowerhi hzlo) (mul_nonneg hpowerhi hzhi))
    change 0 ≤ fourLo (loop z n).1 (ofReal z)/P160
    exact Int.ediv_nonneg hfour P160_pos.le

private theorem loop_total_lo_step (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    (loop z n).2.lo ≤ (loop z (n+1)).2.lo := by
  have hterm : 0 ≤ (loop z n).1.lo/((n+1 : ℕ) : ℤ) :=
    Int.ediv_nonneg (loop_power_lo_nonneg z hz n) (by positivity)
  change (loop z n).2.lo ≤ (loop z n).2.lo+(loop z n).1.lo/((n+1 : ℕ) : ℤ)
  exact le_add_of_nonneg_right hterm

private theorem loop_total_lo_ge_first (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    (ofReal z).lo ≤ (loop z (n+1)).2.lo := by
  induction n with
  | zero => simp [loop, add, divNat, ofReal]
  | succ n ih => exact ih.trans (loop_total_lo_step z hz (n+1))

/-- The original first total update is z.lo//1=z.lo. All subsequent lower
terms are nonnegative, even after every original rounded multiplication.
No lower approximation to log or accumulated roundoff budget is assumed. -/
theorem originalLnUnit_lo_ge_first {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    (ofReal (1-1/x)).lo ≤ (originalLnUnit x).lo := by
  rw [originalLnUnit_eq]
  change (ofReal (1-1/x)).lo ≤ (loop (1-1/x) 256).2.lo
  exact loop_total_lo_ge_first (1-1/x) (rounded_z_upper hx1 hx2).1 255

/-- A valid raw interval with lower endpoint>=sqrt(P160) has a strictly
positive ORIGINAL rounded square lower endpoint. Mere lo>0 is insufficient. -/
theorem mul_self_lo_pos_of_two_pow_eighty (v : IV)
    (hlo : (2 : ℤ)^80 ≤ v.lo) (hvalid : v.lo ≤ v.hi) :
    0 < (mul v v).lo := by
  have hk : (0 : ℤ) ≤ (2 : ℤ)^80 := by positivity
  have hhi : (2 : ℤ)^80 ≤ v.hi := hlo.trans hvalid
  have hproduct (a b : ℤ) (ha : (2 : ℤ)^80 ≤ a) (hb : (2 : ℤ)^80 ≤ b) :
      P160 ≤ a*b := by
    calc
      P160 = (2 : ℤ)^80*(2 : ℤ)^80 := by norm_num [P160]
      _ ≤ a*b := mul_le_mul ha hb hk (hk.trans ha)
  have hfour : P160 ≤ fourLo v v :=
    le_min (le_min (hproduct v.lo v.lo hlo hlo) (hproduct v.lo v.hi hlo hhi))
      (le_min (hproduct v.hi v.lo hhi hlo) (hproduct v.hi v.hi hhi hhi))
  have hdiv : (1 : ℤ) ≤ fourLo v v/P160 :=
    (Int.le_ediv_iff_mul_le P160_pos).mpr (by simpa only [one_mul] using hfour)
  change 0 < fourLo v v/P160
  omega

/-- Both actual original divisor guards, and the stronger raw log threshold,
for every above-mu pair of original integer coordinate endpoints. The three
inputs are the original positive width, mu lower bound and rho upper bound.
There is no target log/square/mean enclosure or desired positive-lo input. -/
theorem original_integer_above_mu_log_guards (x0 x1 : ℤ)
    (hwidth : x0 < x1)
    (hmu : 25*(48000*2^24 : ℤ) ≤ 128*x0)
    (hrho : 96*x1 ≤ 19*(48000*2^24 : ℤ)) :
    (2 : ℤ)^80 ≤ (originalLnUnit ((x1 : ℝ)/(x0 : ℝ))).lo ∧
      0 < (originalLnUnit ((x1 : ℝ)/(x0 : ℝ))).lo ∧
      0 < (mul (originalLnUnit ((x1 : ℝ)/(x0 : ℝ)))
        (originalLnUnit ((x1 : ℝ)/(x0 : ℝ)))).lo := by
  have hD : (0 : ℝ) < ((48000*2^24 : ℤ) : ℝ) := by norm_num
  have hmuR : 25*((48000*2^24 : ℤ) : ℝ) ≤ 128*(x0 : ℝ) := by
    exact_mod_cast hmu
  have hrhoR : 96*(x1 : ℝ) ≤ 19*((48000*2^24 : ℤ) : ℝ) := by
    exact_mod_cast hrho
  have hwidthR : (x0 : ℝ) < (x1 : ℝ) := by exact_mod_cast hwidth
  have hx0 : (0 : ℝ) < (x0 : ℝ) := by linarith only [hmuR, hD]
  have hx1 : (0 : ℝ) < (x1 : ℝ) := hx0.trans hwidthR
  have hq1 : (1 : ℝ) ≤ (x1 : ℝ)/(x0 : ℝ) :=
    (le_div_iff₀ hx0).mpr (by linarith only [hwidthR])
  have hq2 : (x1 : ℝ)/(x0 : ℝ) ≤ (2 : ℝ) :=
    (div_le_iff₀ hx0).mpr (by linarith only [hmuR, hrhoR, hD])
  have hgap : (1 : ℤ) ≤ x1-x0 := by omega
  have hsmall : (19 : ℤ)*(48000*2^24) ≤ 96*(2 : ℤ)^80 := by norm_num
  have hx1small : x1 ≤ (2 : ℤ)^80 :=
    (mul_le_mul_left (by norm_num : (0 : ℤ) < 96)).mp (hrho.trans hsmall)
  have hscaled : (2 : ℤ)^80*x1 ≤ (x1-x0)*P160 := by
    calc
      (2 : ℤ)^80*x1 ≤ (2 : ℤ)^80*(2 : ℤ)^80 :=
        mul_le_mul_of_nonneg_left hx1small (by positivity)
      _ = P160 := by norm_num [P160]
      _ ≤ (x1-x0)*P160 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hgap P160_pos.le
  have hscaledR : ((2 : ℤ)^80 : ℝ)*(x1 : ℝ) ≤
      ((x1 : ℝ)-(x0 : ℝ))*(P160 : ℝ) := by exact_mod_cast hscaled
  have hfirst : ((2 : ℤ)^80 : ℝ) ≤
      (1-1/((x1 : ℝ)/(x0 : ℝ)))*(P160 : ℝ) := by
    calc
      ((2 : ℤ)^80 : ℝ) ≤ ((x1 : ℝ)-(x0 : ℝ))*(P160 : ℝ)/(x1 : ℝ) :=
        (le_div_iff₀ hx1).mpr hscaledR
      _ = (1-1/((x1 : ℝ)/(x0 : ℝ)))*(P160 : ℝ) := by
        field [hx0.ne', hx1.ne']
  have hfloor : (2 : ℤ)^80 ≤ (ofReal (1-1/((x1 : ℝ)/(x0 : ℝ)))).lo :=
    Int.le_floor.mpr hfirst
  have hlo := hfloor.trans (originalLnUnit_lo_ge_first hq1 hq2)
  have hlog := original_positive256_ln_sound hq1 hq2
  have hvalid : (originalLnUnit ((x1 : ℝ)/(x0 : ℝ))).lo ≤
      (originalLnUnit ((x1 : ℝ)/(x0 : ℝ))).hi :=
    value_le_iff.mp (hlog.1.trans hlog.2)
  refine ⟨hlo, ?_, mul_self_lo_pos_of_two_pow_eighty _ hlo hvalid⟩
  exact (by norm_num : (0 : ℤ) < (2 : ℤ)^80).trans_le hlo

/-- Direct consumer wrapper for the ORIGINAL rational physical coordinates.
The representation equalities are literal row-field bindings, not desired
guards. The remaining geometric hypotheses are precisely width_xy, selected
above-mu and upper_rho. No extra minimum-width/depth gate is introduced. -/
theorem original_stored_above_mu_log_guards (x0 x1 : ℤ) (a b : ℚ)
    (ha : a=(x0 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hb : b=(x1 : ℚ)/((48000*2^24 : ℤ) : ℚ))
    (hwidth : (a : ℝ) < (b : ℝ))
    (hmu : (25 : ℝ)/128 ≤ (a : ℝ)) (hrho : (b : ℝ) ≤ (19 : ℝ)/96) :
    0 < (originalLnUnit ((b : ℝ)/(a : ℝ))).lo ∧
      0 < (mul (originalLnUnit ((b : ℝ)/(a : ℝ)))
        (originalLnUnit ((b : ℝ)/(a : ℝ)))).lo := by
  have hD : (0 : ℝ) < ((48000*2^24 : ℤ) : ℝ) := by norm_num
  have haR : (a : ℝ)=(x0 : ℝ)/((48000*2^24 : ℤ) : ℝ) := by
    rw [ha]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hbR : (b : ℝ)=(x1 : ℝ)/((48000*2^24 : ℤ) : ℝ) := by
    rw [hb]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hwidthR : (x0 : ℝ) < (x1 : ℝ) :=
    (div_lt_div_iff_of_pos_right hD).mp (by simpa only [haR, hbR] using hwidth)
  have hmuR : (25 : ℝ)/128*((48000*2^24 : ℤ) : ℝ) ≤ (x0 : ℝ) :=
    (le_div_iff₀ hD).mp (by simpa only [haR] using hmu)
  have hrhoR : (x1 : ℝ) ≤ (19 : ℝ)/96*((48000*2^24 : ℤ) : ℝ) :=
    (div_le_iff₀ hD).mp (by simpa only [hbR] using hrho)
  have hwidthI : x0 < x1 := by exact_mod_cast hwidthR
  have hmuI : 25*(48000*2^24 : ℤ) ≤ 128*x0 := by
    have h : 25*((48000*2^24 : ℤ) : ℝ) ≤ 128*(x0 : ℝ) := by linarith only [hmuR]
    exact_mod_cast h
  have hrhoI : 96*x1 ≤ 19*(48000*2^24 : ℤ) := by
    have h : 96*(x1 : ℝ) ≤ 19*((48000*2^24 : ℤ) : ℝ) := by linarith only [hrhoR]
    exact_mod_cast h
  have hx0 : (0 : ℝ) < (x0 : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 25/128) hD).trans_le hmuR
  have hratio : (b : ℝ)/(a : ℝ)=(x1 : ℝ)/(x0 : ℝ) := by
    rw [haR, hbR]
    field [hD.ne', hx0.ne']
  rw [hratio]
  exact (original_integer_above_mu_log_guards x0 x1 hwidthI hmuI hrhoI).2

end
end ImbalancedChen.OriginalThirdPositiveLogSourceOnly
