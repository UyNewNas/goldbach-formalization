import ImbalancedChen.Part3DistributionTargets
import Mathlib.Tactic

/-! A necessary product inequality of the literal Type II length tests.
Neither the slot assignment nor the weight on the factors appears. -/
namespace ImbalancedChen.P4AActualMediumProductCeiling
noncomputable section
open Part3

theorem eliminate (u a b c R X : ℝ) (h1 : a≤u)
    (h2 : 2*u+b+2*c ≤ X) (h3 : (7/32)*R+u+a+5*b+2*c ≤ 2*X) :
    8*(a+b+c) ≤ 5*X-(7/32)*R := by linarith

theorem admissible_ceiling {B : ℕ} {sig kap c0 : ℝ} {d : MediumAtom}
    (hsig : 0≤sig) (h : MediumAdmissible B sig kap c0 d)
    (hx : 1≤d.scale) (hr : 0<d.residue.natAbs) :
    8*(Real.log d.Q1+Real.log d.Q2+Real.log d.Q3) ≤
      5*Real.log d.scale-(7/32)*Real.log d.residue.natAbs := by
  obtain ⟨hU,_,hA,hB,hC,_,_,_,h1,h2,h3,_⟩ := h
  have hu : 0<d.U := lt_of_lt_of_le zero_lt_one hU
  have ha : 0<d.Q1 := zero_lt_one.trans_le hA
  have hb : 0<d.Q2 := zero_lt_one.trans_le hB
  have hc : 0<d.Q3 := zero_lt_one.trans_le hC
  have hR : (0:ℝ)<d.residue.natAbs := by exact_mod_cast hr
  have hx' : 0<d.scale := zero_lt_one.trans_le hx
  have hX := Real.log_nonneg hx
  have H1 := Real.log_le_log ha h1.le
  have H2 := Real.log_le_log (show 0<d.U^2*d.Q2*d.Q3^2 by positivity) h2.le
  have H3 := Real.log_le_log
    (show 0<(d.residue.natAbs:ℝ)^(7/32:ℝ)*d.U*d.Q1*d.Q2^5*d.Q3^2 by positivity) h3.le
  rw [Real.log_mul hu.ne' (Real.rpow_pos_of_pos hx' _).ne',Real.log_rpow hx'] at H1
  rw [Real.log_mul (mul_pos (pow_pos hu _) hb).ne' (pow_pos hc _).ne',
    Real.log_mul (pow_pos hu _).ne' hb.ne',Real.log_rpow hx'] at H2
  have hpow := Real.rpow_pos_of_pos hR (7/32:ℝ)
  rw [Real.log_mul (mul_pos (mul_pos (mul_pos hpow hu) ha) (pow_pos hb _)).ne' (pow_pos hc _).ne',
    Real.log_mul (mul_pos (mul_pos hpow hu) ha).ne' (pow_pos hb _).ne',
    Real.log_mul (mul_pos hpow hu).ne' ha.ne',Real.log_mul hpow.ne' hu.ne',
    Real.log_rpow hR,Real.log_rpow hx'] at H3
  simp only [Real.log_pow,Nat.cast_ofNat] at H2 H3
  apply eliminate (Real.log d.U)
  all_goals nlinarith [mul_nonneg hsig hX]

theorem physical_ceiling {B : ℕ} {sig kap c0 : ℝ} {d : MediumAtom}
    (hsig : 0≤sig) (h : MediumAdmissible B sig kap c0 d)
    (hx : 1≤d.scale) (hr : 0<d.residue.natAbs)
    {a b c : ℕ} (ha : a∈factorCarrier d.Q1) (hb : b∈factorCarrier d.Q2)
    (hc : c∈factorCarrier d.Q3) (hp : 0<a*b*c) :
    8*(Real.log ((a*b*c:ℕ):ℝ)-Real.log 8) ≤
      5*Real.log d.scale-(7/32)*Real.log d.residue.natAbs := by
  have hA : 0<d.Q1 := zero_lt_one.trans_le h.2.2.1
  have hB : 0<d.Q2 := zero_lt_one.trans_le h.2.2.2.1
  have hC : 0<d.Q3 := zero_lt_one.trans_le h.2.2.2.2.1
  have H {x : ℝ} (hx : 0<x) {n : ℕ} (hn : n∈factorCarrier x) : (n:ℝ) ≤ 2*x :=
    (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
  have hprod : ((a*b*c:ℕ):ℝ) ≤ 8*d.Q1*d.Q2*d.Q3 := by
    push_cast
    calc
      _ ≤ (2*d.Q1)*(2*d.Q2)*(2*d.Q3) := by
        gcongr
        · exact H hA ha
        · exact H hB hb
        · exact H hC hc
      _ = _ := by ring
  have hl := Real.log_le_log (by exact_mod_cast hp) hprod
  rw [Real.log_mul (by positivity) hC.ne',Real.log_mul (by positivity) hB.ne',
    Real.log_mul (by norm_num) hA.ne'] at hl
  linarith [admissible_ceiling hsig h hx hr]

end
end ImbalancedChen.P4AActualMediumProductCeiling
