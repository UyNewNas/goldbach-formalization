import ImbalancedChen.P2GammaDyadicConductorSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT.
The two additional logarithmic costs of the actual weaker LS are budgeted
before selecting the cutoff. No sharp N+Q² sieve is silently substituted.
-/

namespace ImbalancedChen.P2GammaConductorScaleThreshold
noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics
open P2GammaConvolutionLargeConductor P2GammaExactConductorRegrouping
open P2GammaDyadicConductorSum

def logGauge (Q : ℕ) : ℝ := 1+Real.log (max 1 (Q : ℝ))
def lsLogCoefficient : ℝ := 18+4/Real.log 2
def dyadicCountCoefficient : ℝ := 1+1/Real.log 2

theorem logGauge_one_le (Q : ℕ) : 1≤logGauge Q := by
  unfold logGauge
  have := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
  linarith

theorem lsLogCoefficient_pos : 0<lsLogCoefficient := by
  unfold lsLogCoefficient
  have := Real.log_pos (by norm_num : (1 : ℝ)<2)
  positivity

theorem dyadicCountCoefficient_pos : 0<dyadicCountCoefficient := by
  unfold dyadicCountCoefficient
  have := Real.log_pos (by norm_num : (1 : ℝ)<2)
  positivity

theorem dyadicCount_le_logGauge (Q : ℕ) :
    (Nat.log 2 Q+1 : ℕ)≤dyadicCountCoefficient*logGauge Q := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  by_cases hQ : Q=0
  · subst Q
    simp only [Nat.log_zero_right,zero_add,Nat.cast_one,logGauge,Nat.cast_zero,
      max_eq_left (by norm_num : (0 : ℝ)≤1),Real.log_one,add_zero]
    unfold dyadicCountCoefficient
    positivity
  have hQr : (0 : ℝ)<Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
  have hQ1 : (1 : ℝ)≤Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
  have hpow := Nat.pow_log_le_self 2 hQ
  have hpowR : (2 : ℝ)^(Nat.log 2 Q)≤Q := by exact_mod_cast hpow
  have hl := Real.log_le_log (by positivity : (0 : ℝ)<2^(Nat.log 2 Q)) hpowR
  rw [Real.log_pow] at hl
  have hlQ : 0≤Real.log (Q : ℝ) := Real.log_nonneg hQ1
  have hn : (Nat.log 2 Q : ℝ)≤Real.log (Q : ℝ)/Real.log 2 :=
    (le_div_iff₀ h2).mpr hl
  unfold dyadicCountCoefficient logGauge
  rw [max_eq_right hQ1]
  push_cast
  have hcross : 0≤Real.log (Q : ℝ)/Real.log 2 := div_nonneg hlQ h2.le
  nlinarith

/-- Literal ceiling constant bounded only after it has appeared in the
finite LS theorem. Its coefficient is recorded explicitly. -/
theorem lsLog_le_logGauge (Q : ℕ) :
    lsLog (2*Q)≤lsLogCoefficient*logGauge Q := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  by_cases hQ : Q=0
  · subst Q
    norm_num [lsLog,logGauge,lsLogCoefficient]
    positivity
  have hQr : (0 : ℝ)<Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
  have hQ1 : (1 : ℝ)≤Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
  have ht : Real.log (((2*Q : ℕ) : ℝ)^2)/Real.log 2 =
      2+2*Real.log (Q : ℝ)/Real.log 2 := by
    push_cast
    rw [Real.log_pow,Real.log_mul (by norm_num : (2 : ℝ)≠0) hQr.ne']
    field_simp
    <;> ring
  have ht0 : 0≤Real.log (((2*Q : ℕ) : ℝ)^2)/Real.log 2 := by
    rw [ht]
    exact add_nonneg (by norm_num) (div_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg hQ1)) h2.le)
  have hceil := Nat.ceil_lt_add_one ht0
  have hlQ := Real.log_nonneg hQ1
  have hcross : 0≤4/Real.log 2*Real.log (Q : ℝ) := by positivity
  unfold lsLog lsLogCoefficient logGauge
  rw [max_eq_right hQ1]
  rw [ht] at hceil
  nlinarith

theorem sqrt_lsLog_le (Q : ℕ) :
    Real.sqrt (lsLog (2*Q))≤(lsLogCoefficient+1)*logGauge Q := by
  have hc := lsLog_nonneg (2*Q)
  have hg := logGauge_one_le Q
  have hb := lsLog_le_logGauge Q
  have hcoef := lsLogCoefficient_pos
  have hs : Real.sqrt (lsLog (2*Q))≤lsLog (2*Q)+1 := by
    nlinarith [Real.sq_sqrt hc,Real.sqrt_nonneg (lsLog (2*Q)),
      sq_nonneg (Real.sqrt (lsLog (2*Q))-1)]
  nlinarith

def lowConductorTotal (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb Q b0 : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 Q,inducedShell a b Ma Mb La Lb k
    ((Finset.Icc 2 (Q/k)).filter (fun r => r≤2^b0))

theorem inducedTotal_eq_low_add_high (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb Q b0 : ℕ) :
    inducedTotal a b Ma Mb La Lb Q =
      lowConductorTotal a b Ma Mb La Lb Q b0+
        highConductorTotal a b Ma Mb La Lb Q b0 := by
  unfold inducedTotal lowConductorTotal highConductorTotal inducedShell
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have h := Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 (Q/k))
    (fun r => r≤2^b0)
    (fun r => (1/((r*k).totient : ℝ))*∑ psi : AnalyticNumberTheory.LargeSieve.PrimitiveCharacter r,
      rowAmplitude (unitMask k a) Ma La r psi*rowAmplitude (unitMask k b) Mb Lb r psi)
  simpa only [not_le] using h.symm

/-- Original level sum has an explicit small-conductor residual, not a
small-conductor estimate assumed as a renamed BV premise. -/
theorem full_rectangle_norm_le_low_add_high (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (hMa : 0≤Ma) (hMb : 0≤Mb) (La Lb Q b0 : ℕ)
    (z : (q : ℕ) → ZMod q) :
    (∑ q ∈ Finset.Icc 1 Q,‖rectangleCharacterDiscrepancy a b Ma Mb La Lb q (z q)‖)≤
      lowConductorTotal a b Ma Mb La Lb Q b0+
        4*logGauge Q*highU a b Ma Mb La Lb Q b0+
          8*highV a b Ma Mb La Lb Q := by
  have h := sum_rectangleCharacterDiscrepancy_norm_le a b Ma Mb La Lb Q z
  rw [allNonprincipalMajorant_eq_inducedTotal a b Ma Mb hMa hMb,
    inducedTotal_eq_low_add_high a b Ma Mb La Lb Q b0] at h
  exact h.trans (by have hh := highConductorTotal_le a b Ma Mb La Lb Q b0
                   dsimp [logGauge]; linarith)

/-- Polynomial form of the whole high ledger. The explicit LS loss costs
one log in the terminal lane and at most three in the middle lane. -/
theorem highConductorTotal_polynomial_le (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb Q b0 : ℕ) (l : ℝ) (hl : 1≤l) (hg : logGauge Q≤l) :
    highConductorTotal a b Ma Mb La Lb Q b0 ≤
      8*energyProduct a b Ma Mb La Lb*Real.sqrt La*Real.sqrt Lb*l/(2 : ℝ)^b0+
      8*(lsLogCoefficient+1)*dyadicCountCoefficient*
        energyProduct a b Ma Mb La Lb*(Real.sqrt La+Real.sqrt Lb)*l^3+
      64*lsLogCoefficient*energyProduct a b Ma Mb La Lb*(Q : ℝ)*l := by
  have hE := energyProduct_nonneg a b Ma Mb La Lb
  have hc := lsLogCoefficient_pos
  have hd := dyadicCountCoefficient_pos
  have hcQ := lsLog_le_logGauge Q
  have hsQ := sqrt_lsLog_le Q
  have hdQ := dyadicCount_le_logGauge Q
  have hcc : lsLog (2*Q)≤lsLogCoefficient*l :=
    hcQ.trans (mul_le_mul_of_nonneg_left hg hc.le)
  have hss : Real.sqrt (lsLog (2*Q))≤(lsLogCoefficient+1)*l :=
    hsQ.trans (mul_le_mul_of_nonneg_left hg (by linarith))
  have hdd : ((Nat.log 2 Q+1 : ℕ) : ℝ)≤dyadicCountCoefficient*l :=
    hdQ.trans (mul_le_mul_of_nonneg_left hg hd.le)
  have hh := highConductorTotal_le a b Ma Mb La Lb Q b0
  unfold highU highV at hh
  refine hh.trans ?_
  calc
    _ ≤ 4*l*(energyProduct a b Ma Mb La Lb*
        (2*Real.sqrt La*Real.sqrt Lb/(2 : ℝ)^b0+
          2*((lsLogCoefficient+1)*l)*(dyadicCountCoefficient*l)*
            (Real.sqrt La+Real.sqrt Lb)))+
        8*(8*(lsLogCoefficient*l)*energyProduct a b Ma Mb La Lb*(Q : ℝ)) := by
      gcongr
    _ = _ := by ring

private theorem power_ratio_le (A C j : ℕ) (hj : j≤3) (l : ℝ) (hl : 1≤l) :
    l^(C+j)/l^(A+C+3)≤1/l^A := by
  have hl0 : 0<l := zero_lt_one.trans_le hl
  apply (div_le_div_iff₀ (pow_pos hl0 _) (pow_pos hl0 _)).mpr
  rw [one_mul,← pow_add]
  exact pow_le_pow_right₀ hl (by omega)

/-- Finite scale conversion of the proved entire high-conductor ledger.
All inputs concern only the original two energies, lengths and scale. In
particular there is no dyadic, BV or high-conductor bound among the premises.
The additional three log powers pay for the actual weaker LS constant. -/
theorem highConductorTotal_scale_le (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb Q b0 A C : ℕ) (x l e d : ℝ)
    (hx : 0≤x) (hl : 1≤l) (he : 0≤e) (hd : 0≤d) (hg : logGauge Q≤l)
    (henergy : energyProduct a b Ma Mb La Lb≤e*Real.sqrt x*l^C)
    (hproduct : Real.sqrt La*Real.sqrt Lb≤d*Real.sqrt x)
    (hlength : Real.sqrt La+Real.sqrt Lb≤d*Real.sqrt x/l^(A+C+3))
    (hcutoff : l^(A+C+3)≤(2 : ℝ)^b0)
    (hlevel : (Q : ℝ)≤Real.sqrt x/l^(A+C+3)) :
    highConductorTotal a b Ma Mb La Lb Q b0 ≤
      e*(8*d+8*(lsLogCoefficient+1)*dyadicCountCoefficient*d+
        64*lsLogCoefficient)*x/l^A := by
  have hl0 : 0<l := zero_lt_one.trans_le hl
  have hE := energyProduct_nonneg a b Ma Mb La Lb
  have hc := lsLogCoefficient_pos
  have hdc := dyadicCountCoefficient_pos
  have hp : 0<l^(A+C+3) := pow_pos hl0 _
  have hh := highConductorTotal_polynomial_le a b Ma Mb La Lb Q b0 l hl hg
  have hfirst :
      8*energyProduct a b Ma Mb La Lb*Real.sqrt La*Real.sqrt Lb*l/(2 : ℝ)^b0 ≤
        (8*e*d*x)*(l^(C+1)/l^(A+C+3)) := by
    calc
      _ = 8*energyProduct a b Ma Mb La Lb*(Real.sqrt La*Real.sqrt Lb)*l/(2 : ℝ)^b0 := by ring
      _ ≤ 8*(e*Real.sqrt x*l^C)*(d*Real.sqrt x)*l/l^(A+C+3) := by gcongr
      _ = _ := by
        conv_rhs => rw [← Real.sq_sqrt hx]
        rw [pow_succ]
        ring
  have hmiddle :
      8*(lsLogCoefficient+1)*dyadicCountCoefficient*
        energyProduct a b Ma Mb La Lb*(Real.sqrt La+Real.sqrt Lb)*l^3 ≤
      (8*(lsLogCoefficient+1)*dyadicCountCoefficient*e*d*x)*
        (l^(C+3)/l^(A+C+3)) := by
    calc
      _ ≤ 8*(lsLogCoefficient+1)*dyadicCountCoefficient*
          (e*Real.sqrt x*l^C)*(d*Real.sqrt x/l^(A+C+3))*l^3 := by gcongr
      _ = _ := by
        conv_rhs => rw [← Real.sq_sqrt hx]
        rw [pow_add]
        ring
  have hlast :
      64*lsLogCoefficient*energyProduct a b Ma Mb La Lb*(Q : ℝ)*l ≤
        (64*lsLogCoefficient*e*x)*(l^(C+1)/l^(A+C+3)) := by
    calc
      _ ≤ 64*lsLogCoefficient*(e*Real.sqrt x*l^C)*
          (Real.sqrt x/l^(A+C+3))*l := by gcongr
      _ = _ := by
        conv_rhs => rw [← Real.sq_sqrt hx]
        rw [pow_succ]
        ring
  have hr1 := power_ratio_le A C 1 (by omega) l hl
  have hr3 := power_ratio_le A C 3 le_rfl l hl
  have h1 := hfirst.trans (mul_le_mul_of_nonneg_left hr1 (by positivity))
  have h2 := hmiddle.trans (mul_le_mul_of_nonneg_left hr3 (by positivity))
  have h3 := hlast.trans (mul_le_mul_of_nonneg_left hr1 (by positivity))
  calc
    _ ≤ (8*e*d*x)*(1/l^A)+
        (8*(lsLogCoefficient+1)*dyadicCountCoefficient*e*d*x)*(1/l^A)+
        (64*lsLogCoefficient*e*x)*(1/l^A) :=
      hh.trans (add_le_add (add_le_add h1 h2) h3)
    _ = _ := by ring

/-- The dyadic cutoff is chosen from the logarithm; its ceiling factor is
less than two and its exponent is fixed before the scale tends to infinity. -/
def cutoffExponent (l : ℝ) (B : ℕ) : ℕ :=
  Nat.ceil (Real.log (l^B)/Real.log 2)

theorem cutoffExponent_bounds (l : ℝ) (hl : 1≤l) (B : ℕ) :
    l^B≤(2 : ℝ)^(cutoffExponent l B) ∧
      (2 : ℝ)^(cutoffExponent l B)≤2*l^B := by
  have hl0 : 0<l := zero_lt_one.trans_le hl
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0≤Real.log (l^B)/Real.log 2 :=
    div_nonneg (Real.log_nonneg (one_le_pow₀ hl)) h2.le
  have hlo := Nat.le_ceil (Real.log (l^B)/Real.log 2)
  have hhi := Nat.ceil_lt_add_one ht
  have hpow : 0<l^B := pow_pos hl0 B
  have hdyad : 0<(2 : ℝ)^(cutoffExponent l B) := by positivity
  constructor
  · apply (Real.log_le_log_iff hpow hdyad).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ h2).mp hlo
  · apply (Real.log_le_log_iff hdyad (by positivity : 0<2*l^B)).mp
    rw [Real.log_pow,Real.log_mul (by norm_num : (2 : ℝ)≠0) hpow.ne']
    unfold cutoffExponent
    have h := (lt_div_iff₀ h2).mp (show
      (Nat.ceil (Real.log (l^B)/Real.log 2) : ℝ)<
        (Real.log (l^B)+Real.log 2)/Real.log 2 by
          convert hhi using 1 <;> field_simp <;> ring)
    linarith

/-- One common threshold for every coefficient row satisfying the displayed
primitive norm/length constraints. No dependence on the later row, quotient,
character, residue or target is allowed in this threshold. -/
theorem eventually_log_power_le_fixed_power (m : ℕ) (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ x : ℝ in atTop,1≤Real.log x ∧ (Real.log x)^m≤x^eta := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (m : ℝ) heta).bound (by norm_num : (0 : ℝ)<1)
  filter_upwards [hsmall,tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (0 : ℝ)] with x hx hlog hx0
  refine ⟨hlog,?_⟩
  simpa only [Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(Real.log x)^m),
    abs_of_nonneg (Real.rpow_nonneg hx0 eta),one_mul] using hx

theorem eventually_one_add_log_power_le_fixed_power (m : ℕ) (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ x : ℝ in atTop,1≤Real.log x ∧ (1+Real.log x)^m≤x^eta := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (m : ℝ) heta).bound
    (by positivity : (0 : ℝ)<1/(2 : ℝ)^m)
  filter_upwards [hsmall,tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (0 : ℝ)] with x hx hlog hx0
  refine ⟨hlog,?_⟩
  have hraw : (Real.log x)^m≤(1/(2 : ℝ)^m)*x^eta := by
    simpa only [Real.rpow_natCast,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0≤(Real.log x)^m),
      abs_of_nonneg (Real.rpow_nonneg hx0 eta)] using hx
  calc
    _ ≤ (2*Real.log x)^m := pow_le_pow_left₀ (by positivity) (by linarith) m
    _ = (2 : ℝ)^m*(Real.log x)^m := mul_pow _ _ _
    _ ≤ (2 : ℝ)^m*((1/(2 : ℝ)^m)*x^eta) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = _ := by field_simp

/-- The actual complete-modulus exponent .45 is below half at the same
complete scale. Every prescribed logarithmic D is absorbed after fixing D. -/
theorem eventually_actual_power_level (D : ℕ) :
    ∀ᶠ x : ℝ in atTop,x^((9 : ℝ)/20)≤Real.sqrt x/(Real.log x)^D := by
  filter_upwards [eventually_log_power_le_fixed_power D ((1 : ℝ)/20) (by norm_num),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hlog0 : 0<(Real.log x)^D := pow_pos (zero_lt_one.trans_le hx.1) _
  apply (le_div_iff₀ hlog0).mpr
  calc
    _ ≤ x^((9 : ℝ)/20)*x^((1 : ℝ)/20) :=
      mul_le_mul_of_nonneg_left hx.2 (Real.rpow_nonneg hx0.le _)
    _ = Real.sqrt x := by
      rw [← Real.rpow_add hx0]
      norm_num [Real.sqrt_eq_rpow]

/-- Uniform high-conductor logarithmic saving at the actual .45 complete
scale. One threshold precedes every row, length, quotient, character and
residue. The two row energies and two positive-length consequences remain
primitive data, to be supplied by the actual separated-source construction. -/
theorem exists_uniform_high_conductor_threshold (A C : ℕ) (eta : ℝ) (heta : 0<eta) :
    ∃ x0 : ℝ,∀ x : ℝ,x0≤x →
      ∀ (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb Q : ℕ) (e d : ℝ),
      0≤e → 0≤d →
      energyProduct a b Ma Mb La Lb≤e*Real.sqrt x*(1+Real.log x)^C →
      Real.sqrt La*Real.sqrt Lb≤d*Real.sqrt x →
      Real.sqrt La+Real.sqrt Lb≤d*Real.sqrt x/x^eta →
      (Q : ℝ)≤x^((9 : ℝ)/20) →
      highConductorTotal a b Ma Mb La Lb Q
        (cutoffExponent (1+Real.log x) (A+C+3)) ≤
      e*(8*d+8*(lsLogCoefficient+1)*dyadicCountCoefficient*d+
        64*lsLogCoefficient)*x/(1+Real.log x)^A := by
  have hlarge : ∀ᶠ x : ℝ in atTop,
      1≤Real.log x ∧ (1+Real.log x)^(A+C+3)≤x^eta ∧
        (1+Real.log x)^(A+C+3)≤x^((1 : ℝ)/20) ∧ 1≤x := by
    filter_upwards [eventually_one_add_log_power_le_fixed_power (A+C+3) eta heta,
      eventually_one_add_log_power_le_fixed_power (A+C+3) ((1 : ℝ)/20) (by norm_num),
      eventually_ge_atTop (1 : ℝ)] with x hx hy hx1
    exact ⟨hx.1,hx.2,hy.2,hx1⟩
  obtain ⟨x0,hx0⟩ := eventually_atTop.mp hlarge
  refine ⟨x0,?_⟩
  intro x hx a b Ma Mb La Lb Q e d he hd hE hp hs hQ
  obtain ⟨hl,hpow,hpowLevel,hx1⟩ := hx0 x hx
  have hxpos : 0<x := zero_lt_one.trans_le hx1
  have hl1 : 1≤1+Real.log x := by linarith
  have hg : logGauge Q≤1+Real.log x := by
    have hQx : (Q : ℝ)≤x := hQ.trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (9 : ℝ)/20≤1))
    unfold logGauge
    exact add_le_add_left (Real.log_le_log (by positivity)
      (max_le hx1 hQx)) 1
  have hlevel : (Q : ℝ)≤Real.sqrt x/(1+Real.log x)^(A+C+3) := by
    apply (le_div_iff₀ (pow_pos (by linarith : 0<1+Real.log x) _)).mpr
    calc
      _ ≤ x^((9 : ℝ)/20)*x^((1 : ℝ)/20) :=
        mul_le_mul hQ hpowLevel (by positivity) (Real.rpow_nonneg hxpos.le _)
      _ = Real.sqrt x := by
        rw [← Real.rpow_add hxpos]
        norm_num [Real.sqrt_eq_rpow]
  have hlength : Real.sqrt La+Real.sqrt Lb≤
      d*Real.sqrt x/(1+Real.log x)^(A+C+3) := by
    exact hs.trans (div_le_div_of_nonneg_left (by positivity)
      (pow_pos (by linarith : 0<1+Real.log x) _) hpow)
  exact highConductorTotal_scale_le a b Ma Mb La Lb Q
    (cutoffExponent (1+Real.log x) (A+C+3)) A C x (1+Real.log x) e d
    hxpos.le hl1 he hd hg hE hp hlength
    (cutoffExponent_bounds (1+Real.log x) hl1 _).1 hlevel

end
end ImbalancedChen.P2GammaConductorScaleThreshold
