import ImbalancedChen.P2HistoricLogComputeCore
import ImbalancedChen.P2HistoricQ80DefectLookup
import ImbalancedChen.P2HistoricLogRangeReduction
import ImbalancedChen.Certificates.RationalLogCertificate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
SOURCE_ONLY / UNCOMPILED. Literal historic logarithm backend.

Source: certify_conservative_chen.py, SHA256
67b9429667e18786058e0fe58676fbe09d556868468f1281166cac2b55f8604e.
The source uses 32 odd terms, integer floors on every lower power/summand,
integer ceilings on every upper power/summand, and the sharpened tail with
divisor 65. RationalLogCertificate's existing remainder omits that divisor;
it cannot establish soundness of these historical upper outputs. The sharper
real analytic inequality is proved here from Mathlib's exact derivative.

The loop below uses the literal old integer operations, rather than a new
rational-series certificate whose endpoints merely resemble the old ones.
The sibling range-reduction module supplies the literal integer bit-length
branches. Its endpoint bounds prove every atanh guard. The final `logI`
theorem retains exactly the producer's positive rounded-lower-endpoint
guard; it assumes no true-log bound and no saved-output numerical check.
No producer, numeric replay, Lean evaluator, or native oracle was run.
-/

namespace ImbalancedChen.Certificates.P2HistoricLogPointInterpreter

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2HistoricQ80DefectLookup
open P2DirectedLogRounding

def decode (n : ℤ) : ℝ := (n : ℝ) / (Q : ℝ)

theorem Q_real_pos : (0 : ℝ) < Q := by norm_num [Q]
theorem Q_int_pos : (0 : ℤ) < Q := by exact_mod_cast Q_real_pos

theorem contains_iff (x : I80) (v : ℝ) :
    x.Contains v ↔ decode x.lo ≤ v ∧ v ≤ decode x.hi := by
  simp [I80.Contains, I80.enclosure, I80.decodeLo, I80.decodeHi,
    Enclosure.Contains, decode]

theorem ediv_le_real (n d : ℤ) (hd : 0 < d) :
    ((n/d : ℤ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
  have hh := Int.floor_le ((n : ℝ) / (d : ℝ))
  rw [Int.floor_div_cast_of_nonneg hd.le, Int.floor_intCast] at hh
  exact hh

theorem real_le_ceilDiv (n d : ℤ) (hd : 0 < d) :
    (n : ℝ) / (d : ℝ) ≤ (ceilDiv n d : ℝ) := by
  have hh := ediv_le_real (-n) d hd
  simp only [Int.cast_neg, neg_div] at hh
  simp only [ceilDiv, Int.cast_neg]
  linarith

theorem ceilDiv_le (n d m : ℤ) (hd : 0 < d) (hnm : n ≤ m*d) :
    ceilDiv n d ≤ m := by
  have hh := Int.le_ediv_of_mul_le hd (show (-m)*d ≤ -n by nlinarith)
  dsimp [ceilDiv]
  linarith

theorem ceilDiv_nonnegative {n d : ℤ} (hn : 0 ≤ n) (hd : 0 < d) :
    0 ≤ ceilDiv n d := by
  have hh := real_le_ceilDiv n d hd
  have hr : (0 : ℝ) ≤ (n : ℝ)/(d : ℝ) :=
    div_nonneg (by exact_mod_cast hn) (by exact_mod_cast hd.le)
  exact_mod_cast hr.trans hh

theorem floor_product_decode (a b : ℤ) :
    decode (a*b/(Q : ℤ)) ≤ decode a * decode b := by
  calc
    decode (a*b/(Q : ℤ)) ≤ (((a*b : ℤ) : ℝ)/(Q : ℝ))/(Q : ℝ) :=
      div_le_div_of_nonneg_right (ediv_le_real _ _ Q_int_pos) Q_real_pos.le
    _ = _ := by simp only [decode, Int.cast_mul]; ring

theorem ceil_product_decode (a b : ℤ) :
    decode a * decode b ≤ decode (ceilDiv (a*b) (Q : ℤ)) := by
  calc
    decode a * decode b = (((a*b : ℤ) : ℝ)/(Q : ℝ))/(Q : ℝ) := by
      simp only [decode, Int.cast_mul]; ring
    _ ≤ _ := div_le_div_of_nonneg_right (real_le_ceilDiv _ _ Q_int_pos) Q_real_pos.le

/-- The literal positive-endpoint product used in the odd-power loop. -/
theorem positiveMul_lo_nonnegative {x y : I80} (hx : 0 ≤ x.lo) (hy : 0 ≤ y.lo) :
    0 ≤ (positiveMul x y).lo := by
  exact Int.ediv_nonneg (mul_nonneg hx hy) Q_int_pos.le

theorem positiveMul_contains {x y : I80} {v w : ℝ}
    (hx : x.Contains v) (hy : y.Contains w) (hx0 : 0 ≤ x.lo) (hy0 : 0 ≤ y.lo) :
    (positiveMul x y).Contains (v*w) := by
  obtain ⟨hxl,hxh⟩ := (contains_iff x v).1 hx
  obtain ⟨hyl,hyh⟩ := (contains_iff y w).1 hy
  have hxl0 : 0 ≤ decode x.lo := div_nonneg (by exact_mod_cast hx0) Q_real_pos.le
  have hyl0 : 0 ≤ decode y.lo := div_nonneg (by exact_mod_cast hy0) Q_real_pos.le
  have hv0 := hxl0.trans hxl
  have hw0 := hyl0.trans hyl
  apply (contains_iff _ _).2
  constructor
  · exact (floor_product_decode _ _).trans (mul_le_mul hxl hyl hyl0 hv0)
  · exact (mul_le_mul hxh hyh hw0 (hv0.trans hxh)).trans (ceil_product_decode _ _)

theorem divNat_contains {x : I80} {v : ℝ} (hx : x.Contains v)
    {n : ℕ} (hn : 0 < n) : (divNat x n).Contains (v/(n : ℝ)) := by
  obtain ⟨hxl,hxh⟩ := (contains_iff x v).1 hx
  have hni : (0 : ℤ) < n := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  apply (contains_iff _ _).2
  constructor
  · calc
      decode (x.lo/(n : ℤ)) ≤ ((x.lo : ℝ)/(n : ℝ))/(Q : ℝ) :=
        div_le_div_of_nonneg_right (ediv_le_real _ _ hni) Q_real_pos.le
      _ = decode x.lo / (n : ℝ) := by unfold decode; ring
      _ ≤ _ := div_le_div_of_nonneg_right hxl hnr.le
  · calc
      v/(n : ℝ) ≤ decode x.hi/(n : ℝ) := div_le_div_of_nonneg_right hxh hnr.le
      _ = ((x.hi : ℝ)/(n : ℝ))/(Q : ℝ) := by unfold decode; ring
      _ ≤ _ := div_le_div_of_nonneg_right (real_le_ceilDiv _ _ hni) Q_real_pos.le

def oddSum (u : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, u^(2*j+1)/((2*j+1 : ℕ) : ℝ)

/-- The historical sharp remainder, including the factor 2*n+1. -/
theorem sharp_odd_log_upper {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (n : ℕ) :
    Real.log ((1+u)/(1-u)) ≤
      2*oddSum u n + 2*u^(2*n+1)/(((2*n+1 : ℕ) : ℝ)*(1-u^2)) := by
  let F : ℝ → ℝ := fun y =>
    1/2 * Real.log ((1+y)/(1-y)) - oddSum y n
  let G : ℝ → ℝ := fun y =>
    y^(2*n+1)/(((2*n+1 : ℕ) : ℝ)*(1-u^2)) - F y
  have hd : 0 < 1-u^2 := by
    nlinarith [mul_pos (sub_pos.mpr hu1) (show 0 < 1+u by linarith)]
  have hn : (0 : ℝ) < (2*n+1 : ℕ) := by positivity
  have hder (y : ℝ) (hy : y ∈ Icc 0 u) :
      HasDerivAt G (y^(2*n)/(1-u^2) - y^(2*n)/(1-y^2)) y := by
    have hf := Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range n
      (show -1 < y by linarith [hy.1]) (show y < 1 by linarith [hy.2])
    have hp := (hasDerivAt_pow (2*n+1) y).div_const
      (((2*n+1 : ℕ) : ℝ)*(1-u^2))
    have hh : HasDerivAt G
        ((((2*n+1 : ℕ) : ℝ)*y^(2*n))/(((2*n+1 : ℕ) : ℝ)*(1-u^2)) -
          (y^2)^n/(1-y^2)) y := by
      convert! (hp.sub hf) using 1 <;>
        simp only [G, F, oddSum, Pi.sub_apply, Nat.add_sub_cancel, Nat.cast_add,
          Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      funext z
      rfl
    convert hh using 1
    simp only [← pow_mul]
    have hylt : y < 1 := hy.2.trans_lt hu1
    have hdy : 1-y^2 ≠ 0 := ne_of_gt (by
      nlinarith [mul_pos (sub_pos.mpr hylt) (show 0 < 1+y by linarith [hy.1])])
    field_simp [hn.ne',hd.ne',hdy] <;> ring
  have hm : MonotoneOn G (Icc 0 u) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u)
      (fun y hy => (hder y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hder y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    have hyc : y ∈ Icc 0 u := interior_subset hy
    have hy2 : y^2 ≤ u^2 := by nlinarith [hyc.1, hyc.2]
    have hdy : 0 < 1-y^2 := by linarith
    have hp : 0 ≤ y^(2*n) := pow_nonneg hyc.1 _
    exact sub_nonneg.mpr (div_le_div_of_nonneg_left hp hd (by linarith))
  have hG := hm ⟨le_rfl,hu0⟩ ⟨hu0,le_rfl⟩ hu0
  have hz : G 0 = 0 := by simp [G,F,oddSum]
  rw [hz] at hG
  dsimp [G,F] at hG
  have hoddpos : (0 : ℝ) < ((2*n+1 : ℕ) : ℝ)*(1-u^2) := mul_pos hn hd
  ring_nf at hG ⊢
  linarith only [hG]

theorem oddLoop_invariant {ul uh : ℤ} {u : ℝ} (hu : (I80.mk ul uh).Contains u)
    (hul : 0 ≤ ul) (n : ℕ) :
    let square := oddSquare ul uh
    let state := oddLoop square ul uh n
    state.power.Contains (u^(2*n+1)) ∧ 0 ≤ state.power.lo ∧
      state.total.Contains (oddSum u n) := by
  have hsq : (oddSquare ul uh).Contains (u^2) := by
    simpa only [oddSquare, positiveMul, pow_two] using positiveMul_contains hu hu hul hul
  have hsq0 : 0 ≤ (oddSquare ul uh).lo := by
    simpa only [oddSquare, positiveMul] using
      (positiveMul_lo_nonnegative (x := I80.mk ul uh) (y := I80.mk ul uh) hul hul)
  induction n with
  | zero =>
      refine ⟨?_,hul,?_⟩
      · simpa only [oddLoop_zero_eq,oddStart,Nat.mul_zero,Nat.zero_add,pow_one] using hu
      · simp [oddLoop_zero_eq,oddStart,oddSum,I80.raw,contains_iff,decode]
  | succ n ih =>
      obtain ⟨hp,hp0,hs⟩ := ih
      have hprod := positiveMul_contains hp hsq hp0 hsq0
      have he : u^(2*n+1)*u^2 = u^(2*(n+1)+1) := by
        rw [← pow_add]
        congr 1 <;> omega
      refine ⟨?_, positiveMul_lo_nonnegative hp0 hsq0, ?_⟩
      · simpa only [oddLoop_succ_eq,oddStep,he] using hprod
      · have hadd := I80.add_contains hs (divNat_contains hp (by omega : 0 < 2*n+1))
        simpa only [oddLoop_succ_eq,oddStep,oddSum,Finset.sum_range_succ] using hadd

/-- Literal Python atanh_log_bounds. The first state component is pl/ph;
the second is sl/sh, and the last ceil is the exact source tail. -/
theorem atanhBounds_sound {ul uh : ℤ} {u : ℝ}
    (hul : 0 ≤ ul) (huh : uh < (Q : ℤ))
    (hsquare : (oddSquare ul uh).hi < (Q : ℤ))
    (hu : (I80.mk ul uh).Contains u) :
    (atanhBounds ul uh).Contains (Real.log ((1+u)/(1-u))) := by
  obtain ⟨hulow,huhi⟩ := (contains_iff _ _).1 hu
  have hu0 : 0 ≤ u :=
    (div_nonneg (by exact_mod_cast hul) Q_real_pos.le).trans hulow
  have hu1 : u < 1 := huhi.trans_lt ((div_lt_one Q_real_pos).2 (by exact_mod_cast huh))
  let square := oddSquare ul uh
  let state := oddLoop square ul uh 32
  obtain ⟨hp,hp0,hs⟩ := oddLoop_invariant hu hul 32
  obtain ⟨hsl,hsh⟩ := (contains_iff _ _).1 hs
  obtain ⟨hpl,hph⟩ := (contains_iff _ _).1 hp
  change decode state.total.lo ≤ oddSum u 32 at hsl
  change oddSum u 32 ≤ decode state.total.hi at hsh
  change decode state.power.lo ≤ u^65 at hpl
  change u^65 ≤ decode state.power.hi at hph
  have hsq := positiveMul_contains hu hu hul hul
  have hsqhi : u^2 ≤ decode square.hi := by
    simpa only [square,oddSquare,positiveMul,pow_two] using ((contains_iff _ _).1 hsq).2
  have hsqd : 0 < 1-decode square.hi := by
    apply sub_pos.mpr
    exact (div_lt_one Q_real_pos).2 (by exact_mod_cast hsquare)
  have hd : 0 < 1-u^2 := by linarith
  have hph0 : 0 ≤ decode state.power.hi := (pow_nonneg hu0 _).trans hph
  have hrem : 2*u^65/(65*(1-u^2)) ≤
      2*decode state.power.hi/(65*(1-decode square.hi)) := by
    have h1 := div_le_div_of_nonneg_right hph (show (0 : ℝ) ≤ 65*(1-u^2) by positivity)
    have h2 := div_le_div_of_nonneg_left hph0 (show (0 : ℝ) < 65*(1-decode square.hi) by positivity)
      (show 65*(1-decode square.hi) ≤ 65*(1-u^2) by linarith)
    have h12 := mul_le_mul_of_nonneg_left (h1.trans h2) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [mul_div_assoc] using h12
  have htail := real_le_ceilDiv (2*state.power.hi*(Q : ℤ))
    (65*((Q : ℤ)-square.hi)) (by
      have hh : square.hi < (Q : ℤ) := hsquare
      omega)
  have htail' := div_le_div_of_nonneg_right htail Q_real_pos.le
  have he : (((2*state.power.hi*(Q : ℤ) : ℤ) : ℝ) /
        ((65*((Q : ℤ)-square.hi) : ℤ) : ℝ))/(Q : ℝ) =
      2*decode state.power.hi/(65*(1-decode square.hi)) := by
    dsimp [decode]
    push_cast
    have hdiff : (Q : ℝ)-(square.hi : ℝ) ≠ 0 := by
      have hh : (square.hi : ℝ) < (Q : ℝ) := by exact_mod_cast hsquare
      linarith
    field_simp [Q_real_pos.ne',hdiff] <;> ring
  rw [he] at htail'
  change 2*decode state.power.hi/(65*(1-decode square.hi)) ≤
    decode (ceilDiv (2*state.power.hi*(Q : ℤ)) (65*((Q : ℤ)-square.hi))) at htail'
  have hlo := Real.sum_range_le_log_div hu0 hu1 32
  have hhi := sharp_odd_log_upper hu0 hu1 32
  change (atanhBounds ul uh).Contains (Real.log ((1+u)/(1-u)))
  apply (contains_iff _ _).2
  constructor
  · change decode (2*state.total.lo) ≤ _
    have helo : decode (2*state.total.lo) = 2*decode state.total.lo := by
      simp only [decode,Int.cast_mul,Int.cast_ofNat]; ring
    rw [helo]
    have hlo' : oddSum u 32 ≤ 1/2*Real.log ((1+u)/(1-u)) := by
      simpa only [oddSum, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hlo
    linarith only [hlo', hsl]
  · change _ ≤ decode (2*state.total.hi+
        ceilDiv (2*state.power.hi*(Q : ℤ)) (65*((Q : ℤ)-square.hi)))
    have hehi (z : ℤ) : decode (2*state.total.hi+z) =
        2*decode state.total.hi+decode z := by
      simp only [decode,Int.cast_add,Int.cast_mul,Int.cast_ofNat]; ring
    rw [hehi]
    norm_num only [show 2*32+1=65 by norm_num, Nat.cast_ofNat] at hhi
    linarith

theorem logTwoBounds_contains : logTwoBounds.Contains (Real.log 2) := by
  have hu : (I80.mk ((Q : ℤ)/3) (ceilDiv (Q : ℤ) 3)).Contains (1/3 : ℝ) := by
    have hh := divNat_contains (x := I80.raw (Q : ℤ))
      (v := (1 : ℝ)) (by simp [contains_iff,decode,I80.raw,Q_real_pos.ne']) (by norm_num : 0 < 3)
    simpa [divNat, I80.raw] using hh
  have hh := atanhBounds_sound
    (ul := (Q : ℤ)/3) (uh := ceilDiv (Q : ℤ) 3)
    (by norm_num [Q]) (by norm_num [Q,ceilDiv])
    (by norm_num [oddSquare,Q,ceilDiv]) hu
  norm_num at hh
  exact hh

theorem floor_scaled_div (a d : ℤ) (hd : 0 < d) :
    decode (a*(Q : ℤ)/d) ≤ (a : ℝ)/(d : ℝ) := by
  calc
    decode (a*(Q : ℤ)/d) ≤ (((a*(Q : ℤ) : ℤ) : ℝ)/(d : ℝ))/(Q : ℝ) :=
      div_le_div_of_nonneg_right (ediv_le_real _ _ hd) Q_real_pos.le
    _ = _ := by
      push_cast
      have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp [Q_real_pos.ne',hdr] <;> ring

theorem ceil_scaled_div (a d : ℤ) (hd : 0 < d) :
    (a : ℝ)/(d : ℝ) ≤ decode (ceilDiv (a*(Q : ℤ)) d) := by
  calc
    (a : ℝ)/(d : ℝ) = (((a*(Q : ℤ) : ℤ) : ℝ)/(d : ℝ))/(Q : ℝ) := by
      push_cast
      have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp [Q_real_pos.ne',hdr] <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right (real_le_ceilDiv _ _ hd) Q_real_pos.le

/-- Literal ul/uh transformation in log_point, including its crossed
denominators. This is not exact evaluation of an unrounded parameter. -/
theorem reducedParameter_contains {rl rh : ℤ} {r : ℝ}
    (hr : (I80.mk rl rh).Contains r) (hrl : (Q : ℤ) ≤ rl) :
    (reducedParameter rl rh).Contains ((r-1)/(r+1)) := by
  obtain ⟨hlo,hhi⟩ := (contains_iff _ _).1 hr
  have hlo' : (rl : ℝ) ≤ r*(Q : ℝ) := (div_le_iff₀ Q_real_pos).1 hlo
  have hhi' : r*(Q : ℝ) ≤ (rh : ℝ) := (le_div_iff₀ Q_real_pos).1 hhi
  have hrlr : (Q : ℝ) ≤ (rl : ℝ) := by exact_mod_cast hrl
  have hr1 : 1 ≤ r := by nlinarith [Q_real_pos]
  have hrp : 0 < r+1 := by linarith
  have hQpos : (0 : ℤ) < Q := Q_int_pos
  have hdl : 0 < rl+(Q : ℤ) := by omega
  have hdr : 0 < rh+(Q : ℤ) := by
    have horder : rl ≤ rh := by exact_mod_cast (hlo'.trans hhi')
    omega
  have hdlr : (0 : ℝ) < (rl : ℝ)+(Q : ℝ) := by exact_mod_cast hdl
  have hdrr : (0 : ℝ) < (rh : ℝ)+(Q : ℝ) := by exact_mod_cast hdr
  apply (contains_iff _ _).2
  constructor
  · calc
      decode ((reducedParameter rl rh).lo) ≤
          ((rl : ℝ)-(Q : ℝ))/((rh : ℝ)+(Q : ℝ)) := by
        simpa only [reducedParameter,Int.cast_sub,Int.cast_add,Int.cast_natCast] using
          floor_scaled_div (rl-(Q : ℤ)) (rh+(Q : ℤ)) hdr
      _ ≤ (r-1)/(r+1) := by
        apply (div_le_div_iff₀ hdrr hrp).2
        nlinarith [mul_nonneg (show 0 ≤ r-1 by linarith) (sub_nonneg.mpr hhi'),
          mul_nonneg (sub_nonneg.mpr hlo') hrp.le]
  · calc
      (r-1)/(r+1) ≤ ((rh : ℝ)-(Q : ℝ))/((rl : ℝ)+(Q : ℝ)) := by
        apply (div_le_div_iff₀ hrp hdlr).2
        nlinarith [mul_nonneg (show 0 ≤ r-1 by linarith) (sub_nonneg.mpr hlo'),
          mul_nonneg (sub_nonneg.mpr hhi') hrp.le]
      _ ≤ decode ((reducedParameter rl rh).hi) := by
        simpa only [reducedParameter,Int.cast_sub,Int.cast_add,Int.cast_natCast] using
          ceil_scaled_div (rh-(Q : ℤ)) (rl+(Q : ℤ)) hdl

/-- These are entirely integer guards, not assumptions about Real.log.
For each historic query they may be checked without invoking a producer. -/
def ReducedChecks (rl rh : ℤ) : Prop :=
  (Q : ℤ) ≤ rl ∧ 0 ≤ (reducedParameter rl rh).lo ∧
    (reducedParameter rl rh).hi < (Q : ℤ) ∧
    (oddSquare (reducedParameter rl rh).lo (reducedParameter rl rh).hi).hi < (Q : ℤ)

instance (rl rh : ℤ) : Decidable (ReducedChecks rl rh) := by
  unfold ReducedChecks
  infer_instance

def reducedCheck (rl rh : ℤ) : Bool := decide (ReducedChecks rl rh)

/-- The literal range-reduction endpoints imply all tail denominator and
power-loop guards. Rounded uh may exceed Q/3; Q/2 is a safe proved cap. -/
theorem reducedCheck_of_endpoints {rl rh : ℤ}
    (hrl : (Q : ℤ) ≤ rl) (horder : rl ≤ rh) (hrh : rh ≤ 2*(Q : ℤ)) :
    reducedCheck rl rh = true := by
  apply decide_eq_true
  have hd : 0 < rl+(Q : ℤ) := by have hh := Q_int_pos; omega
  have hdh : 0 < rh+(Q : ℤ) := by have hh := Q_int_pos; omega
  let half : ℤ := (Q : ℤ)/2
  let quarter : ℤ := (Q : ℤ)/4
  have hhalf : 0 ≤ half := by norm_num [half,Q]
  have hquarter : 0 ≤ quarter := by norm_num [quarter,Q]
  have hhalfQ : 2*half = (Q : ℤ) := by norm_num [half,Q]
  have hquartQ : quarter*(Q : ℤ) = half^2 := by norm_num [quarter,half,Q]
  have hhalf_lt : half < (Q : ℤ) := by norm_num [half,Q]
  have hquarter_lt : quarter < (Q : ℤ) := by norm_num [quarter,Q]
  have hul : 0 ≤ (reducedParameter rl rh).lo := by
    exact Int.ediv_nonneg (mul_nonneg (by omega) Q_int_pos.le) hdh.le
  have huh0 : 0 ≤ (reducedParameter rl rh).hi := by
    exact ceilDiv_nonnegative (mul_nonneg (by omega) Q_int_pos.le) hd
  have huhcap : (reducedParameter rl rh).hi ≤ half := by
    apply ceilDiv_le _ _ _ hd
    have h1 := mul_le_mul_of_nonneg_right
      (show rh-(Q : ℤ) ≤ (Q : ℤ) by omega) Q_int_pos.le
    have h2 := mul_le_mul_of_nonneg_left
      (show 2*(Q : ℤ) ≤ rl+(Q : ℤ) by omega) hhalf
    nlinarith
  have hsqcap :
      (oddSquare (reducedParameter rl rh).lo (reducedParameter rl rh).hi).hi ≤ quarter := by
    apply ceilDiv_le _ _ _ Q_int_pos
    have hh := mul_nonneg huh0 (sub_nonneg.mpr huhcap)
    nlinarith
  exact ⟨hrl,hul,huhcap.trans_lt hhalf_lt,hsqcap.trans_lt hquarter_lt⟩

theorem reducedLogBounds_contains {rl rh : ℤ} {r : ℝ}
    (hr : (I80.mk rl rh).Contains r) (hc : reducedCheck rl rh = true) :
    (reducedLogBounds rl rh).Contains (Real.log r) := by
  obtain ⟨hrl,hul,huh,hsq⟩ := (of_decide_eq_true hc : ReducedChecks rl rh)
  have hp := reducedParameter_contains hr hrl
  have ha := atanhBounds_sound hul huh hsq hp
  obtain ⟨hlo,hhi⟩ := (contains_iff _ _).1 hr
  have hr1 : 1 ≤ r := by
    have hrr : (Q : ℝ) ≤ (rl : ℝ) := by exact_mod_cast hrl
    have hh := (div_le_iff₀ Q_real_pos).1 hlo
    nlinarith [Q_real_pos]
  have he : (1+(r-1)/(r+1))/(1-(r-1)/(r+1)) = r := by
    field_simp [show r+1 ≠ 0 by linarith,show r ≠ 0 by linarith]
    ring
  rw [he] at ha
  exact ha

/-- The k<0 branch reverses the LOG2 endpoints exactly as Python does. -/
theorem integerScale_contains {x : I80} {v : ℝ} (hx : x.Contains v) (k : ℤ) :
    (integerScale x k).Contains ((k : ℝ)*v) := by
  obtain ⟨hlo,hhi⟩ := (contains_iff _ _).1 hx
  have he (n : ℤ) : decode (k*n) = (k : ℝ)*decode n := by
    simp only [decode,Int.cast_mul]
    ring
  apply (contains_iff _ _).2
  by_cases hk : 0 ≤ k
  · simp only [integerScale,if_pos hk,he]
    have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk
    exact ⟨mul_le_mul_of_nonneg_left hlo hkr,mul_le_mul_of_nonneg_left hhi hkr⟩
  · simp only [integerScale,if_neg hk,he]
    have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hk))
    exact ⟨mul_le_mul_of_nonpos_left hhi hkr,mul_le_mul_of_nonpos_left hlo hkr⟩

theorem logPointFromReduction_contains {k rl rh : ℤ} {r x : ℝ}
    (hr : (I80.mk rl rh).Contains r) (hc : reducedCheck rl rh = true)
    (hidentity : Real.log x = Real.log r+(k : ℝ)*Real.log 2) :
    (logPointFromReduction k rl rh).Contains (Real.log x) := by
  rw [hidentity]
  exact I80.add_contains (reducedLogBounds_contains hr hc)
    (integerScale_contains logTwoBounds_contains k)

/-- Literal log_point: q is a fixed-point INTEGER, not an unrounded rational
argument. Q is a special exact-zero case in the frozen implementation. -/
theorem logPoint_contains {q : ℤ} (hq : 0 < q) :
    (logPoint q).Contains (Real.log ((q : ℝ)/(Q : ℝ))) := by
  by_cases hqQ : q = (Q : ℤ)
  · subst q
    simp [logPoint,I80.raw,contains_iff,decode,Q_real_pos.ne']
  · have hg := P2HistoricLogRangeReduction.source_endpoint_guards hq
    have hc := reducedCheck_of_endpoints hg.1 hg.2.1 hg.2.2
    have hr : (I80.mk (P2HistoricLogRangeReduction.sourceRL q)
        (P2HistoricLogRangeReduction.sourceRH q)).Contains
        (P2HistoricLogRangeReduction.exactReduced q : ℝ) := by
      apply (contains_iff _ _).2
      exact P2HistoricLogRangeReduction.source_reduced_contains_real q
    have hid := P2HistoricLogRangeReduction.log_point_decomposition hq
    have hid' : Real.log ((q : ℝ)/(Q : ℝ)) =
        Real.log (P2HistoricLogRangeReduction.exactReduced q : ℝ)+
          (P2HistoricLogRangeReduction.sourceShift q : ℝ)*Real.log 2 := by
      simpa only [add_comm, P2HistoricLogRangeReduction.Q, Q] using hid
    simpa only [logPoint,if_neg hqQ] using
      logPointFromReduction_contains hr hc hid'

/- Literal log(I(q)): first round q to its old Q80 interval, then use
log_point(lo).lo and log_point(hi).hi. No endpoint is exchanged for the
output of RationalLogCertificate or a differently rounded algorithm. -/
/-- Exact rational-query contract requested by the historical pair engine.
The sole guard is its original `assert x.lo > 0`, after I(q) conversion. -/
theorem logI_contains (q : ℚ) (hpos : 0 < (I80.point q).lo) :
    (logI q).Contains (Real.log (q : ℝ)) := by
  let x := I80.point q
  have hx := (contains_iff x (q : ℝ)).1 (I80.point_contains q)
  have hlo : 0 < decode x.lo := div_pos (by exact_mod_cast hpos) Q_real_pos
  have hq : (0 : ℝ) < q := hlo.trans_le hx.1
  have hhi : 0 < x.hi := by
    have hh : (0 : ℝ) < decode x.hi := hq.trans_le hx.2
    have hh' := (lt_div_iff₀ Q_real_pos).1 hh
    have hiR : (0 : ℝ) < x.hi := by simpa using hh'
    exact_mod_cast hiR
  have hl := (contains_iff _ _).1 (logPoint_contains hpos)
  have hu := (contains_iff _ _).1 (logPoint_contains hhi)
  apply (contains_iff _ _).2
  constructor
  · exact hl.1.trans (Real.log_le_log hlo hx.1)
  · exact (Real.log_le_log hq hx.2).trans hu.2

/-- This stronger hypothesis is often convenient for saved positive ratios:
any rational at least one satisfies the historic rounded-lower guard. -/
theorem logI_contains_of_one_le (q : ℚ) (hq : 1 ≤ q) :
    (logI q).Contains (Real.log (q : ℝ)) := by
  apply logI_contains
  change 0 < ⌊q*(Q : ℚ)⌋
  apply lt_of_lt_of_le (show (0 : ℤ) < 1 by norm_num)
  apply Int.le_floor.mpr
  have hh := mul_le_mul_of_nonneg_right hq Q_pos.le
  have hh' : (Q : ℚ) ≤ q*(Q : ℚ) := by simpa only [one_mul] using hh
  have hQ1 : (1 : ℚ) ≤ Q := by norm_num [Q]
  simpa only [Int.cast_one] using hQ1.trans hh'

/-- The existing rectangle backend can consume the literal old log engine
without an additional logarithm-enclosure hypothesis on either ratio. -/
theorem rectangleMass_logI_contains (tl tr ul ur : ℚ)
    (ht : 1 ≤ tr/tl) (hu : 1 ≤ ur/ul) :
    (rectangleMass logI tl tr ul ur).Contains (rectangleMassValue tl tr ul ur) := by
  exact rectangleMass_contains logI tl tr ul ur
    (logI_contains_of_one_le _ ht) (logI_contains_of_one_le _ hu)

end
end ImbalancedChen.Certificates.P2HistoricLogPointInterpreter
