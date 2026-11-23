import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! A rational polynomial certificate for the four one-dimensional functions
in the switched costs. Its derivative and anchor tests are finite rational
arithmetic. The integral is the real Lebesgue interval integral. -/
namespace ImbalancedChen.P6OriginalLogPolynomialBound

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval

abbrev Coeffs := List ℚ

def ev : Coeffs → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * ev p x

def add : Coeffs → Coeffs → Coeffs
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a+b) :: add p q

def scale (a : ℚ) (p : Coeffs) : Coeffs := p.map (a * ·)

def mul : Coeffs → Coeffs → Coeffs
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

theorem ev_add (p q : Coeffs) (x : ℝ) : ev (add p q) x = ev p x + ev q x := by
  induction p generalizing q with
  | nil => simp [ev, add]
  | cons a p ih => cases q with
    | nil => simp [ev, add]
    | cons b q => simp only [add, ev, Rat.cast_add, ih]; ring

theorem ev_scale (a : ℚ) (p : Coeffs) (x : ℝ) : ev (scale a p) x = (a : ℝ) * ev p x := by
  induction p with
  | nil => simp [scale, ev]
  | cons b p ih =>
    change ((a*b : ℚ) : ℝ) + x * ev (scale a p) x = _
    rw [Rat.cast_mul, ih, ev]
    ring

theorem ev_mul (p q : Coeffs) (x : ℝ) : ev (mul p q) x = ev p x * ev q x := by
  induction p with
  | nil => simp [ev, mul]
  | cons a p ih => simp only [mul, ev_add, ev_scale, ev, Rat.cast_zero, zero_add, ih]; ring

def first : Coeffs → ℚ
  | [] => 0
  | a :: _ => a

theorem ev_zero (p : Coeffs) : ev p 0 = (first p : ℝ) := by cases p <;> simp [ev, first]
theorem ev_one (p : Coeffs) : ev p 1 = (p.sum : ℝ) := by
  induction p with
  | nil => simp [ev]
  | cons a p ih => simp [ev, ih]

def negativeMass : Coeffs → ℚ
  | [] => 0
  | a :: p => min a 0 + negativeMass p

def lower : Coeffs → ℚ
  | [] => 0
  | a :: p => a + negativeMass p

private theorem mass_estimates (p : Coeffs) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    (negativeMass p : ℝ) ≤ 0 ∧ (negativeMass p : ℝ) ≤ x * ev p x := by
  induction p with
  | nil => simp [negativeMass, ev]
  | cons a p ih =>
    have h0 : ((min a 0 : ℚ):ℝ) ≤ 0 := by exact_mod_cast min_le_right a (0:ℚ)
    have ha : ((min a 0 : ℚ):ℝ) ≤ (a:ℝ) := by exact_mod_cast min_le_left a (0:ℚ)
    have hm0 : ((negativeMass p : ℝ) + ((min a 0 : ℚ):ℝ)) ≤ 0 := add_nonpos ih.1 h0
    have hm : ((min a 0 : ℚ):ℝ) + (negativeMass p : ℝ) ≤ (a : ℝ) + x * ev p x :=
      add_le_add ha ih.2
    have hscale : ((min a 0 : ℚ):ℝ) + (negativeMass p : ℝ) ≤
        x * (((min a 0 : ℚ):ℝ) + (negativeMass p : ℝ)) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx.2) (neg_nonneg.mpr hm0)]
    simp only [negativeMass, Rat.cast_add, ev]
    exact ⟨by linarith, hscale.trans (mul_le_mul_of_nonneg_left hm hx.1)⟩

theorem lower_le_ev (p : Coeffs) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : (lower p : ℝ) ≤ ev p x := by
  cases p with
  | nil => simp [lower, ev]
  | cons a p => simpa only [lower, ev, Rat.cast_add] using add_le_add (le_refl (a:ℝ)) (mass_estimates p hx).2

def weighted (n : ℕ) : Coeffs → Coeffs
  | [] => []
  | a :: p => ((n:ℚ)*a) :: weighted (n+1) p

def derivative (p : Coeffs) : Coeffs := weighted 1 p.tail

private theorem ev_weighted_succ (p : Coeffs) (n : ℕ) (x : ℝ) :
    ev (weighted (n+1) p) x = ev (weighted n p) x + ev p x := by
  induction p generalizing n with
  | nil => simp [weighted, ev]
  | cons a p ih =>
    simp only [weighted, ev, Rat.cast_mul, Rat.cast_natCast, Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_one]
    rw [ih (n+1)]
    ring

private theorem ev_weighted_zero (p : Coeffs) (x : ℝ) :
    ev (weighted 0 p) x = x * ev (derivative p) x := by
  cases p <;> simp [weighted, derivative, ev]

theorem hasDeriv_ev (p : Coeffs) (x : ℝ) : HasDerivAt (ev p) (ev (derivative p) x) x := by
  induction p with
  | nil => simpa [ev, derivative, weighted] using hasDerivAt_const x (0:ℝ)
  | cons a p ih =>
    change HasDerivAt (fun y : ℝ => (a:ℝ) + y * ev p y) (ev (weighted 1 p) x) x
    have hval : ev (weighted 1 p) x = x * ev (derivative p) x + ev p x := by
      simpa only [zero_add, ev_weighted_zero] using ev_weighted_succ p 0 x
    apply (((hasDerivAt_id x).mul ih).const_add (a:ℝ)).congr_deriv
    rw [hval]
    simp only [id_eq, one_mul]
    <;> ring

theorem ev_continuous (p : Coeffs) : Continuous (ev p) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDeriv_ev p x).continuousAt)

def divided (n : ℕ) : Coeffs → Coeffs
  | [] => []
  | a :: p => (a/(n:ℚ)) :: divided (n+1) p

def primitive (p : Coeffs) : Coeffs := 0 :: divided 1 p
def average (p : Coeffs) : ℚ := (divided 1 p).sum

private theorem weighted_divided (p : Coeffs) (n : ℕ) (hn : 0<n) :
    weighted n (divided n p) = p := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih =>
    have hnq : (n:ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [divided, weighted, ih (n+1) (Nat.zero_lt_succ _), List.cons.injEq, and_true]
    field_simp

theorem derivative_primitive (p : Coeffs) : derivative (primitive p) = p := weighted_divided p 1 (by decide)

theorem integral_reverse_polynomial (p : Coeffs) {l r : ℝ} (hlr : l<r) :
    (∫ t in l..r, ev p ((r-t)/(r-l))) = (r-l)*(average p:ℝ) := by
  have hw := sub_pos.mpr hlr
  let z := fun t : ℝ => (r-t)/(r-l)
  have hz (t : ℝ) : HasDerivAt z (-1/(r-l)) t :=
    ((hasDerivAt_id t).const_sub r).div_const (r-l)
  have hprim (t : ℝ) : HasDerivAt (fun u : ℝ => -(r-l)*ev (primitive p) (z u)) (ev p (z t)) t := by
    have h := (((hasDeriv_ev (primitive p) (z t)).comp t (hz t)).const_mul (-(r-l)))
    rw [derivative_primitive] at h
    apply h.congr_deriv
    field_simp [hw.ne']
    <;> ring
  have hc : Continuous (fun t : ℝ => ev p (z t)) :=
    (ev_continuous p).comp ((continuous_const.sub continuous_id).div_const _)
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=l) (b:=r) (fun t _ => hprim t)
    (hc.intervalIntegrable l r)
  have hzr : z r = 0 := by simp [z]
  have hzl : z l = 1 := by simp [z, hw.ne']
  simpa only [z, sub_self, zero_div, div_self hw.ne', ev_zero, first, Rat.cast_zero, mul_zero,
    ev_one, primitive, List.sum_cons, zero_add, average, zero_sub, neg_mul, neg_neg] using hft

structure LogRow where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  den : Coeffs
  p : Coeffs

def decode (ns : List ℤ) : Coeffs := ns.map (fun z => (z : ℚ)/1000000000000000000000000)

def LogRow.anchor (w : LogRow) : ℚ := first w.den * first w.p
def expLower (y : ℚ) : ℚ := ∑ i ∈ Finset.range 24, y^i / (i.factorial : ℚ)

def LogRow.residual (w : LogRow) : Coeffs :=
  add (mul (mul [w.a,w.b] [w.c,w.d]) (derivative (mul w.den w.p))) [w.a*w.d-w.b*w.c]

def LogRow.Valid (w : LogRow) : Prop :=
  0 < lower [w.a,w.b] ∧ 0 < lower [w.c,w.d] ∧ 0 < lower w.den ∧
  0 ≤ w.anchor ∧ w.a/w.c ≤ expLower w.anchor ∧ 0 ≤ lower w.residual

instance (w : LogRow) : Decidable w.Valid := inferInstanceAs (Decidable
  (0 < lower [w.a,w.b] ∧ 0 < lower [w.c,w.d] ∧ 0 < lower w.den ∧
   0 ≤ w.anchor ∧ w.a/w.c ≤ expLower w.anchor ∧ 0 ≤ lower w.residual))

theorem LogRow.bound (w : LogRow) (hv : w.Valid) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    Real.log (((w.a:ℝ)+x*(w.b:ℝ))/((w.c:ℝ)+x*(w.d:ℝ))) / ev w.den x ≤ ev w.p x := by
  obtain ⟨ha,hc,hD,hanc,hex,hres⟩ := hv
  let A (z : ℝ) := (w.a:ℝ)+z*(w.b:ℝ)
  let B (z : ℝ) := (w.c:ℝ)+z*(w.d:ℝ)
  have positive (u v : ℚ) (hu : 0 < lower [u,v]) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) :
      0 < (u:ℝ)+z*v := by
    have h := (show (0:ℝ)<(lower [u,v]:ℝ) by exact_mod_cast hu).trans_le (lower_le_ev [u,v] hz)
    simpa [ev] using h
  have hA {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : 0 < A z := positive _ _ ha hz
  have hB {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : 0 < B z := positive _ _ hc hz
  have hz0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have hDpos : 0 < ev w.den x :=
    (show (0:ℝ)<(lower w.den:ℝ) by exact_mod_cast hD).trans_le (lower_le_ev w.den hx)
  let P := mul w.den w.p
  let V (z : ℝ) := ev P z - (Real.log (A z) - Real.log (B z))
  let V' (z : ℝ) := ev (derivative P) z - ((w.b:ℝ)/A z - (w.d:ℝ)/B z)
  have hder (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) : HasDerivAt V (V' z) z := by
    have da : HasDerivAt A (w.b:ℝ) z := by simpa [A] using
      (((hasDerivAt_id z).mul_const (w.b:ℝ)).const_add (w.a:ℝ))
    have db : HasDerivAt B (w.d:ℝ) z := by simpa [B] using
      (((hasDerivAt_id z).mul_const (w.d:ℝ)).const_add (w.c:ℝ))
    exact (hasDeriv_ev P z).sub ((da.log (hA hz).ne').sub (db.log (hB hz).ne'))
  have hderpos (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) : 0 ≤ V' z := by
    have ht : (0:ℝ) ≤ ev w.residual z :=
      (show (0:ℝ) ≤ (lower w.residual:ℝ) by exact_mod_cast hres).trans (lower_le_ev _ hz)
    have hn : ev w.residual z = (A z*B z)*V' z := by
      simp only [LogRow.residual, ev_add, ev_mul, ev, Rat.cast_sub, Rat.cast_mul, mul_zero, add_zero]
      dsimp only [A,B,V',P]
      have h1 := (hA hz).ne'
      have h2 := (hB hz).ne'
      dsimp only [A,B] at h1 h2
      field_simp [h1,h2]
      <;> ring
    exact nonneg_of_mul_nonneg_right (hn ▸ ht) (mul_pos (hA hz) (hB hz))
  have hmon : MonotoneOn V (Icc (0:ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (f':=V') (convex_Icc _ _)
      (fun z hz => (hder z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hder z (interior_subset hz)).hasDerivWithinAt)
      (fun z hz => hderpos z (interior_subset hz))
  have he : (expLower w.anchor:ℝ) ≤ Real.exp (w.anchor:ℝ) := by
    have hp := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ (w.anchor:ℝ) by exact_mod_cast hanc) 24
    simpa only [expLower, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using hp
  have hh : Real.log (A 0 / B 0) ≤ (w.anchor:ℝ) := by
    apply (Real.log_le_iff_le_exp (div_pos (hA hz0) (hB hz0))).mpr
    have hfrac : ((w.a/w.c:ℚ):ℝ) ≤ (expLower w.anchor:ℝ) := by exact_mod_cast hex
    simpa [A,B] using hfrac.trans he
  have hge : 0 ≤ V 0 := by
    unfold V
    rw [← Real.log_div (hA hz0).ne' (hB hz0).ne', sub_nonneg, ev_mul, ev_zero, ev_zero]
    simpa only [LogRow.anchor, Rat.cast_mul] using hh
  have htarget := hge.trans (hmon hz0 hx hx.1)
  change 0 ≤ ev P x - (Real.log (A x) - Real.log (B x)) at htarget
  rw [← Real.log_div (hA hx).ne' (hB hx).ne', sub_nonneg] at htarget
  apply (div_le_iff₀ hDpos).mpr
  simpa only [P,ev_mul,mul_comm (ev w.p x)] using htarget

end
end ImbalancedChen.P6OriginalLogPolynomialBound
