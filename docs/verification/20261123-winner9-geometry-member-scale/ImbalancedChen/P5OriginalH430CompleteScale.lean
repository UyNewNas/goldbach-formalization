import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Complete scales on both sides of the global residue. The original
box capacities and modulus endpoints are retained while the old chart
inequalities are evaluated at min(x,N) with seven eighths of zeta. -/
namespace ImbalancedChen.P5OriginalH430CompleteScale
noncomputable section
open Filter
open scoped Topology

/-- Fix the two constants of the original dyadic complete-scale window
and the parameters in manuscript order. Uniformly on this entire window,
the actual medium capacity is also legal at the auxiliary complete scale.
The original residue and both of its actual-size comparisons are retained. -/
theorem eventually_complete_scale {c C z k k0 : ℝ} (hc : 0<c) (hC : 0<C)
    (hz : 0<z) (hz' : z≤1/100) (hk : 0<k) (hk0 : k0<k/(4*(1+k))) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, c*(N:ℝ)^(1-k0)≤x → x≤C*(N:ℝ) →
      let y := min x (N:ℝ)
      let q := Real.logb y (N:ℝ)
      1<x ∧ 1/C*x≤(N:ℝ) ∧ (N:ℝ)≤x^(1+k) ∧ x^(Real.logb x (N:ℝ))=(N:ℝ) ∧
      1<y ∧ y≤x ∧ y^q=(N:ℝ) ∧ 1≤q ∧ q≤1+k ∧
      x^(1/3-z/2)≤y^(1/3-(7*z/8)/2) := by
  let g := k/(4*(1+k))
  have hk1 : 0<1+k := by linarith
  have hg : 0<g := div_pos hk (by positivity)
  have hge : g*(1+k)=k/4 := by dsimp only [g]; field_simp [ne_of_gt hk1] <;> ring
  have hgt := mul_lt_mul_of_pos_right (show k0<g from hk0) hk1
  have hlarge : 1≤(1-k0-g)*(1+k) := by nlinarith only [hgt,hge,hk]
  have hlow : 0<1-k0-g := by
    by_contra! h
    linarith only [hlarge,mul_nonpos_of_nonpos_of_nonneg h hk1.le]
  have grow (e : ℝ) (he : 0<e) (M : ℝ) : ∀ᶠ N : ℕ in atTop, M≤(N:ℝ)^e :=
    ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop M)
  filter_upwards [grow g hg (1/c),grow (z/16) (by positivity) C,eventually_ge_atTop (2:ℕ)] with N hsmall hconst hN
  intro x hlo hhi
  dsimp only
  let y := min x (N:ℝ)
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hNp := zero_lt_one.trans hNr
  have hcN : 1≤c*(N:ℝ)^g := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hsmall
  have hbase : (N:ℝ)^(1-k0-g)≤x := calc
    _ ≤ (N:ℝ)^(1-k0-g)*(c*(N:ℝ)^g) := le_mul_of_one_le_right (Real.rpow_nonneg hNp.le _) hcN
    _ = c*((N:ℝ)^(1-k0-g)*(N:ℝ)^g) := by ring
    _ = c*(N:ℝ)^(1-k0) := by rw [←Real.rpow_add hNp,sub_add_cancel]
    _ ≤ x := hlo
  have hx : 1<x := (Real.one_lt_rpow hNr hlow).trans_le hbase
  have hxN : (N:ℝ)≤x^(1+k) := calc
    (N:ℝ) = (N:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ (N:ℝ)^((1-k0-g)*(1+k)) := Real.rpow_le_rpow_of_exponent_le hNr.le hlarge
    _ = ((N:ℝ)^(1-k0-g))^(1+k) := Real.rpow_mul hNp.le _ _
    _ ≤ x^(1+k) := Real.rpow_le_rpow (Real.rpow_nonneg hNp.le _) hbase hk1.le
  have hy : 1<y := lt_min hx hNr
  have hyN : (N:ℝ)≤y^(1+k) := by
    rcases le_total x (N:ℝ) with h | h
    · simpa only [y,min_eq_left h] using hxN
    · dsimp only [y]; rw [min_eq_right h]
      simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hNr.le (show (1:ℝ)≤1+k by linarith))
  have hCx : 1/C*x≤(N:ℝ) := by
    rw [div_mul_eq_mul_div,one_mul]
    exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hhi)
  refine ⟨hx,hCx,hxN,Real.rpow_logb (zero_lt_one.trans hx) hx.ne' hNp,hy,min_le_left _ _,
    Real.rpow_logb (zero_lt_one.trans hy) hy.ne' hNp,
    (Real.le_logb_iff_rpow_le hy hNp).mpr (by simpa only [Real.rpow_one] using (min_le_right x (N:ℝ))),
    (Real.logb_le_iff_le_rpow hy hNp).mpr hyN,?_⟩
  rcases le_total x (N:ℝ) with h | h
  · rw [min_eq_left h]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [hz])
  · rw [min_eq_right h]
    have hX : x≤(N:ℝ)^(1+z/16) := calc
      x ≤ C*(N:ℝ) := hhi
      _ ≤ (N:ℝ)^(z/16)*(N:ℝ) := mul_le_mul_of_nonneg_right hconst hNp.le
      _ = (N:ℝ)^(1+z/16) := by rw [Real.rpow_add hNp,Real.rpow_one,mul_comm]
    calc
      x^(1/3-z/2) ≤ ((N:ℝ)^(1+z/16))^(1/3-z/2) :=
        Real.rpow_le_rpow (zero_lt_one.trans hx).le hX (by linarith only [hz'])
      _ = (N:ℝ)^((1+z/16)*(1/3-z/2)) := (Real.rpow_mul hNp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNr.le (by nlinarith only [hz,sq_nonneg z])

/-- Recover the original U=A*x^z and sigma=z/2000 after evaluating
all three unspent group estimates with z'=7*z/8 at the auxiliary y.
R is the actual positive global numerator. Only group three receives M. -/
theorem full_trim_medium_ranges {x y R z A a b c M : ℝ} (hx : 1<x) (hy : 0<y) (hyx : y≤x)
    (hR : 0<R) (hz : 0<z) (hz' : z≤1/100) (hA : 0<A) (ha : 0<a) (hb : 0<b)
    (hc : 0<c) (hM : 0<M) (hbeta : M≤x^(z/8)) (h1 : a≤A)
    (h2 : A^2*b*c^2≤y^(1-3*(7*z/8))) (h3 : R^(7/32:ℝ)*A*a*b^5*c^2≤y^(2-4*(7*z/8)))
    (h4 : (A*c/b)^(7/16:ℝ)*A*a*b^5*c^2≤y^(2-39*(7*z/8)/8)) :
    let U := A*x^z
    let Q3 := M*c
    let sigma := z/2000
    a<U*x^(-sigma) ∧ U^2*b*Q3^2<x^(1-8*sigma) ∧ R^(7/32:ℝ)*U*a*b^5*Q3^2<x^(2-15*sigma) ∧
      U^(1+7/16:ℝ)*a*b^(5-7/16:ℝ)*Q3^(2+7/16:ℝ)<x^(2-15*sigma) := by
  dsimp only
  have hx0 := zero_lt_one.trans hx
  have hzL := mul_pos hz (Real.log_pos hx)
  have hMlog := (Real.le_rpow_iff_log_le hM hx0).mp hbeta
  have hAlog := Real.log_le_log ha h1
  have lift (s : ℝ) (hs : 0≤s) : y^s≤x^s := Real.rpow_le_rpow hy.le hyx hs
  have H2 := (Real.le_rpow_iff_log_le (by positivity) hx0).mp (h2.trans (lift _ (by linarith only [hz'])))
  have H3 := (Real.le_rpow_iff_log_le (by positivity) hx0).mp (h3.trans (lift _ (by linarith only [hz'])))
  have H4 := (Real.le_rpow_iff_log_le (by positivity) hx0).mp (h4.trans (lift _ (by linarith only [hz'])))
  simp (disch := positivity) only [Real.log_mul,Real.log_rpow,Real.log_div,Real.log_pow,Nat.cast_ofNat] at H2 H3 H4
  refine ⟨?_,?_,?_,?_⟩
  · apply (Real.log_lt_log_iff ha (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul,Real.log_rpow]
    nlinarith only [hAlog,hzL]
  · apply (Real.lt_rpow_iff_log_lt (by positivity) hx0).mpr
    simp (disch := positivity) only [Real.log_mul,Real.log_rpow,Real.log_pow,Nat.cast_ofNat]
    nlinarith only [H2,hMlog,hzL]
  · apply (Real.lt_rpow_iff_log_lt (by positivity) hx0).mpr
    simp (disch := positivity) only [Real.log_mul,Real.log_rpow,Real.log_pow,Nat.cast_ofNat]
    nlinarith only [H3,hMlog,hzL]
  · apply (Real.lt_rpow_iff_log_lt (by positivity) hx0).mpr
    simp (disch := positivity) only [Real.log_mul,Real.log_rpow,Real.log_pow,Nat.cast_ofNat]
    nlinarith only [H4,hMlog,hzL]

end
end ImbalancedChen.P5OriginalH430CompleteScale
