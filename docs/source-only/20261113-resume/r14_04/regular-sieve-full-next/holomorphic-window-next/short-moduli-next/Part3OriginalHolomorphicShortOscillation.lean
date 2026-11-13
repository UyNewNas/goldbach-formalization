import ImbalancedChen.Part3OriginalHolomorphicPhysicalCosine

/-! The strongly oscillatory cosine and sine forms on the original
physical progression, retaining the exact square root of frequency loss. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicShortOscillation20261113
open Finset Real
open OriginalHolomorphicPhysicalCosine20261113
open OriginalTwistedKloosterman20261113 (twistedForm twisted_form_bound)
open OriginalTwistedSqrtAnalysis20261113 (budget)
open OriginalTwistedSqrtTaylor20261113 (fullFactor)
open OriginalAllParameterKloosterman20261113 (dyadEnergy twistedForm_conj)
open OAI.Problem337.ExponentialSum (phase)

def sineForm (M c : ℕ) (q : ℝ) (a b : ℕ → ℂ) : ℂ :=
  form M c a b (fun m n => (sin (q*argument c m n):ℂ))

private theorem sine_factors (q : ℝ) (c m n : ℕ) :
    ((2:ℂ)*Complex.I)*(sin (q*argument c m n):ℂ) =
      fullFactor 0 q c (sqrt m) (sqrt n) - fullFactor 0 (-q) c (sqrt m) (sqrt n) := by
  have ep : 2*π*(2*q/(c:ℝ)*sqrt m*sqrt n)=q*argument c m n := by
    dsimp [argument,scale]; ring
  have en : 2*π*(2*(-q)/(c:ℝ)*sqrt m*sqrt n)=-(q*argument c m n) := by
    dsimp [argument,scale]; ring
  simp only [fullFactor,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,one_mul,phase,
    ep,en,Complex.ofReal_neg,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg,Complex.ofReal_sin]
  ring

theorem sine_signs (M c : ℕ) (q : ℝ) (a b : ℕ → ℂ) :
    ((2:ℂ)*Complex.I)*sineForm M c q a b =
      twistedForm M c 0 q a b - twistedForm M c 0 (-q) a b := by
  simp only [sineForm,form,twistedForm,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [←mul_sub,←sine_factors]
  ring

def oscillationCost (M c : ℕ) : ℝ := exp (4*π)*sqrt ((c:ℝ)*(244*M*(1+log M)))

def rowProduct (M : ℕ) (a b : ℕ → ℂ) : ℝ := sqrt (dyadEnergy M a)*sqrt (dyadEnergy M b)

theorem row_product_nonnegative (M : ℕ) (a b : ℕ → ℂ) : 0≤rowProduct M a b :=
  mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)

theorem oscillation_cost_nonnegative (M c : ℕ) : 0≤oscillationCost M c :=
  mul_nonneg (exp_pos _).le (sqrt_nonneg _)

theorem short_oscillation {M c : ℕ} [NeZero c] (hc : c≤M)
    {q : ℝ} (hq : 0<q) (hq2 : q≤2) (a b : ℕ → ℂ) :
    ‖cosineForm M c q a b‖ ≤ oscillationCost M c*rowProduct M a b/sqrt q ∧
    ‖sineForm M c q a b‖ ≤ oscillationCost M c*rowProduct M a b/sqrt q := by
  have m1 : 1≤(M:ℝ) := by exact_mod_cast (show 1≤M from (NeZero.pos c).trans_le hc)
  have n0 : 0≤(c:ℝ)*(244*M*(1+log M)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) (by linarith only [log_nonneg m1]))
  have pos (u v : ℕ → ℂ) : ‖twistedForm M c 0 q u v‖ ≤
      oscillationCost M c*rowProduct M u v/sqrt q := by
    apply (twisted_form_bound hc (le_refl 0) hq hq2 u v).trans_eq
    dsimp only [rowProduct,oscillationCost,dyadEnergy,budget]
    rw [show (c:ℝ)*(244*M*(1+log M)/q)=((c:ℝ)*(244*M*(1+log M)))/q by ring,
      sqrt_div n0]
    ring
  have neg : ‖twistedForm M c 0 (-q) a b‖ ≤ oscillationCost M c*rowProduct M a b/sqrt q := by
    simpa [twistedForm_conj M c 0 q a b,rowProduct,dyadEnergy] using
      pos (fun m => star (a m)) (fun m => star (b m))
  constructor
  · have h := norm_add_le (twistedForm M c 0 q a b) (twistedForm M c 0 (-q) a b)
    rw [←cosine_signs,norm_mul,Complex.norm_two] at h
    linarith only [h,pos a b,neg]
  · have h := norm_sub_le (twistedForm M c 0 q a b) (twistedForm M c 0 (-q) a b)
    rw [←sine_signs,norm_mul,norm_mul,Complex.norm_two,Complex.norm_I,mul_one] at h
    linarith only [h,pos a b,neg]

def rootRow (a : ℕ → ℂ) (m : ℕ) : ℂ := (sqrt m:ℂ)*a m

theorem root_row_product (M : ℕ) (a b : ℕ → ℂ) :
    rowProduct M (rootRow a) (rootRow b) ≤ (2*(M:ℝ))*rowProduct M a b := by
  have cap (u : ℕ → ℂ) : sqrt (dyadEnergy M (rootRow u)) ≤ sqrt (2*(M:ℝ))*sqrt (dyadEnergy M u) := by
    have h : dyadEnergy M (rootRow u)≤2*(M:ℝ)*dyadEnergy M u := by
      dsimp only [dyadEnergy]
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      have h0 : (↑(M+i):ℝ)≤2*(M:ℝ) := by
        have hi' := mem_range.mp hi
        exact_mod_cast (show M+i≤2*M by omega)
      simpa only [rootRow,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (sqrt_nonneg _),mul_pow,sq_sqrt (Nat.cast_nonneg _)]
        using mul_le_mul_of_nonneg_right h0 (sq_nonneg ‖u (M+i)‖)
    simpa only [sqrt_mul (show 0≤2*(M:ℝ) by positivity)] using sqrt_le_sqrt h
  have h := mul_le_mul (cap a) (cap b) (sqrt_nonneg _) (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
  apply h.trans_eq
  dsimp only [rowProduct]
  calc
    _ = (sqrt (2*(M:ℝ)))^2*(sqrt (dyadEnergy M a)*sqrt (dyadEnergy M b)) := by ring
    _ = _ := by rw [sq_sqrt (by positivity)]

end ImbalancedChen.Part3.OriginalHolomorphicShortOscillation20261113
end
