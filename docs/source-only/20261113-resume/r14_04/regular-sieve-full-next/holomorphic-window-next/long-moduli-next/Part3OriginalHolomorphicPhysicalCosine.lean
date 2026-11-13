import ImbalancedChen.Part3OriginalAllParameterKloosterman

/-! The two actual phase signs and the cubic row weights in the long-modulus
part of the original odd Petersson window. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicPhysicalCosine20261113
open Finset Real
open OriginalSmoothPoissonTail (kloosterman)
open OriginalTwistedSqrtTaylor20261113 (fullFactor)
open OriginalTwistedKloosterman20261113 (twistedForm)
open OriginalAllParameterKloosterman20261113 (dyadEnergy allCost all_parameter_bound twistedForm_conj)
open OAI.Problem337.ExponentialSum (phase)

def scale (c : ℕ) : ℝ := 4*π/c

def argument (c m n : ℕ) : ℝ := scale c * sqrt m * sqrt n

def form (M c : ℕ) (a b : ℕ → ℂ) (W : ℕ → ℕ → ℂ) : ℂ :=
  ∑ i ∈ range (M+1), ∑ j ∈ range (M+1),
    (a (M+i)*b (M+j)*kloosterman c (M+i:ℕ) (M+j:ℕ))*W (M+i) (M+j)

def cosineForm (M c : ℕ) (q : ℝ) (a b : ℕ → ℂ) : ℂ :=
  form M c a b (fun m n => (cos (q*argument c m n):ℂ))

private theorem two_phase (q : ℝ) (c m n : ℕ) :
    (2:ℂ)*(cos (q*argument c m n):ℂ) =
      fullFactor 0 q c (sqrt m) (sqrt n) + fullFactor 0 (-q) c (sqrt m) (sqrt n) := by
  have ep : 2*π*(2*q/(c:ℝ)*sqrt m*sqrt n)=q*argument c m n := by
    dsimp [argument,scale]
    ring
  have en : 2*π*(2*(-q)/(c:ℝ)*sqrt m*sqrt n)=-(q*argument c m n) := by
    dsimp [argument,scale]
    ring
  simp only [fullFactor,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,one_mul,phase,
    ep,en,Complex.ofReal_neg,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg,Complex.ofReal_cos]
  ring

theorem cosine_signs (M c : ℕ) (q : ℝ) (a b : ℕ → ℂ) :
    (2:ℂ)*cosineForm M c q a b = twistedForm M c 0 q a b + twistedForm M c 0 (-q) a b := by
  simp only [cosineForm,form,twistedForm,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [←mul_add,←two_phase]
  ring

private theorem long_cost {M c : ℕ} (hc : M≤c) {q : ℝ} (hq : q≤1) :
    allCost M c q ≤ 3*(c:ℝ) := by
  have cm : (M:ℝ)≤c := by exact_mod_cast hc
  have q1 := mul_le_mul_of_nonneg_right hq (mul_nonneg (Nat.cast_nonneg c) (Nat.cast_nonneg M))
  have m1 := mul_le_mul_of_nonneg_left cm (Nat.cast_nonneg c : 0≤(c:ℝ))
  have sq : sqrt (q*c*M)≤(c:ℝ) := Real.sqrt_le_iff.mpr
    ⟨Nat.cast_nonneg _,by nlinarith only [q1,m1]⟩
  dsimp only [allCost]
  linarith only [cm,sq]

private theorem star_energy (M : ℕ) (a : ℕ → ℂ) :
    dyadEnergy M (fun m => star (a m))=dyadEnergy M a := by simp [dyadEnergy]

theorem cosine_long_bound {M c : ℕ} [NeZero c] (hM : 0<M) (hc : M≤c)
    {q : ℝ} (h0 : 0≤q) (h1 : q≤1) (a b : ℕ → ℂ) :
    ‖cosineForm M c q a b‖ ≤ 12*exp (4*π)*c*sqrt (dyadEnergy M a)*sqrt (dyadEnergy M b) := by
  have pos (u v : ℕ → ℂ) : ‖twistedForm M c 0 q u v‖ ≤
      12*exp (4*π)*c*sqrt (dyadEnergy M u)*sqrt (dyadEnergy M v) := by
    apply (all_parameter_bound M c hM (le_refl 0) h0 u v).trans
    apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
    have z := mul_le_mul_of_nonneg_left (long_cost hc h1) (show 0≤4*exp (4*π) by positivity)
    linarith only [z]
  have n := pos (fun m => star (a m)) (fun m => star (b m))
  rw [star_energy,star_energy] at n
  have n' : ‖twistedForm M c 0 (-q) a b‖ ≤
      12*exp (4*π)*c*sqrt (dyadEnergy M a)*sqrt (dyadEnergy M b) := by
    simpa only [twistedForm_conj M c 0 q a b,norm_star] using n
  have d := norm_add_le (twistedForm M c 0 q a b) (twistedForm M c 0 (-q) a b)
  rw [←cosine_signs,norm_mul] at d
  norm_num only [Complex.norm_ofNat] at d
  linarith only [d,n',pos a b]

def cubicRow (a : ℕ → ℂ) (m : ℕ) : ℂ := ((sqrt m)^3:ℝ)*a m

def rowCost (M : ℕ) : ℝ := (sqrt (2*(M:ℝ)))^3

theorem row_cost_square (M : ℕ) : (rowCost M)^2=8*(M:ℝ)^3 := by
  have eq : (sqrt (2*(M:ℝ))^3)^2=(sqrt (2*(M:ℝ))^2)^3 := by ring
  rw [rowCost,eq,sq_sqrt (by positivity)]
  ring

theorem cubic_row_energy (M : ℕ) (a : ℕ → ℂ) :
    sqrt (dyadEnergy M (cubicRow a)) ≤ rowCost M*sqrt (dyadEnergy M a) := by
  have h0 : 0≤rowCost M := pow_nonneg (sqrt_nonneg _) _
  have h : dyadEnergy M (cubicRow a)≤(rowCost M)^2*dyadEnergy M a := by
    dsimp only [dyadEnergy]
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have ih := mem_range.mp hi
    have mi : (↑(M+i):ℝ)≤2*(M:ℝ) := by exact_mod_cast (show M+i≤2*M by omega)
    have c0 := pow_nonneg (sqrt_nonneg (↑(M+i):ℝ)) 3
    have p := pow_le_pow_left₀ (sqrt_nonneg (↑(M+i):ℝ)) (sqrt_le_sqrt mi) 3
    have p2 := pow_le_pow_left₀ c0 p 2
    simpa only [cubicRow,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg c0,mul_pow,rowCost]
      using mul_le_mul_of_nonneg_right p2 (sq_nonneg ‖a (M+i)‖)
  simpa only [sqrt_mul (sq_nonneg _),sqrt_sq h0] using sqrt_le_sqrt h

end ImbalancedChen.Part3.OriginalHolomorphicPhysicalCosine20261113
end
