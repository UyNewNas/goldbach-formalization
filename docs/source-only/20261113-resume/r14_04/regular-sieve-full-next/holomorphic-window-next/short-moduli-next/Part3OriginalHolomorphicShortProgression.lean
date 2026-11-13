import ImbalancedChen.Part3OriginalHolomorphicShortAngleBounds

/-! Balanced square-root angular cutoff for every short same-cusp modulus
and its complete finite progression at the original level. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicShortProgression20261113
open Real Finset
open OriginalHolomorphicOddWindow20261113 (amplitudeConstant)
open OriginalHolomorphicPhysicalCosine20261113 (form argument scale)
open OriginalHolomorphicLongModulus20261113 (rawWindow)
open OriginalHolomorphicShortOscillation20261113
open OriginalHolomorphicShortAngleBounds20261113 (ampCost short_angle_bound)

def balancedConstant : ℝ := 8*π/sqrt (cos 1)+(π/2)/sqrt (cos 1)+π/2

def shortBill (M : ℕ) (a b : ℕ → ℂ) : ℝ :=
  balancedConstant*amplitudeConstant*exp (4*π)*M*sqrt (244*(1+log M))*rowProduct M a b

private theorem short_bill_nonnegative (M : ℕ) (a b : ℕ → ℂ) : 0≤shortBill M a b := by
  have e := row_product_nonnegative M a b
  dsimp only [shortBill,balancedConstant,amplitudeConstant]
  positivity

theorem short_modulus_bound {M c : ℕ} [NeZero c] (hc : c≤M)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) (a b : ℕ → ℂ) :
    ‖form M c a b (fun m n => (rawWindow t (argument c m n):ℂ))‖ ≤ shortBill M a b := by
  let Δ := sqrt ((c:ℝ)/M)
  let E := ampCost M c a b
  have cp : 0<(c:ℝ) := by exact_mod_cast NeZero.pos c
  have mp : 0<(M:ℝ) := by exact_mod_cast (NeZero.pos c).trans_le hc
  have cm : (c:ℝ)≤M := by exact_mod_cast hc
  have d0 : 0<Δ := sqrt_pos.mpr (div_pos cp mp)
  have d1 : Δ≤1 := by simpa only [sqrt_one] using sqrt_le_sqrt ((div_le_one mp).mpr cm)
  have d2 : Δ^2=(c:ℝ)/M := sq_sqrt (div_nonneg cp.le mp.le)
  have key : (M:ℝ)*Δ^2=c := by rw [d2]; field_simp [mp.ne'] <;> ring
  have e0 : 0≤E := mul_nonneg (by dsimp [amplitudeConstant]; positivity)
    (mul_nonneg (oscillation_cost_nonnegative _ _) (row_product_nonnegative _ _ _))
  have hπ : Δ≤π/2 := by linarith only [d1,pi_gt_three]
  have J := mul_le_sin d0.le hπ
  have u0 : 0<2/π*Δ := mul_pos (div_pos (by norm_num) pi_pos) d0
  have inv : 1/sin Δ≤(π/2)/Δ := by
    have r := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1) u0 J
    convert r using 1 <;> field_simp [pi_pos.ne',d0.ne'] <;> ring
  have osc : (scale c*(2*(M:ℝ))*E/sqrt (cos 1))*Δ= (8*π/sqrt (cos 1))*(E/Δ) := by
    have h : (M:ℝ)*Δ/c=1/Δ := by
      field_simp [cp.ne',d0.ne'] <;> nlinarith only [key]
    calc
      _ = (8*π/sqrt (cos 1))*E*((M:ℝ)*Δ/c) := by dsimp only [scale]; ring
      _ = _ := by rw [h]; ring
  have u := mul_le_mul_of_nonneg_left inv e0
  have v := div_le_div_of_nonneg_right u (sqrt_nonneg (cos 1))
  have C : E/(sin Δ*sqrt (cos 1))≤((π/2)/sqrt (cos 1))*(E/Δ) := by
    convert v using 1 <;> ring
  have C' : E/sin Δ≤(π/2)*(E/Δ) := by convert u using 1 <;> ring
  have W := short_angle_bound hc ht ht1 d0 d1 a b
  change _ ≤ (scale c*(2*(M:ℝ))*E/sqrt (cos 1))*Δ+E/(sin Δ*sqrt (cos 1))+E/sin Δ at W
  rw [osc] at W
  have res : ‖form M c a b (fun m n => (rawWindow t (argument c m n):ℂ))‖ ≤
      balancedConstant*(E/Δ) := by
    dsimp only [balancedConstant]
    linarith only [W,C,C']
  have m1 : 1≤(M:ℝ) := by exact_mod_cast (show 1≤M from (NeZero.pos c).trans_le hc)
  have l0 : 0≤244*(1+log M) := mul_nonneg (by norm_num) (by linarith only [log_nonneg m1])
  have rot : sqrt ((c:ℝ)*(244*M*(1+log M)))/Δ=(M:ℝ)*sqrt (244*(1+log M)) := by
    apply (div_eq_iff d0.ne').mpr
    apply (sq_eq_sq₀ (sqrt_nonneg _) (mul_nonneg (mul_nonneg mp.le (sqrt_nonneg _)) d0.le)).mp
    rw [sq_sqrt (show 0≤(c:ℝ)*(244*M*(1+log M)) by
      have h := log_nonneg m1; positivity),mul_pow,mul_pow,sq_sqrt l0,d2]
    field_simp [mp.ne'] <;> ring
  apply res.trans_eq
  dsimp only [shortBill,E,ampCost,oscillationCost]
  calc
    _ = balancedConstant*amplitudeConstant*exp (4*π)*
      (sqrt ((c:ℝ)*(244*M*(1+log M)))/Δ)*rowProduct M a b := by ring
    _ = _ := by rw [rot]; ring

def shortTerm (M z : ℕ) (t : ℝ) (a b : ℕ → ℂ) (d : ℕ) : ℂ :=
  if z*d<M then form M (z*d) a b (fun m n => (rawWindow t (argument (z*d) m n):ℂ))/((z*d:ℕ):ℂ)
  else 0

/-- Every integer d>0 with z*d<M occurs in Icc 1 M. The boundary z*d=M
belongs to the long progression. -/
theorem short_progression_bound {M z : ℕ} (hM : 0<M) (hz : 0<z)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) (a b : ℕ → ℂ) :
    (∑ d∈Icc 1 M, ‖shortTerm M z t a b d‖) ≤ shortBill M a b/z*(1+log M) := by
  have zp : 0<(z:ℝ) := by exact_mod_cast hz
  have B0 := short_bill_nonnegative M a b
  have H : (∑ d∈Icc 1 M, 1/(d:ℝ))≤1+log M := by
    calc
      _ = (harmonic M:ℝ) := by
        simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
      _ ≤ _ := harmonic_le_one_add_log M
  calc
    _ ≤ ∑ d∈Icc 1 M, (shortBill M a b/z)*(1/(d:ℝ)) := by
      apply sum_le_sum
      intro d hd
      have dp : 0<d := (mem_Icc.mp hd).1
      have dr : 0<(d:ℝ) := by exact_mod_cast dp
      have cp := Nat.mul_pos hz dp
      letI : NeZero (z*d) := ⟨cp.ne'⟩
      by_cases h : z*d<M
      · simp only [shortTerm,if_pos h,norm_div,Complex.norm_natCast,Nat.cast_mul]
        have p := div_le_div_of_nonneg_right (short_modulus_bound h.le ht ht1 a b)
          (mul_nonneg zp.le dr.le)
        convert p using 1 <;> ring
      · simp only [shortTerm,if_neg h,norm_zero]
        exact mul_nonneg (div_nonneg B0 zp.le) (div_nonneg zero_le_one dr.le)
    _ = (shortBill M a b/z)*(∑ d∈Icc 1 M, 1/(d:ℝ)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left H (div_nonneg B0 zp.le)

end ImbalancedChen.Part3.OriginalHolomorphicShortProgression20261113
end
