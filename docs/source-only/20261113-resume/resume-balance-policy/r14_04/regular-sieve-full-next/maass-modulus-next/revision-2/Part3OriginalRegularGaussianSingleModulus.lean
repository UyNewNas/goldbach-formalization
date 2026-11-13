import ImbalancedChen.Part3OriginalRegularGaussianForms

/-! The true same-cusp Gaussian numerator at every short modulus. The
cosine integral is used up to M/K², the sine integral above it. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularGaussianSingleModulus20261113
open Real MeasureTheory
open OriginalHolomorphicPhysicalCosine20261113 (cosineForm scale)
open OriginalHolomorphicShortOscillation20261113
open OriginalAllParameterKloosterman20261113 (allCost)
open OriginalRegularPreKuznetsovAverage20261113 (G)
open OriginalRegularGaussianForms20261113
open OriginalRegularGaussianMoment20261113

def price (M : ℕ) : ℝ := exp (4*π)*sqrt (244*(1+log M))
def shortConstant := normalization*bill*(100*π)

theorem price_exp {M : ℕ} (hM : 0<M) : exp (4*π)≤price M := by
  have l := log_nonneg (show (1:ℝ)≤M by exact_mod_cast hM)
  have e := sqrt_le_sqrt (show (1:ℝ)≤244*(1+log M) by linarith)
  rw [sqrt_one] at e
  exact (mul_one _).symm.le.trans (mul_le_mul_of_nonneg_left e (exp_pos _).le)

theorem uniform_cost {M c : ℕ} {D θ q : ℝ} (hM : (M:ℝ)≤D) (hc : (c:ℝ)≤D)
    (hθ : 1≤θ) (hq : q≤θ) : allCost M c q≤3*D*θ := by
  have d0 := (Nat.cast_nonneg M).trans hM
  have θ0 := zero_le_one.trans hθ
  have A := mul_le_mul hc hM (Nat.cast_nonneg M) d0
  have B := mul_le_mul_of_nonneg_left A θ0
  have C := mul_le_mul_of_nonneg_right hq (mul_nonneg (Nat.cast_nonneg c) (Nat.cast_nonneg M))
  have D2 := mul_le_mul_of_nonneg_left hθ (mul_nonneg θ0 (sq_nonneg D))
  have DR : sqrt (q*c*M)≤D*θ := sqrt_le_iff.mpr
    ⟨mul_nonneg d0 θ0,by nlinarith only [B,C,D2]⟩
  have D1 := mul_le_mul_of_nonneg_left hθ d0
  unfold allCost
  nlinarith only [hM,hc,DR,D1]

private theorem weak {M c : ℕ} [NeZero c] (hM : 0<M) (hc : c≤M) (ξ : ℝ) (a b : ℕ→ℂ) :
    ‖cosineForm M c (cosh ξ) a b‖≤12*price M*M*cosh ξ*rowProduct M a b ∧
    ‖sineForm M c (cosh ξ) a b‖≤12*price M*M*cosh ξ*rowProduct M a b := by
  have lim := uniform_cost (M:=M) (c:=c) (le_refl (M:ℝ))
    (by exact_mod_cast hc) (one_le_cosh ξ) (le_refl (cosh ξ))
  have p := mul_le_mul (price_exp hM) lim
    (show 0≤allCost M c (cosh ξ) by dsimp only [allCost]; positivity)
    ((exp_pos _).le.trans (price_exp hM))
  have w := mul_le_mul_of_nonneg_right p (row_product_nonnegative M a b)
  have h := all_forms hM (cosh_pos ξ).le a b
  constructor <;> nlinarith only [w,h.1,h.2]

private theorem central {M c : ℕ} [NeZero c] (hc : c≤M) {ξ : ℝ} (near : |ξ|≤1) (a b : ℕ→ℂ) :
    ‖cosineForm M c (cosh ξ) a b‖≤price M*sqrt ((c:ℝ)*M)*rowProduct M a b ∧
    ‖sineForm M c (cosh ξ) a b‖≤price M*sqrt ((c:ℝ)*M)*rowProduct M a b := by
  have m1 : 1≤(M:ℝ) := by exact_mod_cast (NeZero.pos c).trans_le hc
  have l := log_nonneg m1
  have l0 : 0≤244*(1+log M) := by linarith only [l]
  have op : oscillationCost M c=price M*sqrt ((c:ℝ)*M) := by
    dsimp only [oscillationCost,price]
    rw [show (c:ℝ)*(244*M*(1+log M))=(244*(1+log M))*(c*M) by ring,sqrt_mul l0]
    ring
  have d := sqrt_le_sqrt (one_le_cosh ξ)
  rw [sqrt_one] at d
  have w := short_oscillation hc (cosh_pos ξ) (cosh_near near) a b
  have bnd := div_le_self
    (mul_nonneg (oscillation_cost_nonnegative M c) (row_product_nonnegative M a b)) d
  rw [op] at w bnd
  exact ⟨w.1.trans bnd,w.2.trans bnd⟩

theorem norm_cosKernel (M c : ℕ) (K : ℝ) (a b : ℕ→ℂ) (ξ : ℝ) :
    ‖cosKernel M c K a b ξ‖=cosineWeight K ξ*‖cosineForm M c (cosh ξ) a b‖ := by
  simp only [cosKernel,cosineWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_div,abs_mul,abs_of_pos (Real.cosh_pos _),abs_of_pos (show 0<G K ξ from exp_pos _)]

theorem norm_sinKernel (M c : ℕ) (K : ℝ) (a b : ℕ→ℂ) (ξ : ℝ) :
    ‖sinKernel M c K a b ξ‖=scale c*sineWeight K ξ*‖sineForm M c (cosh ξ) (rootRow a) (rootRow b)‖ := by
  have sc : 0≤scale c := by unfold scale; positivity
  simp only [sinKernel,sineWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg sc,abs_of_pos (show 0<G K ξ from exp_pos _)]
  ring

theorem sine_nonnegative (K ξ : ℝ) : 0≤sineWeight K ξ := mul_nonneg (abs_nonneg _) (exp_pos _).le
theorem cosine_nonnegative (K ξ : ℝ) : 0≤cosineWeight K ξ :=
  div_nonneg (mul_nonneg (abs_nonneg _) (exp_pos _).le) (cosh_pos _).le

private theorem cosine_short {M c : ℕ} [NeZero c] (hM : 0<M) (hc : c≤M)
    {K : ℝ} (hK : 2≤K) (small : K^2*c≤M) (a b : ℕ→ℂ) (ξ : ℝ) :
    K^2*‖cosKernel M c K a b ξ‖≤
      (100*π*K*M*price M*rowProduct M a b)*major (K*ξ) := by
  let E := rowProduct M a b
  let J := major (K*ξ)
  let D := cosineWeight K ξ
  have e0 : 0≤E := row_product_nonnegative M a b
  have p0 := (exp_pos _).le.trans (price_exp hM)
  have m0 : 0≤(M:ℝ) := Nat.cast_nonneg M
  have k0 : 0≤K := by linarith only [hK]
  have j0 : 0≤J := major_nonnegative _
  have d0 : 0≤D := cosine_nonnegative K ξ
  have hπ := pi_gt_three
  rw [norm_cosKernel]
  by_cases near : |ξ|≤1
  · have s0 := sqrt_nonneg ((c:ℝ)*M)
    have scaleBound : K*sqrt ((c:ℝ)*M)≤M := by
      apply (sq_le_sq₀ (mul_nonneg k0 s0) m0).mp
      rw [mul_pow,sq_sqrt (mul_nonneg (Nat.cast_nonneg _) m0)]
      have B := mul_le_mul_of_nonneg_right small m0
      nlinarith only [B]
    have w := mul_le_mul (cosine_major hK ξ) (central hc near a b).1 (norm_nonneg _ ) j0
    have v := mul_le_mul_of_nonneg_left w (sq_nonneg K)
    have u := mul_le_mul_of_nonneg_left scaleBound
      (show 0≤K*price M*E*J by positivity)
    have P := mul_le_mul_of_nonneg_right (show (1:ℝ)≤100*π by linarith only [hπ])
      (show 0≤K*M*price M*E*J by positivity)
    change _≤100*π*K*M*price M*E*J
    dsimp only [E,J,D] at *
    nlinarith only [v,u,P]
  · have w := mul_le_mul_of_nonneg_left (weak hM hc ξ a b).1 (mul_nonneg (sq_nonneg K) d0)
    have v := mul_le_mul_of_nonneg_right (cosine_far_major hK (le_of_not_ge near))
      (show 0≤12*price M*M*E by positivity)
    have u := mul_le_mul_of_nonneg_right (show (12:ℝ)≤100*π*K by
      have v := mul_le_mul_of_nonneg_left hK pi_pos.le
      linarith only [hπ,v]) (show 0≤(M:ℝ)*price M*E*J by positivity)
    dsimp only [E,J,D] at *
    nlinarith only [w,v,u]

private theorem sine_short {M c : ℕ} [NeZero c] (hM : 0<M) (hc : c≤M)
    {K : ℝ} (hK : 2≤K) (large : (M:ℝ)≤K^2*c) (a b : ℕ→ℂ) (ξ : ℝ) :
    K^2*‖sinKernel M c K a b ξ‖≤
      (100*π*K*M*price M*rowProduct M a b)*major (K*ξ) := by
  let E := rowProduct M a b
  let J := major (K*ξ)
  let S := sineWeight K ξ
  have e0 : 0≤E := row_product_nonnegative M a b
  have p0 := (exp_pos _).le.trans (price_exp hM)
  have j0 : 0≤J := major_nonnegative _
  have s0 : 0≤S := sine_nonnegative K ξ
  have m0 : 0≤(M:ℝ) := Nat.cast_nonneg _
  have cp : 0<(c:ℝ) := by exact_mod_cast NeZero.pos c
  have k0 : 0<K := by linarith only [hK]
  have sc : 0≤scale c := by unfold scale; positivity
  have e := root_row_product M a b
  have fre : sqrt ((c:ℝ)*M)≤K*c := sqrt_le_iff.mpr ⟨mul_nonneg k0.le cp.le,by
    have B := mul_le_mul_of_nonneg_left large cp.le
    nlinarith only [B]⟩
  have nearS : K^2*S≤J := by
    have d := pow_le_pow_left₀ (by norm_num : 0≤(1:ℝ)) (one_le_cosh ξ) 2
    rw [one_pow] at d
    have w := mul_le_mul_of_nonneg_left d (mul_nonneg (sq_nonneg K) s0)
    calc
      K^2*S ≤ K^2*S*cosh ξ^2 := by simpa only [mul_one] using w
      _ ≤ _ := sine_major hK ξ
  rw [norm_sinKernel]
  have pe := mul_le_mul_of_nonneg_left e p0
  by_cases near : |ξ|≤1
  · have h := (central hc near (rootRow a) (rootRow b)).2
    have v := mul_le_mul fre pe (mul_nonneg p0 (row_product_nonnegative _ _ _)) (mul_nonneg k0.le cp.le)
    have F : ‖sineForm M c (cosh ξ) (rootRow a) (rootRow b)‖≤(K*c)*(price M*(2*M*E)) := by
      dsimp only [E]
      nlinarith only [h,v]
    have w := mul_le_mul nearS F (norm_nonneg _) j0
    have w' := mul_le_mul_of_nonneg_left w sc
    have normScale : scale c*(J*((K*c)*(price M*(2*M*E))))=8*π*K*M*price M*E*J := by
      dsimp only [scale];field_simp [cp.ne'] <;> ring
    have big := mul_le_mul_of_nonneg_right (show 8*π≤100*π by linarith only [pi_pos])
      (show 0≤K*M*price M*E*J by positivity)
    rw [normScale] at w'
    dsimp only [E,J,S] at *
    nlinarith only [w',big]
  · have h := (weak hM hc ξ (rootRow a) (rootRow b)).2
    have v := mul_le_mul_of_nonneg_left e (show 0≤12*price M*M*cosh ξ by positivity)
    have v' := mul_le_mul_of_nonneg_left (h.trans v) (mul_nonneg (sq_nonneg K) s0)
    have f := sine_far_major hK (le_of_not_ge near)
    have L := mul_le_mul_of_nonneg_left large (show 0≤K^2*S*cosh ξ by positivity)
    have L' : K^2*S*cosh ξ*M≤J*c := by
      have w := mul_le_mul_of_nonneg_right f cp.le
      dsimp only [J,S] at *
      nlinarith only [L,w]
    have P := mul_le_mul_of_nonneg_left L' (show 0≤24*price M*M*E by positivity)
    have T : K^2*S*‖sineForm M c (cosh ξ) (rootRow a) (rootRow b)‖≤
        24*price M*M*E*(J*c) := by
      dsimp only [E,J,S] at *
      nlinarith only [v',P]
    have W := mul_le_mul_of_nonneg_left T sc
    have normScale : scale c*(24*price M*M*E*(J*c))=96*π*M*price M*E*J := by
      dsimp only [scale];field_simp [cp.ne'] <;> ring
    rw [normScale] at W
    have B := mul_le_mul_of_nonneg_right (show 96*π≤100*π*K by
      have v := mul_le_mul_of_nonneg_left hK pi_pos.le
      linarith only [pi_pos,v]) (show 0≤(M:ℝ)*price M*E*J by positivity)
    dsimp only [E,J,S] at *
    nlinarith only [W,B]

theorem short_modulus {M c : ℕ} [NeZero c] (hM : 0<M) (hc : c≤M) {K : ℝ} (hK : 2≤K) (a b : ℕ→ℂ) :
    ‖numerator M c K a b‖≤shortConstant*K*M*price M*rowProduct M a b := by
  have kp : 0<K := by linarith only [hK]
  obtain ⟨si,ci,S,C⟩ := numerator_forms hM kp a b
  have cost (F : ℝ→ℂ) (hi : Integrable F)
      (E : numerator M c K a b=((normalization*K^3:ℝ):ℂ)*∫ ξ : ℝ,F ξ)
      (B : ∀ ξ,K^2*‖F ξ‖≤(100*π*K*M*price M*rowProduct M a b)*major (K*ξ)) :
      ‖numerator M c K a b‖≤shortConstant*K*M*price M*rowProduct M a b := by
    rw [E,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg normalization_pos.le (pow_nonneg kp.le 3))]
    have lim := mul_le_mul_of_nonneg_left (integral_price hK F hi B) normalization_pos.le
    dsimp only [shortConstant]
    nlinarith only [lim]
  by_cases small : K^2*c≤M
  · exact cost _ ci C (cosine_short hM hc hK small a b)
  · exact cost _ si S (sine_short hM hc hK (le_of_not_ge small) a b)

end ImbalancedChen.Part3.OriginalRegularGaussianSingleModulus20261113
end

