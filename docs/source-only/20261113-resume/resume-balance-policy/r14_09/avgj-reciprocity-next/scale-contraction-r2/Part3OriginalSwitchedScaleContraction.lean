import ImbalancedChen.Part3OriginalSwitchedPhysicalWindows

/-! Quantify all 24 return scales at the damped critical weight.
No spectral bound or level recurrence is a hypothesis of these identities. -/
namespace ImbalancedChen.Part3.OriginalSwitchedScaleContraction20261113
noncomputable section
open OriginalSwitchedPhysicalWindows20261113 (returnScale)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)

def kappa : ℝ := 16*Real.pi
def lambda : ℝ := Real.pi/16
def endpoint (j : ℕ) (Y Q : ℝ) (b : Fin 4) (l : Fin 6) :=
  (2:ℝ)^l.val*returnScale j Y ((2:ℝ)^b.val*Q)/2

private theorem ratio_range (b : Fin 4) (l : Fin 6) :
    1/16≤(2:ℝ)^l.val/(2*(2:ℝ)^b.val) ∧ (2:ℝ)^l.val/(2*(2:ℝ)^b.val)≤16 := by
  fin_cases b <;> fin_cases l <;> norm_num

theorem actual_scales (j : ℕ) {Q D : ℝ} (qp : 0<Q) (dp : 0<D) (b : Fin 4) (l : Fin 6) :
    let M := classicalMScale j
    let Z := Q^2/(D*M)
    let B := endpoint j Z Q b l
    lambda*(Q/D)≤B ∧ B≤kappa*(Q/D) := by
  let M := classicalMScale j
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  let r := (2:ℝ)^l.val/(2*(2:ℝ)^b.val)
  have e : endpoint j (Q^2/(D*M)) Q b l=(r*Real.pi)*(Q/D) := by
    unfold endpoint returnScale
    change (2:ℝ)^l.val*(Real.pi*M*(Q^2/(D*M))/((2:ℝ)^b.val*Q))/2=_
    dsimp only [r]
    field_simp [qp.ne',dp.ne',mp.ne',show (2:ℝ)^b.val≠0 by positivity] <;> ring
  dsimp only
  rw [e]
  have h := ratio_range b l
  have lo := mul_le_mul_of_nonneg_right h.1 Real.pi_pos.le
  have hi := mul_le_mul_of_nonneg_right h.2 Real.pi_pos.le
  refine ⟨mul_le_mul_of_nonneg_right ?_ (div_nonneg qp.le dp.le),
    mul_le_mul_of_nonneg_right hi (div_nonneg qp.le dp.le)⟩
  calc
    lambda = (1/16)*Real.pi := by dsimp [lambda];ring
    _ ≤ _ := lo

/-- The square-root transport from the parent critical weight to Z
and from the child critical weight to Z has exactly this product. -/
theorem transports {Q B D M : ℝ} (qp : 0<Q) (bp : 0<B) (dp : 0<D) (mp : 0<M) :
    Real.sqrt ((Q^2/M)/(Q^2/(D*M)))*Real.sqrt ((Q^2/(D*M))/(B^2/M))=Q/B := by
  let U := (Q^2/M)/(Q^2/(D*M))
  let V := (Q^2/(D*M))/(B^2/M)
  have up : 0≤U := by dsimp [U];positivity
  change Real.sqrt U*Real.sqrt V=Q/B
  rw [←Real.sqrt_mul up,show U*V=(Q/B)^2 by
    dsimp only [U,V];field_simp [qp.ne',bp.ne',dp.ne',mp.ne'] <;> ring,
    Real.sqrt_sq (div_nonneg qp.le bp.le)]

theorem recursive_band {M Q B D Y₀ T : ℝ} (mp : 0<M) (y1 : 1≤Y₀) (dp : 0<D)
    (ds : kappa^2≤D) (ds' : 2*kappa≤D)
    (t₁ : 1≤T) (t₂ : D/lambda≤T) (t₃ : Real.sqrt (D*Y₀)≤T)
    (entry : T*max 1 M<Q) (bl : lambda*(Q/D)≤B) (bu : B≤kappa*(Q/D)) :
    let Z := Q^2/(D*M)
    Y₀≤Z ∧ max 1 M≤B ∧ B≤Q/2 ∧ B^2/M≤Z := by
  let H : ℝ := max 1 M
  have hp : 1≤H := le_max_left _ _
  have hm : M≤H := le_max_right _ _
  have tp : 0<T := zero_lt_one.trans_le t₁
  have qp : 0<Q := (mul_pos tp (zero_lt_one.trans_le hp)).trans entry
  have lp : 0<lambda := div_pos Real.pi_pos (by norm_num)
  have kp : 0<kappa := mul_pos (by norm_num) Real.pi_pos
  have bd : (D/lambda)*H≤Q := (mul_le_mul_of_nonneg_right t₂ (zero_le_one.trans hp)).trans entry.le
  have H_bd : H≤lambda*(Q/D) := by
    rw [show lambda*(Q/D)=Q/(D/lambda) by field_simp [dp.ne',lp.ne'] <;> ring,le_div_iff₀ (div_pos dp lp)]
    simpa only [mul_comm H (D/lambda)] using bd
  have hQ : T*H≤Q := entry.le
  have h2 : (T*H)^2≤Q^2 := pow_le_pow_left₀ (mul_nonneg tp.le (zero_le_one.trans hp)) hQ 2
  have d0 : 0≤D*Y₀ := mul_nonneg dp.le (zero_le_one.trans y1)
  have tSq : D*Y₀≤T^2 := by
    simpa only [Real.sq_sqrt d0] using pow_le_pow_left₀ (Real.sqrt_nonneg _) t₃ 2
  have hSq : M≤H^2 := hm.trans (by nlinarith only [mul_nonneg (by linarith only [hp] : 0≤H-1)
    (zero_le_one.trans hp)])
  have ybound := mul_le_mul tSq hSq mp.le (sq_nonneg T)
  have bp : 0≤B := (zero_le_one.trans hp).trans (H_bd.trans bl)
  have bs := pow_le_pow_left₀ bp bu 2
  have yb : Y₀≤Q^2/(D*M) := (le_div_iff₀ (mul_pos dp mp)).mpr (by nlinarith only [ybound,h2])
  have bq : B≤Q/2 := bu.trans (by
    calc
      kappa*(Q/D) ≤ (D/2)*(Q/D) := mul_le_mul_of_nonneg_right (by linarith only [ds']) (div_nonneg qp.le dp.le)
      _ = Q/2 := by field_simp [dp.ne'] <;> ring)
  have scale : B^2≤Q^2/D := by
    calc
      _ ≤ (kappa*(Q/D))^2 := bs
      _ = kappa^2*(Q/D)^2 := mul_pow _ _ _
      _ ≤ D*(Q/D)^2 := mul_le_mul_of_nonneg_right ds (sq_nonneg _)
      _ = Q^2/D := by field_simp [dp.ne'] <;> ring
  refine ⟨yb,H_bd.trans bl,bq,?_⟩
  exact (div_le_div_of_nonneg_right scale mp.le).trans_eq (by rw [div_div])

/-- The fixed contraction factor is chosen after the aggregate
constant A and ε, before the physical scales. -/
theorem choose_damping (A : ℝ) (ap : 1≤A) {ε : ℝ} (ep : 0<ε) :
    ∃ D : ℝ,0<D ∧ kappa^2≤D ∧ 2*kappa≤D ∧ 2*A*(kappa/D)^ε≤1/2 := by
  let u := (4*A)^(1/ε)
  let D := max (kappa^2) (max (2*kappa) (kappa*u))
  have kp : 0<kappa := mul_pos (by norm_num) Real.pi_pos
  have ad : 0<4*A := by linarith
  have up : 0<u := Real.rpow_pos_of_pos ad _
  have lo : kappa*u≤D := (le_max_right _ _).trans (le_max_right _ _)
  have dp : 0<D := (mul_pos kp up).trans_le lo
  refine ⟨D,dp,le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),?_⟩
  have f : kappa/D≤1/u := (div_le_div_iff₀ dp up).mpr (by simpa only [one_mul] using lo)
  have p := Real.rpow_le_rpow (div_nonneg kp.le dp.le) f ep.le
  have z : (1/u)^ε=1/(4*A) := by
    rw [Real.div_rpow zero_le_one up.le,Real.one_rpow]
    dsimp only [u]
    rw [←Real.rpow_mul ad.le,show (1/ε)*ε=1 by field_simp [ep.ne'],Real.rpow_one]
  apply (mul_le_mul_of_nonneg_left (p.trans_eq z) (by positivity : 0≤2*A)).trans_eq
  field_simp [ad.ne',show A≠0 by linarith] <;> ring

theorem normalized_contribution {A Q B M D ε : ℝ} (ap : 0≤A) (qp : 0<Q) (bp : 0<B)
    (mp : 0≤M) (dp : 0<D) (ep : 0≤ε) (small : M≤B) (shrink : B≤kappa*(Q/D))
    (budget : 2*A*(kappa/D)^ε≤1/2) :
    A*(B/Q)^ε*(Q*(B+M)/(B*(Q+M)))≤1/2 := by
  have e : B/Q≤kappa/D := (div_le_iff₀ qp).mpr (shrink.trans_eq (by ring))
  have scale := Real.rpow_le_rpow (div_nonneg bp.le qp.le) e ep
  have norm : Q*(B+M)/(B*(Q+M))≤2 := by
    apply (div_le_iff₀ (mul_pos bp (add_pos_of_pos_of_nonneg qp mp))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left small qp.le,mul_nonneg bp.le mp]
  have bound := mul_le_mul (mul_le_mul_of_nonneg_left scale ap) norm
    (div_nonneg (mul_nonneg qp.le (add_nonneg bp.le mp)) (mul_nonneg bp.le (add_nonneg qp.le mp)))
    (mul_nonneg ap (Real.rpow_nonneg (by dsimp [kappa];positivity) _))
  exact bound.trans ((show A*(kappa/D)^ε*2=2*A*(kappa/D)^ε by ring).le.trans budget)

end
end ImbalancedChen.Part3.OriginalSwitchedScaleContraction20261113
