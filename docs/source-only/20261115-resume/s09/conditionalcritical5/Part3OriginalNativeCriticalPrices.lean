import ImbalancedChen.Part3OriginalSwitchedScaleContraction

/-! The scalar size of the new additive charge on the critical induction
bands. All constants are fixed before the level, interval and phase. -/
namespace ImbalancedChen.Part3.OriginalNativeCriticalPrices20261113
noncomputable section
open Real

def height (M : ℝ) := max 1 M
def benchmark (M Q : ℝ) := max (height M) (Q^2/M)
def normPrice (M Q ε : ℝ) := (max 1 Q*height M)^ε*(Q+M)*M

private theorem two (M : ℝ) (hm : 1/2≤M) :
    1≤height M ∧ M≤height M ∧ height M≤2*M :=
  ⟨le_max_left _ _,le_max_right _ _,max_le (by linarith) (by linarith)⟩

theorem base {M Q T ε : ℝ} (hm : 1/2≤M) (qp : 0<Q) (ep : 0<ε)
    (low : Q≤T*height M) :
    let c := 1+2*T^2
    let W := benchmark M Q
    ((1+M)*(1+W))^(ε/2)*(Q+M+W)*M≤
      (2*(1+c))^(ε/2)*(1+2*c)*normPrice M Q ε := by
  let H := height M
  let W := benchmark M Q
  let c := 1+2*T^2
  let N := max 1 Q*H
  have h := two M hm
  have mp : 0<M := by linarith only [hm]
  have hp : 0<H := zero_lt_one.trans_le h.1
  have cp : 0<c := by dsimp only [c];positivity
  have c1 : 1≤c := by dsimp only [c];nlinarith only [sq_nonneg T]
  have hn : H≤N := by simpa only [N,one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 Q) hp.le
  have np : 0<N := hp.trans_le hn
  have q2 := pow_le_pow_left₀ qp.le low 2
  have sh : H^2≤2*H*M := by nlinarith only [mul_le_mul_of_nonneg_left h.2.2 hp.le]
  have hi : Q^2/M≤c*H := (div_le_iff₀ mp).mpr (by dsimp only [c];nlinarith only
    [q2,mul_le_mul_of_nonneg_left sh (sq_nonneg T),mul_nonneg hp.le mp.le])
  have hch : H≤c*H := by simpa only [one_mul] using mul_le_mul_of_nonneg_right c1 hp.le
  have w : W≤c*H := max_le hch hi
  have wm := w.trans (mul_le_mul_of_nonneg_left h.2.2 cp.le)
  have w0 : 0<W := hp.trans_le (le_max_left _ _)
  have cbase : 0<2*(1+c) := by positivity
  have u : (1+M)*(1+W)≤(2*(1+c))*(H*H) := by
    have left : 1+M≤2*H := by linarith only [h.1,h.2.1]
    have right : 1+W≤(1+c)*H := by nlinarith only [h.1,w]
    exact (mul_le_mul left right (by linarith only [w0]) (by positivity)).trans_eq (by ring)
  have grow := Real.rpow_le_rpow (by positivity : 0≤(1+M)*(1+W)) u (half_pos ep).le
  have pow : (H*H)^(ε/2)=H^ε := by
    rw [Real.mul_rpow hp.le hp.le,←Real.rpow_add hp,show ε/2+ε/2=ε by ring]
  rw [Real.mul_rpow (by positivity : 0≤2*(1+c)) (mul_nonneg hp.le hp.le),pow] at grow
  have lift := grow.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.le hn ep.le) (Real.rpow_nonneg cbase.le _))
  have v : Q+M+W≤(1+2*c)*(Q+M) := by nlinarith only [wm,mul_nonneg cp.le qp.le]
  have b := mul_le_mul lift v (by linarith only [qp,mp,w0])
    (mul_nonneg (Real.rpow_nonneg cbase.le _) (Real.rpow_nonneg np.le _))
  exact (mul_le_mul_of_nonneg_right b mp.le).trans_eq (by dsimp only [normPrice,N,H,c];ring)

theorem recursive {M Q D ε : ℝ} (hm : 1/2≤M) (qp : 1≤Q) (dq : 1≤D) (ep : 0<ε)
    (z1 : 1≤Q^2/(D*M)) :
    let Z := Q^2/(D*M)
    ((1+M)*(1+Z))^(ε/2)*(Q+M+M*Z/Q)*M≤
      2*6^(ε/2)*normPrice M Q ε := by
  let Z := Q^2/(D*M)
  let H := height M
  let N := max 1 Q*H
  have mp : 0<M := by linarith only [hm]
  have qpos := zero_lt_one.trans_le qp
  have dp := zero_lt_one.trans_le dq
  have zp : 0<Z := zero_lt_one.trans_le z1
  have qsq : M*Z=Q^2/D := by dsimp only [Z];field_simp [dp.ne',mp.ne'] <;> ring
  have p : M*Z≤Q^2 := qsq.le.trans ((div_le_iff₀ dp).mpr (by nlinarith only [mul_le_mul_of_nonneg_left dq (sq_nonneg Q)]))
  have a : (1+M)*(1+Z)≤6*(M*Z) := (mul_le_mul (by linarith only [hm] : 1+M≤3*M)
    (by linarith only [z1] : 1+Z≤2*Z) (by linarith only [zp]) (by positivity)).trans_eq (by ring)
  have grow := Real.rpow_le_rpow (by positivity : 0≤(1+M)*(1+Z)) (a.trans (mul_le_mul_of_nonneg_left p (by norm_num)))
    (half_pos ep).le
  have eq : (6*Q^2)^(ε/2)=6^(ε/2)*Q^ε := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤6) (sq_nonneg Q),sq,Real.mul_rpow qpos.le qpos.le,
      ←Real.rpow_add qpos,show ε/2+ε/2=ε by ring]
  rw [eq] at grow
  have qn : Q≤N := by dsimp only [N];rw [max_eq_right qp];simpa only [mul_one] using mul_le_mul_of_nonneg_left (two M hm).1 qpos.le
  have np : 0<N := qpos.trans_le qn
  have lift := grow.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow qpos.le qn ep.le) (by positivity))
  have zratio : M*Z/Q≤Q := (div_le_iff₀ qpos).mpr (p.trans_eq (by ring))
  have size : Q+M+M*Z/Q≤2*(Q+M) := by linarith only [zratio,mp]
  have b := mul_le_mul lift size (by positivity : 0≤Q+M+M*Z/Q) (by positivity : 0≤(6:ℝ)^(ε/2)*N^ε)
  exact (mul_le_mul_of_nonneg_right b mp.le).trans_eq (by dsimp only [normPrice,N];ring)

end
end ImbalancedChen.Part3.OriginalNativeCriticalPrices20261113

