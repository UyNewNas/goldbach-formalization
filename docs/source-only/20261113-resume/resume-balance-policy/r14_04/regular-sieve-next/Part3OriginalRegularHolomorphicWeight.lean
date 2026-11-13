import ImbalancedChen.Part3OriginalRegularHolomorphicPacket
import ImbalancedChen.Part3OriginalRegularPacketTest
import ImbalancedChen.Part3OriginalHolomorphicBasisMass
import Batteries.Tactic.OpenPrivate

/-! A positive proportion of the archimedean Petersson mass is above a
height of order (k−1)/L, even at k=2.  Comparison with the already
evaluated density at 2n proves this without a Gamma asymptotic. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularHolomorphicWeight20261113
open Set Filter MeasureTheory Matrix Complex UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators ENNReal ModularForm
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalPeterssonPretrace20261112 OriginalPeterssonNormalization20261112
open OriginalPeterssonHighStrip20261112 OriginalRegularHolomorphicPacket20261113
open ActualContinuousPoincarePairing20261110 OriginalRegularPeterssonStrip20261113
open OriginalRegularPacketTest20261113 (Dyadic)
open private mass_pos from ImbalancedChen.Part3OriginalHolomorphicBasisMass

def order (j : ℕ) : ℕ := 2*j+1
def hScale (j : ℕ) (L : ℝ) : ℝ := (order j:ℝ)*Real.log (3/2)/(8*Real.pi*L)
private def d (j n : ℕ) (y : ℝ) : ℝ := y^(2*j)*Real.exp (-(4*Real.pi*n*y))
private theorem total (j : ℕ) {n : ℕ} (hn : 0<n) :
    (∫ y in Ioi (0:ℝ),d j n y)=mass (j+1) n := by
  simpa only [d,show 2*(j+1)-2=2*j by omega] using mass_integral (r:=j+1) (by omega) hn
private theorem di (j : ℕ) {n : ℕ} (hn : 0<n) : IntegrableOn (d j n) (Ioi (0:ℝ)) := by
  by_contra H
  exact (mass_pos (r:=j+1) (by omega) hn).ne' ((total j hn).symm.trans (integral_undef H))

private theorem half_rate (j n : ℕ) : (2:ℝ)^order j *mass (j+1) (2*n)=mass (j+1) n := by
  unfold mass
  rw [show 2*(j+1)-1=order j by unfold order;omega]
  push_cast
  rw [←mul_assoc,←mul_pow]
  have eq : (2:ℝ)*(1/(4*Real.pi*(2*(n:ℝ))))=1/(4*Real.pi*n) := by
    by_cases hn : n=0
    · simp [hn]
    · field_simp [Real.pi_ne_zero,show (n:ℝ)≠0 by exact_mod_cast hn] <;>ring
  rw [eq]

private theorem small (j : ℕ) {n : ℕ} (hn : 0<n) {Y : ℝ} (hY : 0<Y)
    (bd : 4*Real.pi*n*Y ≤ (order j:ℝ)*Real.log (3/2)) :
    (∫ y in Ioc 0 Y,d j n y) ≤ (3/4)*mass (j+1) n := by
  let s := order j
  let c := (3/2:ℝ)^s
  have cn : 0≤c := by dsimp [c]; positivity
  have H (y : ℝ) (hy : y∈Ioc 0 Y) : d j n y ≤ c*d j (2*n) y := by
    let b : ℝ := 4*Real.pi*n
    have ex : Real.exp (b*y)≤c := by
      have u := Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hy.2 (by dsimp [b]; positivity)).trans bd)
      rwa [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<3/2)] at u
    have E : Real.exp (-(b*y))=Real.exp (b*y)*Real.exp (-(2*b*y)) := by
      rw [←Real.exp_add];congr 1;ring
    simp only [d,Nat.cast_mul,Nat.cast_ofNat]
    change y^(2*j)*Real.exp (-(b*y))≤_
    rw [E,show (4:ℝ)*Real.pi*(2*(n:ℝ))*y=2*b*y by dsimp [b];ring]
    nlinarith only [mul_le_mul_of_nonneg_right ex
      (mul_nonneg (pow_nonneg hy.1.le _) (Real.exp_pos (-(2*b*y))).le)]
  have dn := di j hn
  have d2 := di j (n:=2*n) (by omega)
  have sub : Ioc (0:ℝ) Y⊆Ioi 0 := fun _ h => h.1
  have rate : c=(3/4:ℝ)^s*(2:ℝ)^s := by rw [←mul_pow];congr 1 <;>norm_num
  have smallpow : (3/4:ℝ)^s ≤ 3/4 := by
    calc
      _ = (3/4:ℝ)^(2*j)*(3/4) := by dsimp [s,order];rw [pow_succ]
      _ ≤ 1*(3/4) := mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
      _ = _ := one_mul _
  calc
    _ ≤ ∫ y in Ioc 0 Y,c*d j (2*n) y := integral_mono_ae (dn.mono_set sub) ((d2.mono_set sub).const_mul c)
      ((ae_restrict_mem (μ:=volume) measurableSet_Ioc).mono (fun y hy => H y hy))
    _ ≤ ∫ y in Ioi (0:ℝ),c*d j (2*n) y := setIntegral_mono_set (d2.const_mul c)
      ((ae_restrict_mem (μ:=volume) measurableSet_Ioi).mono (fun y hy =>
        mul_nonneg cn (mul_nonneg (pow_nonneg hy.le _) (Real.exp_pos _).le))) (ae_of_all _ (fun _ h => sub h))
    _ = c*mass (j+1) (2*n) := by rw [integral_const_mul,total j (by omega)]
    _ = (3/4:ℝ)^s*mass (j+1) n := by rw [rate,mul_assoc,half_rate]
    _ ≤ _ := mul_le_mul_of_nonneg_right smallpow (mass_pos (r:=j+1) (by omega) hn).le

theorem tail (j : ℕ) {n : ℕ} (hn : 0<n) {Y : ℝ} (hY : 0<Y)
    (bd : 4*Real.pi*n*Y ≤ (order j:ℝ)*Real.log (3/2)) {A : ℝ} (hA : 0≤A) :
    ENNReal.ofReal (mass (j+1) n*A/4) ≤
      ∫⁻ y in Ici Y,ENNReal.ofReal (y^(2*(j+1)-2)*Real.exp (-(4*Real.pi*n*y))*A) := by
  have i := di j hn
  have sub1 : Ioc (0:ℝ) Y⊆Ioi 0 := fun _ h => h.1
  have sub2 : Ioi Y⊆Ioi 0 := fun _ h => hY.trans h
  have hi := i.mono_set sub2
  have split := setIntegral_union (Set.disjoint_left.mpr (fun y (hy : y∈Ioc (0:ℝ) Y) (ht : y∈Ioi Y) => ht.not_ge hy.2))
    measurableSet_Ioi (i.mono_set sub1) hi
  rw [Ioc_union_Ioi_eq_Ioi hY.le,total j hn] at split
  have lower : mass (j+1) n/4 ≤ ∫ y in Ioi Y,d j n y := by linarith only [split,small j hn hY bd]
  calc
    _ ≤ ENNReal.ofReal ((∫ y in Ioi Y,d j n y)*A) := ENNReal.ofReal_le_ofReal (by
      simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right lower hA)
    _ = ∫⁻ y in Ioi Y,ENNReal.ofReal (d j n y*A) := by
      rw [←integral_mul_const,ofReal_integral_eq_lintegral_ofReal (hi.mul_const A) (by
        filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with y hy
        exact mul_nonneg (mul_nonneg (pow_nonneg (hY.trans hy).le _) (Real.exp_pos _).le) hA)]
    _ ≤ _ := by
      simp only [show 2*(j+1)-2=2*j by omega,d]
      exact lintegral_mono_set Ioi_subset_Ici_self

def fixedBill (N j : ℕ) (L : ℝ) : ℝ :=
  ((order j:ℝ)*2+32*Real.pi*(L/(N:ℝ))/Real.log (3/2))/Real.pi

/-- Simultaneous restriction, in the original positive coefficient and its
exact Γ(k) normalization, on the entire Petersson space of that even k. -/
theorem restriction (N j : ℕ) [NeZero N] (one : Bool) {L : ℝ} (hL : 0<L)
    (S : Finset ℕ) (band : Dyadic L S) (f : Forms N (j+1)) :
    Real.Gamma (2*(j:ℝ)+2)*(∑ n∈S,‖frameR N (NeZero.pos N) (j+1) f (originalFrame one) n‖^2)
      ≤ fixedBill N j L*‖f‖^2 := by
  let r := j+1
  let s : ℝ := order j
  let Y := hScale j L
  let g := originalFrame one
  let C := 2+4/((N:ℝ)*Y)
  have sp : 0<s := by dsimp [s,order]; positivity
  have lp : 0<Real.log (3/2) := Real.log_pos (by norm_num)
  have yp : 0<Y := by dsimp [Y,hScale]; positivity
  have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have cp : 0≤C := by dsimp [C]; positivity
  let R := fun n => ‖frameR N (NeZero.pos N) (j+1) f g n‖^2
  let A := fun n => ‖raw N (NeZero.pos N) (j+1) g n f‖^2
  have eq (n : ℕ) (hn : 0<n) : mass (j+1) n*A n/4=Real.pi*Real.Gamma s*R n := by
    have id := normalization_factor (j:=j) hn hn
    have nr : Real.sqrt (n:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
    have cs : 0≤coefficientScale j n := by unfold coefficientScale; positivity
    rw [div_self nr,one_pow,one_mul,←sq] at id
    dsimp only [A,R]
    rw [raw_eq_scaled_R N _ j f g hn,norm_mul,Complex.norm_real,Real.norm_of_nonneg cs,mul_pow,←mul_assoc,id]
    have es : s=2*(j:ℝ)+1 := by dsimp [s,order]; push_cast; ring
    rw [es]; ring
  have pt (n : ℕ) (hn : n∈S) : ENNReal.ofReal (Real.pi*Real.Gamma s*R n)≤
      ∫⁻ y in Ici Y,ENNReal.ofReal (y^(2*r-2)*Real.exp (-(4*Real.pi*n*y))*A n) := by
    have n0 : 0<n := Nat.cast_pos.mp (hL.trans (band n hn).1)
    rw [←eq n n0]
    apply tail j n0 yp _ (sq_nonneg _)
    have low := mul_le_mul_of_nonneg_left (band n hn).2 (show 0≤4*Real.pi*Y by positivity)
    have same : 4*Real.pi*Y*(2*L)=(order j:ℝ)*Real.log (3/2) := by
      dsimp [Y,hScale]; field_simp [hL.ne',Real.pi_ne_zero] <;>ring
    nlinarith only [low,same]
  have inc := (Finset.sum_le_sum pt).trans ((strip_packet N r (by dsimp [r];omega) f g S yp).trans
    (moving_strip N r one yp f))
  change (∑ n∈S,ENNReal.ofReal (Real.pi*Real.Gamma s*R n))≤ENNReal.ofReal C*ENNReal.ofReal (‖f‖^2) at inc
  have main : Real.pi*Real.Gamma s*(∑ n∈S,R n) ≤ C*‖f‖^2 := by
    rw [←ENNReal.ofReal_mul cp,←ENNReal.ofReal_sum_of_nonneg (fun n _ =>
      mul_nonneg (mul_nonneg Real.pi_pos.le (Real.Gamma_pos_of_pos sp).le) (sq_nonneg _)),
      ← Finset.mul_sum,ENNReal.ofReal_le_ofReal_iff (mul_nonneg cp (sq_nonneg _))] at inc
    exact inc
  have sc : s/Real.pi*C=fixedBill N j L := by
    dsimp [s,C,Y,hScale,fixedBill]
    have sn : (order j:ℝ)≠0 := sp.ne'
    field_simp [Real.pi_ne_zero,hL.ne',lp.ne',np.ne',sn] <;>ring
  have gs : Real.Gamma (2*(j:ℝ)+2)=s*Real.Gamma s := by
    have ss : 2*(j:ℝ)+2=s+1 := by dsimp [s,order];push_cast;ring
    rw [ss,Real.Gamma_add_one sp.ne']
  calc
    _ = (s/Real.pi)*(Real.pi*Real.Gamma s*∑ n∈S,R n) := by
      rw [gs]; dsimp [R,g];field_simp [Real.pi_ne_zero] <;>ring
    _ ≤ (s/Real.pi)*(C*‖f‖^2) := mul_le_mul_of_nonneg_left main (div_nonneg sp.le Real.pi_pos.le)
    _ = _ := by rw [←mul_assoc,sc]

end ImbalancedChen.Part3.OriginalRegularHolomorphicWeight20261113
end
