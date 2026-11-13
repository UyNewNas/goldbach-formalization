import ImbalancedChen.Part3OriginalSwitchedInitialModulusRange

/-! Recombine the identical arithmetic interval and phase with the
actual first complete trace at each level, with all factorizations. -/
namespace ImbalancedChen.Part3.OriginalSwitchedInitialTraceGeometry20261113
noncomputable section
open Finset Complex
open scoped BigOperators
open OriginalSwitchedInitialModulusRange20261113 (mass broad_initial)
open OriginalSwitchedLevelIdentity20261113 (single spectral levelWeight)
open OriginalSwitchedCutoffFamily20261113 (profile)
open OriginalSwitchedPrescribedTrace20261113 (same_infinity_cutoff_trace)
open OriginalSameInfinityScalarGeometry20261113 (term)
open OriginalInfinitySwitchedGeometry20261113 (argument)
open OriginalSmoothedInitialMean20261113 (smoothSum)
open OriginalTwistedInitialMean20261113 (kernel)
open OriginalExceptionalJNativeCompletion20261110 (mem_full_classical_block)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open CommonSmoothCutoff (dyadicCutoff dyadicCutoff_tsupport_eq_tight dyadicCutoff_nonneg dyadicCutoff_le_one)
open private reindex_multiples from ImbalancedChen.Part3OriginalInfinitySwitchedGeometry
open private orbit from ImbalancedChen.Part3OriginalSwitchedLevelIdentity

def mark (a : ℕ) (ap : 0<a) {b : ℕ} (m : ↥(Ico a b)) : ℕ+ :=
  ⟨m.val,ap.trans_le (mem_Ico.mp m.property).1⟩

def total (q : ℕ+) (a b : ℕ) (ap : 0<a) (Y ω : ℝ) :=
  ∑ m : ↥(Ico a b),∑ n : ↥(Ico a b),star (phaseAt ω m.val)*phaseAt ω n.val*
    spectral q (mark a ap m) (mark a ap n) (single Y)

private theorem star_additive (ω : ℝ) (m : ℕ) : star (phaseAt ω m)=phaseAt (-ω) m := by
  unfold phaseAt
  rw [Complex.star_def,←Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,map_ofNat,map_natCast]
  push_cast;ring

private theorem cutoff (q m n : ℕ+) {Y : ℝ} (yp : 0<Y) (C : ℕ+)
    (h : 16*Real.pi*Y*Real.sqrt ((m.val:ℝ)*(n.val:ℝ))≤(C.val:ℝ)) :
    spectral q m n (single Y)=∑ d∈Icc 1 C,if q*d≤C then orbit (single Y) m n (q*d) else 0 := by
  have T := (same_infinity_cutoff_trace q m n false 0 Y yp).2.symm
  simp only [profile,Bool.false_eq_true,if_false,mul_one] at T
  have zero (k : ℕ+) (hk : k∉Icc 1 C) : single Y (argument m n k)=0 := by
    by_contra nz
    have p : dyadicCutoff (Y*argument m n k)≠0 := fun z => nz (by simp [single,z])
    have L := subset_tsupport _ p
    rw [dyadicCutoff_tsupport_eq_tight] at L
    have lo : 1/2≤Y*argument m n k := L.1
    let R := Real.sqrt ((m.val:ℝ)*(n.val:ℝ))
    have kp : 0<(k.val:ℝ) := by exact_mod_cast k.property
    have u := mul_le_mul_of_nonneg_right lo kp.le
    have e : (Y*argument m n k)*(k.val:ℝ)=4*Real.pi*Y*R := by
      change (Y*(4*Real.pi*R/(k.val:ℝ)))*(k.val:ℝ)=_
      field_simp [kp.ne'] <;> ring
    rw [e] at u
    have r0 : 0≤Real.pi*Y*R := mul_nonneg (mul_nonneg Real.pi_pos.le yp.le) (Real.sqrt_nonneg _)
    have c : k.val≤C.val := by exact_mod_cast (show (k.val:ℝ)≤C.val by nlinarith only [u,h,r0])
    exact hk (mem_Icc.mpr ⟨k.property,c⟩)
  have finite : (∑' k : ℕ+,term (single Y) q m n k)=∑ k∈Icc 1 C,term (single Y) q m n k :=
    tsum_eq_sum (fun k hk => by simp [term,zero k hk])
  exact T.trans (finite.trans (reindex_multiples C q (orbit (single Y) m n)))

theorem open_total (j a b : ℕ) (low : 2^j≤a) (high : b≤2^(j+1)) {Y : ℝ} (yp : 0<Y) :
    let ap := (pow_pos (by decide : 0<(2:ℕ)) j).trans_le low
    ∃ C : ℕ+,∀ (q : ℕ+) (ω : ℝ), total q a b ap Y ω=
      ∑ d∈Icc 1 C,if q*d≤C then smoothSum (q*d) a b a b (-ω) Y/((q*d).val:ℂ) else 0 := by
  let M := classicalMScale j
  let ap := (pow_pos (by decide : 0<(2:ℕ)) j).trans_le low
  obtain ⟨N,H⟩ := exists_nat_gt (32*Real.pi*M*Y)
  let C : ℕ+ := ⟨N+1,Nat.succ_pos _⟩
  let I := ↥(Ico a b)
  have cap (m : I) : (m.val:ℝ)≤2*M :=
    ((mem_full_classical_block j m.val).mp (show m.val∈dyadicWindow j from
      mem_Ico.mpr ⟨low.trans (mem_Ico.mp m.property).1,(mem_Ico.mp m.property).2.trans_le high⟩)).2
  have M0 : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have cut (q : ℕ+) (m n : I) := cutoff q (mark a ap m) (mark a ap n) yp C (by
    have bound : Real.sqrt ((m.val:ℝ)*(n.val:ℝ))≤2*M := by
      rw [show 2*M=Real.sqrt ((2*M)*(2*M)) by rw [←sq,Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (mul_le_mul (cap m) (cap n) (Nat.cast_nonneg _) (by positivity))
    have z := mul_le_mul_of_nonneg_left bound (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤16)
      Real.pi_pos.le) yp.le)
    change 16*Real.pi*Y*Real.sqrt ((m.val:ℝ)*(n.val:ℝ))≤((N+1:ℕ):ℝ)
    push_cast
    nlinarith only [z,H])
  refine ⟨C,fun q ω => ?_⟩
  unfold total
  simp_rw [cut,Finset.mul_sum,mul_ite,mul_zero]
  simp_rw [sum_comm (s:=(univ:Finset I)) (t:=Icc (1:ℕ+) C)]
  apply sum_congr rfl
  intro d _
  by_cases g : q*d≤C
  · simp only [if_pos g,smoothSum,Finset.sum_div,Finset.univ_eq_attach,Finset.sum_attach,
      orbit,mark,single,argument,kernel,star_additive,neg_neg]
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro n _
    ring
  · simp [g]

/-- The quantity being bounded is the complete three-sector first
trace after the marked interval contraction, on any finite level window. -/
theorem first_trace {ε : ℝ} (ep : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (j a b : ℕ) (low : 2^j≤a),a≤b → b≤2^(j+1) → ∀ (Y Q ω : ℝ),
      1≤Y → ∀ S : Finset ℕ+,
      let ap := (pow_pos (by decide : 0<(2:ℕ)) j).trans_le low
      let M := classicalMScale j
      let L := ((2^j:ℕ):ℝ)
      let X := 16*Real.pi*M*Y
      (∑ q∈S,‖levelWeight Q q*total q a b ap Y ω‖)≤C*(X*L*L)^ε*(X+L*L) := by
  obtain ⟨A,ac,P⟩ := broad_initial ep
  refine ⟨A,ac,fun j a b low ab high Y Q ω y1 S => ?_⟩
  let ap := (pow_pos (by decide : 0<(2:ℕ)) j).trans_le low
  obtain ⟨C,eq⟩ := open_total j a b low high (zero_lt_one.trans_le y1)
  let T := Icc (1:ℕ+) C
  have per (q : ℕ+) : ‖levelWeight Q q*total q a b ap Y ω‖≤∑ d∈T,mass a b (-ω) Y (q,d) := by
    rw [norm_mul]
    have wt : ‖levelWeight Q q‖≤1 := by
      simp only [levelWeight,Complex.norm_real,Real.norm_of_nonneg (dyadicCutoff_nonneg _)]
      exact dyadicCutoff_le_one _
    apply (mul_le_of_le_one_left (norm_nonneg _) wt).trans
    rw [eq q ω]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro d _
    by_cases g : q*d≤C
    · simp only [if_pos g,mass,norm_div,Complex.norm_natCast,le_rfl]
    · simp only [if_neg g,norm_zero]
      exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  apply (sum_le_sum (s:=S) (fun q _ => per q)).trans
  have B := P j a b low ab high Y (-ω) y1 (S×ˢT)
  simpa only [Finset.sum_product] using B

/-- At the original classical length and any subinterval, the
arithmetic term has the epsilon and power scale used in (4.30). -/
theorem initial_geometry {ε : ℝ} (ep : 0<ε) :
    ∃ D : ℝ,0<D ∧ ∀ (j a b : ℕ) (low : 2^j≤a),a≤b → b≤2^(j+1) → ∀ (Y Q ω : ℝ),
      1≤Y → ∀ S : Finset ℕ+,
      let ap := (pow_pos (by decide : 0<(2:ℕ)) j).trans_le low
      let M := classicalMScale j
      (∑ q∈S,‖levelWeight Q q*total q a b ap Y ω‖)≤D*((1+M)*(1+Y))^ε*(M+Y)*M := by
  let δ := ε/3
  have dp : 0<δ := div_pos ep (by norm_num)
  obtain ⟨A,ac,H⟩ := first_trace dp
  let H₀ := (64*Real.pi)^δ
  let C := 16*Real.pi+4
  have hpos : 0<H₀ := Real.rpow_pos_of_pos (by positivity) _
  have cp : 0<C := by dsimp [C];positivity
  refine ⟨A*H₀*C,mul_pos (mul_pos ac hpos) cp,fun j a b low ab high Y Q ω y1 S => ?_⟩
  let M := classicalMScale j
  let L : ℝ := (2^j:ℕ)
  let X := 16*Real.pi*M*Y
  let V := (1+M)*(1+Y)
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have yp := zero_lt_one.trans_le y1
  have ln : 0≤L := Nat.cast_nonneg _
  have l : L≤2*M := by linarith only [(classicalMScale_bounds j).2.1]
  have v1 : 1≤V := by dsimp only [V];nlinarith only [mp,yp,mul_nonneg mp.le yp.le]
  have mv : M≤V := by dsimp only [V];nlinarith only [yp,mul_nonneg mp.le yp.le]
  have myv : M*Y≤V := by dsimp only [V];nlinarith only [mp,yp]
  have raw : X*L*L≤(64*Real.pi)*V^3 := by
    have h1 := mul_le_mul_of_nonneg_left myv (by positivity : 0≤16*Real.pi)
    have lv : L≤2*V := l.trans (mul_le_mul_of_nonneg_left mv (by norm_num))
    have h2 := mul_le_mul (mul_le_mul h1 lv ln (by positivity)) lv ln (by positivity)
    dsimp only [X]
    nlinarith only [h2]
  have power := Real.rpow_le_rpow (by dsimp only [X];positivity : 0≤X*L*L) raw dp.le
  have eq : (V^3)^δ=V^ε := by
    rw [←Real.rpow_natCast V 3,←Real.rpow_mul (zero_le_one.trans v1),
      show ((3:ℕ):ℝ)*δ=ε by dsimp only [δ];norm_num <;> ring]
  rw [Real.mul_rpow (by positivity : 0≤64*Real.pi) (pow_nonneg (zero_le_one.trans v1) 3),eq] at power
  have length : X+L*L≤C*(M+Y)*M := by
    have h := mul_le_mul l l ln (by positivity)
    dsimp only [X,C]
    nlinarith only [h,mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤16) Real.pi_pos.le) (sq_nonneg M),
      mul_nonneg mp.le yp.le]
  apply (H j a b low ab high Y Q ω y1 S).trans
  apply (mul_le_mul (mul_le_mul_of_nonneg_left power ac.le) length
    (by dsimp only [X];positivity) (mul_nonneg ac.le (mul_nonneg hpos.le (Real.rpow_nonneg (zero_le_one.trans v1) _)))).trans_eq
  dsimp only [V,H₀,C,M];ring

end
end ImbalancedChen.Part3.OriginalSwitchedInitialTraceGeometry20261113
