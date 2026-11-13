import ImbalancedChen.Part3OriginalFactoredInitialMean
import ImbalancedChen.Part3OriginalSwitchedNativeBilinearTrace

/-! The physical full-modulus support has a fixed ratio. Accumulate all
factorized divisors without strengthening the inverse-sum estimate. -/
namespace ImbalancedChen.Part3.OriginalSwitchedInitialModulusRange20261113
noncomputable section
open Finset
open scoped BigOperators
open OriginalFactoredInitialMean20261113 (factored_initial_mean smooth_modulus_support)
open OriginalSmoothedInitialMean20261113 (smoothSum)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalExceptionalJNativeCompletion20261110 (mem_full_classical_block)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)

def mass (a b : ℕ) (ω Y : ℝ) (p : ℕ+×ℕ+) := ‖smoothSum (p.1*p.2) a b a b ω Y‖/((p.1*p.2).val:ℝ)

theorem broad_initial {ε : ℝ} (ep : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (j a b : ℕ),2^j≤a → a≤b → b≤2^(j+1) → ∀ (Y ω : ℝ),1≤Y →
      ∀ S : Finset (ℕ+×ℕ+),
      let M := classicalMScale j
      let L := ((2^j:ℕ):ℝ)
      let X := 16*Real.pi*M*Y
      (∑ p∈S,mass a b ω Y p)≤C*(X*L*L)^ε*(X+L*L) := by
  classical
  obtain ⟨C,cp,H⟩ := factored_initial_mean ep
  refine ⟨4*C,by positivity,fun j a b low ab high Y ω y1 S => ?_⟩
  let M := classicalMScale j
  let L : ℝ := (2^j:ℕ)
  let X := 16*Real.pi*M*Y
  let K := Real.pi*M*Y
  let V := fun p => mass a b ω Y p
  let qty := fun p : ℕ+×ℕ+ => ((p.1*p.2).val:ℝ)
  let Kt := fun r : Fin 4 => (2:ℝ)^r.val*K
  let F := fun r : Fin 4 => S.filter (fun p => Kt r≤qty p ∧ qty p≤2*Kt r)
  let bill := C*(X*L*L)^ε*(X+L*L)
  have mp : 1/2≤M := (classicalMScale_bounds j).1
  have yp := zero_lt_one.trans_le y1
  have kp : 1≤K := by
    have h := mul_le_mul_of_nonneg_right mp Real.pi_pos.le
    have p : 1≤Real.pi*M := by linarith only [h,Real.pi_gt_three]
    exact p.trans (le_mul_of_one_le_right (zero_le_one.trans p) y1)
  have lo : 0<a := (pow_pos (by decide : 0<(2:ℕ)) _).trans_le low
  have Np : 1≤2^j := Nat.pow_pos (by decide : 0<(2:ℕ)) j
  have len : b-a≤2^j := by rw [pow_succ] at high;omega
  have cap : b≤2*a := by rw [pow_succ] at high;omega
  have band (m : ℕ) (hm : m∈Ico a b) : M≤(m:ℝ) ∧ (m:ℝ)≤2*M := by
    have m0 := mem_Ico.mp hm
    have m1 := (mem_full_classical_block j m).mp (show m∈dyadicWindow j from mem_Ico.mpr ⟨low.trans m0.1,m0.2.trans_le high⟩)
    exact ⟨m1.1.le,m1.2⟩
  have vpn (p : ℕ+×ℕ+) : 0≤V p := div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  have priced (r : Fin 4) : (∑ p∈F r,V p)≤bill := by
    let v := Kt r
    let N := ⌊2*v⌋₊
    have vp : 1≤v := kp.trans (le_mul_of_one_le_left (zero_le_one.trans kp) (one_le_pow₀ (by norm_num : (1:ℝ)≤2)))
    have above : 1≤N := (Nat.le_floor (by linarith only [vp] : (1:ℝ)≤2*v))
    have nf : (N:ℝ)≤2*v := Nat.floor_le (by linarith only [vp])
    have nx : (N:ℝ)≤X := by
      apply nf.trans
      change 2*((2:ℝ)^r.val*K)≤16*Real.pi*M*Y
      rw [show 16*Real.pi*M*Y=16*K by dsimp only [K];ring]
      fin_cases r <;> norm_num <;> linarith only [kp]
    have hf (p) (hp : p∈F r) : v≤qty p ∧ (p.1*p.2).val≤N :=
      ⟨(mem_filter.mp hp).2.1,Nat.le_floor (mem_filter.mp hp).2.2⟩
    have e := H (F r) v N (2^j) (2^j) (zero_lt_one.trans_le vp) nf above Np Np hf
      a b a b lo ab cap len lo ab cap len ω Y yp
    apply e.trans
    have ln : 0≤L := Nat.cast_nonneg _
    have a₁ := Real.rpow_le_rpow (by positivity : 0≤(N:ℝ)*L*L)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right nx ln) ln) ep.le
    have a₂ : (N:ℝ)+L*L≤X+L*L := by linarith only [nx]
    exact mul_le_mul (mul_le_mul_of_nonneg_left a₁ cp.le) a₂ (by positivity)
      (mul_nonneg cp.le (Real.rpow_nonneg (by dsimp [X,L];positivity) _))
  have cover (p) (hp : p∈S) : V p≤∑ r : Fin 4,if p∈F r then V p else 0 := by
    by_cases z : smoothSum (p.1*p.2) a b a b ω Y=0
    · change ‖smoothSum (p.1*p.2) a b a b ω Y‖/_≤_
      rw [z,norm_zero,zero_div]
      exact sum_nonneg (fun _ _ => by split_ifs <;> first | exact vpn _ | exact le_rfl)
    · have w := smooth_modulus_support (p.1*p.2) a b a b ω (by linarith only [mp] : 0<M) yp band band z
      have l : K≤qty p := by
        change Real.pi*M*Y≤((p.1*p.2).val:ℝ)
        nlinarith only [w.1,show 0≤Real.pi*M*Y from zero_le_one.trans kp]
      have u : qty p≤16*K := w.2.trans_eq (by dsimp only [K];ring)
      have found : ∃ r : Fin 4,p∈F r := by
        by_cases a0 : qty p≤2*K
        · exact ⟨0,mem_filter.mpr ⟨hp,by simpa [Kt] using l,by simpa [Kt] using a0⟩⟩
        by_cases a1 : qty p≤4*K
        · exact ⟨1,mem_filter.mpr ⟨hp,by norm_num [Kt] <;> linarith only [a0],by norm_num [Kt] <;> linarith only [a1]⟩⟩
        by_cases a2 : qty p≤8*K
        · exact ⟨2,mem_filter.mpr ⟨hp,by norm_num [Kt] <;> linarith only [a1],by norm_num [Kt] <;> linarith only [a2]⟩⟩
        exact ⟨3,mem_filter.mpr ⟨hp,by norm_num [Kt] <;> linarith only [a2],by norm_num [Kt] <;> linarith only [u]⟩⟩
      obtain ⟨r,hr⟩ := found
      have v := single_le_sum (f:=fun k : Fin 4 => if p∈F k then V p else 0)
        (fun i _ => by split_ifs <;> first | exact vpn _ | exact le_rfl) (mem_univ r)
      simpa only [if_pos hr] using v
  calc
    _ ≤ ∑ p∈S,∑ r : Fin 4,if p∈F r then V p else 0 := sum_le_sum cover
    _ = ∑ r : Fin 4,∑ p∈F r,V p := by
      rw [sum_comm (s:=S) (t:=univ)]
      apply sum_congr rfl
      intro r _
      rw [←sum_filter]
      have e : S.filter (fun p => p∈F r)=F r := by
        ext p;simp [F,and_assoc]
      rw [e]
    _ ≤ ∑ _r : Fin 4,bill := sum_le_sum (fun r _ => priced r)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat];dsimp only [bill];ring

end
end ImbalancedChen.Part3.OriginalSwitchedInitialModulusRange20261113
