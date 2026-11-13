import ImbalancedChen.Part3OriginalMellinPrefixVariation
import ImbalancedChen.Part3OriginalSwitchedTwistedBaseline

/-! Remove the accumulated Mellin twist simultaneously on all native
exceptional rows. The maximal prefix comes after the full energy. -/
namespace ImbalancedChen.Part3.OriginalSwitchedNativePrefixEnergy20261113
noncomputable section
open Finset
open scoped BigOperators
open OriginalMellinPrefixVariation20261113 (coeff abel variation)
open OriginalSwitchedMellinRows20261113 (twistedRow nativeRow wave wave_zero)
open OriginalSwitchedTwistedBaseline20261113 (energy)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)

def intervalEnergy (S : Finset ℕ+) (X ω : ℝ) (a b : ℕ) (t : ℝ) :=
  ∑ z ∈ S,∑ v : ↥(exceptional z),X^(tau z v.val)*
    ‖twistedRow (Ico a b) (nativeRow z v.val ω) t‖^2

theorem full_window (S : Finset ℕ+) (X ω t : ℝ) (j : ℕ) :
    intervalEnergy S X ω (2^j) (2^(j+1)) t=energy S X j ω t := rfl

/-- Native square-root transport on exactly the levels carrying the
Selberg bound; the uniform provider for this explicit premise is external. -/
theorem weight_transport (S : Finset ℕ+) {X Z : ℝ} (zp : 0<Z) (order : Z≤X)
    (τ : ∀ z∈S,∀ i : ↥(exceptional z),tau z i.val≤1/2) (ω t : ℝ) (a b : ℕ) :
    intervalEnergy S X ω a b t≤Real.sqrt (X/Z)*intervalEnergy S Z ω a b t := by
  have one : 1≤X/Z := (le_div_iff₀ zp).mpr (by simpa only [one_mul] using order)
  simp only [intervalEnergy,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  apply Finset.sum_le_sum
  intro i _
  have sep : X^(tau z i.val)=(X/Z)^(tau z i.val)*Z^(tau z i.val) := by
    rw [←Real.mul_rpow (div_nonneg (zp.trans_le order).le zp.le) zp.le,div_mul_cancel₀ _ zp.ne']
  have p := Real.rpow_le_rpow_of_exponent_le one (τ z hz i)
  rw [←Real.sqrt_eq_rpow] at p
  rw [sep,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right p (Real.rpow_nonneg zp.le _)) (sq_nonneg _)

private theorem weighted_sq (P : Finset ℕ) (c v : ℕ→ℂ) :
    ‖∑ i ∈ P,c i*v i‖^2≤(∑ i ∈ P,‖c i‖)*∑ i ∈ P,‖c i‖*‖v i‖^2 := by
  let r := fun i => ‖c i‖*‖v i‖
  have A : ‖∑ i ∈ P,c i*v i‖≤∑ i ∈ P,r i := by
    simpa only [r,norm_mul] using norm_sum_le P (fun i => c i*v i)
  have B := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul P (r:=r) (f:=fun i => ‖c i‖)
    (g:=fun i => ‖c i‖*‖v i‖^2) (fun i _ => norm_nonneg _) (fun _ _ => by positivity)
    (fun i _ => by dsimp only [r];exact le_of_eq (by ring))
  exact (pow_le_pow_left₀ (norm_nonneg _) A 2).trans B

theorem prefix_energy (S : Finset ℕ+) {X : ℝ} (xp : 0≤X) (ω t : ℝ) {a b : ℕ}
    (ap : 0<a) (ab : a≤b) (cap : b≤2*a) :
    intervalEnergy S X ω a b t≤(1+|t|)^2*
      (Icc a b).sup' ⟨a,mem_Icc.mpr ⟨le_rfl,ab⟩⟩
        (fun i => intervalEnergy S X ω a (min b (i+1)) 0) := by
  classical
  let P := Icc a b
  let A := fun i => ‖coeff t b i‖
  let L := ∑ i ∈ P,A i
  let W := fun i => intervalEnergy S X ω a (min b (i+1)) 0
  have ne : P.Nonempty := ⟨a,mem_Icc.mpr ⟨le_rfl,ab⟩⟩
  let V := P.sup' ne W
  have Vp : 0≤V := by
    have p : 0≤W a := by
      unfold W intervalEnergy
      exact sum_nonneg (fun z _ => sum_nonneg (fun v _ => mul_nonneg (Real.rpow_nonneg xp _) (sq_nonneg _)))
    exact p.trans (Finset.le_sup' W (show a∈P from mem_Icc.mpr ⟨le_rfl,ab⟩))
  have Lp : 0≤L := sum_nonneg (fun i _ => norm_nonneg _)
  have H (z : ℕ+) (v : ↥(exceptional z)) :
      ‖twistedRow (Ico a b) (nativeRow z v.val ω) t‖^2≤L*
        ∑ i ∈ P,A i*‖twistedRow (Ico a (min b (i+1))) (nativeRow z v.val ω) 0‖^2 := by
    let F := nativeRow z v.val ω
    have w := weighted_sq P (coeff t b) (fun i => ∑ m ∈ Ico a (min b (i+1)),F m)
    have line : twistedRow (Ico a b) F t=∑ i ∈ P,coeff t b i*(∑ m ∈ Ico a (min b (i+1)),F m) := by
      rw [←abel]
      exact sum_congr rfl (fun m _ => mul_comm _ _)
    rw [←line] at w
    simpa only [twistedRow,wave_zero,mul_one,F] using w
  have raw := sum_le_sum (s:=S) (fun z _ => sum_le_sum (s:=(univ:Finset ↥(exceptional z)))
    (fun v _ => mul_le_mul_of_nonneg_left (H z v) (Real.rpow_nonneg xp _)))
  have swap : (∑ z ∈ S,∑ v : ↥(exceptional z),X^(tau z v.val)*
      (L*∑ i ∈ P,A i*‖twistedRow (Ico a (min b (i+1))) (nativeRow z v.val ω) 0‖^2))=
      L*∑ i ∈ P,A i*W i := by
    simp only [W,intervalEnergy,Finset.mul_sum]
    rw [sum_comm (s:=P) (t:=S)]
    apply sum_congr rfl
    intro z _
    rw [sum_comm (s:=P) (t:=(univ:Finset ↥(exceptional z)))]
    apply sum_congr rfl
    intro v _
    apply sum_congr rfl
    intro i _
    ring
  have per : (∑ i ∈ P,A i*W i)≤∑ i ∈ P,A i*V := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (Finset.le_sup' W hi) (norm_nonneg (coeff t b i)))
  rw [←sum_mul] at per
  change intervalEnergy S X ω a b t≤(1+|t|)^2*V
  have stage : intervalEnergy S X ω a b t≤L*∑ i ∈ P,A i*W i :=
    raw.trans_eq swap
  calc
    _ ≤ L*(L*V) := stage.trans (mul_le_mul_of_nonneg_left per Lp)
    _ = L^2*V := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ Lp (variation t ap ab cap) 2) Vp

end
end ImbalancedChen.Part3.OriginalSwitchedNativePrefixEnergy20261113
