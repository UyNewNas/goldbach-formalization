import ImbalancedChen.Part3OriginalTwistedSqrtGram
import OAI.NumberTheory.CubicMoment.Estimates.GramOperator
import ImbalancedChen.Part3FiniteUnitInverseL2

/-! Arbitrary-sequence bounds for the two factors after splitting the
physical m variable into complete blocks of c possible offsets. The right
factor retains both the additive residue and the block-dependent square
root. Left inputs may be padded by zeros, in particular in the final
partial block. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalTwistedSqrtAnalysis20261113
open Finset Complex
open OriginalTwistedSqrtGram20261113
open OAI.Problem337.ExponentialSum (phase phase_add phase_norm)
open OriginalSmoothPoissonTail.FiniteOperator20261026b (dft dft_energy energy)
open OriginalSmoothPoissonTail (kloosterman)

def rows (M c : ℕ) : Finset (ℕ×ℕ) := (range (blockCount M c)) ×ˢ (range c)
def row (M c : ℕ) (θ : ℝ) (r : ℕ×ℕ) (i : ℕ) := phase (rowAngle M c θ r.1 r.2 i)
def budget (M : ℕ) (θ : ℝ) : ℝ := 244*M*(1+Real.log M)/θ

theorem budget_nonneg {M : ℕ} (hM : 0<M) {θ : ℝ} (hθ : 0<θ) : 0≤budget M θ := by
  have h := Real.log_nonneg (show 1≤(M:ℝ) by exact_mod_cast (show 1≤M by omega))
  unfold budget
  positivity

theorem full_row_energy {M c : ℕ} (hc : 0<c) (hcM : c≤M) {θ : ℝ}
    (hθ : 0<θ) (hθ' : θ≤2) (b : ℕ → ℂ) :
    (∑ r∈rows M c,‖∑ i∈range (M+1),b i*row M c θ r i‖^2)≤
      budget M θ*∑ i∈range (M+1),‖b i‖^2 := by
  apply OAI.CubicFirstMoment.finite_gram_operator_le _ _ _ _ (budget_nonneg (hc.trans_le hcM) hθ)
  intro r hr
  have E (q : ℕ×ℕ) : OAI.CubicFirstMoment.finiteGram (range (M+1)) (row M c θ) r q =
      gram M c θ r.1 r.2 q.1 q.2 := (gram_eq_products ..).symm
  simp only [rows,mem_product,mem_range] at hr
  simp only [E,rows,sum_product,budget]
  exact gram_row_sum (M:=M) hc hcM hθ hθ' hr.1 hr.2

/-- Left part of the physical complete block. Its first phase is common
over the block and has norm one. The inner transform is the previously
established DFT on every positive composite residue ring. -/
def left (M c : ℕ) [NeZero c] (a : ℕ → ZMod c → ℂ) (s : ℕ) (u : ZMod c) : ℂ :=
  ZMod.stdAddChar (((M+s*c:ℕ):ZMod c)*u)*dft c (a s) u

theorem left_energy (M c : ℕ) [NeZero c] (a : ℕ → ZMod c → ℂ) :
    (∑ s∈range (blockCount M c),∑ u : ZMod c,‖left M c a s u‖^2)=
      (c:ℝ)*∑ s∈range (blockCount M c),∑ h : ZMod c,‖a s h‖^2 := by
  rw [mul_sum]
  apply sum_congr rfl
  intro s hs
  have hu (s : ℕ) (u : ZMod c) : ‖left M c a s u‖=‖dft c (a s) u‖ := by
    simp only [left,norm_mul,ZMod.stdAddChar_apply,Circle.norm_coe,one_mul]
  simp only [hu]
  exact dft_energy c (a s)

def right (M c : ℕ) (θ : ℝ) (b : ℕ → ℂ) (s j : ℕ) : ℂ :=
  ∑ i∈range (M+1),b i*row M c θ (s,j) i

private theorem sum_val (c : ℕ) [NeZero c] (v : ℕ → ℝ) :
    (∑ u : ZMod c,v u.val)=∑ j∈range c,v j := by
  apply sum_bij' (fun u _ => u.val) (fun j _ => (j:ZMod c))
  · intro u hu;exact mem_range.mpr (ZMod.val_lt u)
  · intro j hj;exact mem_univ _
  · intro u hu;exact ZMod.natCast_zmod_val u
  · intro j hj;exact ZMod.val_natCast_of_lt (mem_range.mp hj)
  · intro u hu;rfl

private theorem sum_units_le (c : ℕ) [NeZero c] (f : ZMod c → ℝ) (hf : ∀ u,0≤f u) :
    (∑ u : (ZMod c)ˣ,f u)≤∑ u : ZMod c,f u := by
  apply sum_le_injected (fun u : (ZMod c)ˣ => (u:ZMod c))
  · intro x hx y hy h;exact Units.ext h
  · exact subset_univ _
  · intro u hu;exact le_rfl
  · intro u hu h;exact hf u

def unitRows (M c : ℕ) [NeZero c] : Finset (ℕ × (ZMod c)ˣ) :=
  (range (blockCount M c)) ×ˢ univ

private theorem right_unit_energy {M c : ℕ} [NeZero c] (hcM : c≤M) {θ : ℝ}
    (hθ : 0<θ) (hθ' : θ≤2) (b : ℕ → ℂ) :
    (∑ r∈unitRows M c,‖right M c θ b r.1 (((r.2⁻¹:(ZMod c)ˣ):ZMod c).val)‖^2) ≤
      budget M θ*∑ i∈range (M+1),‖b i‖^2 := by
  apply le_trans _ (full_row_energy (NeZero.pos c) hcM hθ hθ' b)
  simp only [unitRows,rows,sum_product]
  apply sum_le_sum
  intro s hs
  let f := fun u : ZMod c => ‖right M c θ b s u.val‖^2
  change (∑ u : (ZMod c)ˣ,f (u⁻¹:(ZMod c)ˣ))≤_
  calc
    _=∑ u : (ZMod c)ˣ,f u := by
      apply sum_bij' (fun u _ => u⁻¹) (fun u _ => u⁻¹) <;> simp
    _≤∑ u : ZMod c,f u := sum_units_le c f (fun _ => sq_nonneg _)
    _=∑ j∈range c,‖right M c θ b s j‖^2 := sum_val c _

def separated (M c : ℕ) [NeZero c] (θ : ℝ) (a : ℕ → ZMod c → ℂ) (b : ℕ → ℂ) : ℂ :=
  ∑ r∈unitRows M c,left M c a r.1 r.2*right M c θ b r.1 (((r.2⁻¹:(ZMod c)ˣ):ZMod c).val)

/-- Every m block is paired with its own square-root modulation, while one
common arbitrary vector b is used on the n side of every block. -/
theorem separated_bound {M c : ℕ} [NeZero c] (hcM : c≤M) {θ : ℝ} (hθ : 0<θ)
    (hθ' : θ≤2) (a : ℕ → ZMod c → ℂ) (b : ℕ → ℂ) :
    ‖separated M c θ a b‖≤
      Real.sqrt ((c:ℝ)*budget M θ)*
        Real.sqrt (∑ s∈range (blockCount M c),∑ h : ZMod c,‖a s h‖^2)*
        Real.sqrt (∑ i∈range (M+1),‖b i‖^2) := by
  let U := unitRows M c
  let l := fun r : ℕ×(ZMod c)ˣ => left M c a r.1 r.2
  let v := fun r : ℕ×(ZMod c)ˣ => right M c θ b r.1 (((r.2⁻¹:(ZMod c)ˣ):ZMod c).val)
  let A := ∑ s∈range (blockCount M c),∑ h : ZMod c,‖a s h‖^2
  let B := ∑ i∈range (M+1),‖b i‖^2
  have a0 : 0≤A := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))
  have b0 : 0≤B := sum_nonneg (fun _ _ => sq_nonneg _)
  have u0 := budget_nonneg ((NeZero.pos c).trans_le hcM) hθ
  have L : (∑ r∈U,‖l r‖^2)≤c*A := by
    dsimp only [A]
    rw [←left_energy M c a]
    simp only [U,unitRows,sum_product,l]
    exact sum_le_sum (fun s hs => sum_units_le c _ (fun u => sq_nonneg ‖left M c a s u‖))
  have V : (∑ r∈U,‖v r‖^2)≤budget M θ*B := right_unit_energy hcM hθ hθ' b
  have Q := (OAI.CubicFirstMoment.complex_bilinear_rows_sq U l v).trans
    (mul_le_mul L V (sum_nonneg (fun _ _ => sq_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) a0))
  have W := Real.sqrt_le_sqrt Q
  rw [Real.sqrt_sq (norm_nonneg _),Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg _) a0),
    Real.sqrt_mul (Nat.cast_nonneg c),Real.sqrt_mul u0] at W
  rw [Real.sqrt_mul (Nat.cast_nonneg c)]
  change ‖∑ r∈U,l r*v r‖≤_
  calc
    _≤_ := W
    _=_ := by ring

def mode (M c s h : ℕ) : ℕ := M+s*c+h

def primaryAngle (M c : ℕ) (θ : ℝ) (s i : ℕ) : ℝ :=
  2*θ/c*Real.sqrt (anchor M c s)*Real.sqrt (M+i:ℕ)

private theorem char_val (c : ℕ) [NeZero c] (n : ℕ) (u : ZMod c) :
    ZMod.stdAddChar ((n:ZMod c)*u)=phase ((u.val:ℝ)/c*n) := by
  have he : ((n*u.val:ℕ):ZMod c)=(n:ZMod c)*u := by simp
  rw [←he]
  have hi : ((n*u.val:ℕ):ZMod c)=(((n*u.val:ℕ):ℤ):ZMod c) := by simp
  rw [hi,ZMod.stdAddChar_coe,phase]
  push_cast
  congr 1
  ring

private theorem right_eq (M c : ℕ) [NeZero c] (θ : ℝ) (b : ℕ → ℂ) (s : ℕ) (u : ZMod c) :
    right M c θ b s u.val = ∑ i∈range (M+1),
      b i * (ZMod.stdAddChar (((M+i:ℕ):ZMod c)*u)*phase (primaryAngle M c θ s i)) := by
  apply sum_congr rfl
  intro i hi
  rw [char_val]
  simp only [row,rowAngle,primaryAngle,phase_add]

private theorem left_eq (M c : ℕ) [NeZero c] (a : ℕ → ZMod c → ℂ) (s : ℕ) (u : ZMod c) :
    left M c a s u=∑ h : ZMod c,a s h*ZMod.stdAddChar (((mode M c s h.val:ℕ):ZMod c)*u) := by
  simp only [left,dft,mul_sum]
  apply sum_congr rfl
  intro h hh
  simp only [mode,Nat.cast_add,ZMod.natCast_zmod_val,add_mul,AddChar.map_add_eq_mul]
  rw [mul_comm u h] <;> ring

/-- Literal Kloosterman arithmetic on each m and n, in the block anchor
approximation on the square-root phase only. -/
theorem separated_eq_kloosterman (M c : ℕ) [NeZero c] (θ : ℝ)
    (a : ℕ → ZMod c → ℂ) (b : ℕ → ℂ) :
    separated M c θ a b =
      ∑ s∈range (blockCount M c),∑ h : ZMod c,∑ i∈range (M+1),
        a s h*b i*phase (primaryAngle M c θ s i)*
          kloosterman c (mode M c s h.val:ℤ) (M+i:ℕ) := by
  simp only [separated,unitRows,sum_product,left_eq,right_eq,sum_mul_sum]
  apply sum_congr rfl
  intro s hs
  rw [sum_comm]
  apply sum_congr rfl
  intro h hh
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [OriginalSmoothPoissonTail.Physical.kloosterman_eq_zmod,
    OriginalSmoothPoissonTail.FiniteOperator20261026b.sum_unitGate_eq_units,mul_sum]
  apply sum_congr rfl
  intro u hu
  simp only [Int.cast_natCast,AddChar.map_add_eq_mul,ZMod.inv_coe_unit]
  ring

end ImbalancedChen.Part3.OriginalTwistedSqrtAnalysis20261113
end
