import ImbalancedChen.Part3OriginalTwistedSqrtTaylor

/-! Uniform arbitrary-sequence bound for the damped, square-root-twisted
same-cusp Kloosterman bilinear form appearing in Drappeau (4.21).
Both coefficient vectors are complex and independent. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalTwistedKloosterman20261113
open Complex Finset
open OriginalTwistedSqrtGram20261113 (anchor blockCount)
open OriginalTwistedSqrtAnalysis20261113 (mode separated separated_eq_kloosterman separated_bound budget)
open OriginalTwistedSqrtTaylor20261113
open OriginalSmoothPoissonTail (kloosterman)

def blockForm (M c : ℕ) [NeZero c] (lam θ : ℝ) (a : ℕ → ZMod c → ℂ) (b : ℕ → ℂ) : ℂ :=
  ∑ s∈range (blockCount M c),∑ h : ZMod c,∑ i∈range (M+1),
    (a s h*b i*kloosterman c (mode M c s h.val:ℤ) (M+i:ℕ))*
      fullFactor lam θ c (Real.sqrt (mode M c s h.val)) (Real.sqrt (M+i:ℕ))

theorem block_form_bound {M c : ℕ} [NeZero c] (hcM : c≤M) {lam θ : ℝ} (hlam : 0≤lam)
    (hθ : 0<θ) (hθ' : θ≤2) (a : ℕ → ZMod c → ℂ) (b : ℕ → ℂ)
    (pad : ∀ s h, 2*M<mode M c s h.val → a s h=0) :
    ‖blockForm M c lam θ a b‖≤Real.exp (4*Real.pi)*
      (Real.sqrt ((c:ℝ)*budget M θ)*
      Real.sqrt (∑ s∈range (blockCount M c),∑ h : ZMod c,‖a s h‖^2)*
      Real.sqrt (∑ i∈range (M+1),‖b i‖^2)) := by
  let x := Real.sqrt (M:ℝ)
  let A := fun j s (h : ZMod c) => a s h*leftWeight lam θ c x
    (Real.sqrt (mode M c s h.val)) (Real.sqrt (anchor M c s)) j
  let B := fun j i => b i*rightWeight lam x (Real.sqrt (M+i:ℕ)) j
  let F := fun j => separated M c θ (A j) (B j)
  let EA := ∑ s∈range (blockCount M c),∑ h : ZMod c,‖a s h‖^2
  let EB := ∑ i∈range (M+1),‖b i‖^2
  let K := Real.sqrt ((c:ℝ)*budget M θ)
  have hM := (NeZero.pos c).trans_le hcM
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have xp : 0<x := Real.sqrt_pos.mpr mp
  have H : HasSum F (blockForm M c lam θ a b) := by
    have h := hasSum_sum (s:=range (blockCount M c)) fun s _ =>
      hasSum_sum (s:=(univ : Finset (ZMod c))) fun v _ =>
      hasSum_sum (s:=range (M+1)) fun i _ =>
      (factor_hasSum lam θ c x (Real.sqrt (mode M c s v.val))
        (Real.sqrt (anchor M c s)) (Real.sqrt (M+i:ℕ)) xp).mul_left
        (a s v*b i*kloosterman c (mode M c s v.val:ℤ) (M+i:ℕ))
    apply h.congr_fun
    intro j
    rw [show F j=separated M c θ (A j) (B j) by rfl,separated_eq_kloosterman]
    apply sum_congr rfl
    intro s hs
    apply sum_congr rfl
    intro v hv
    apply sum_congr rfl
    intro i hi
    dsimp only [A,B,OriginalTwistedSqrtAnalysis20261113.primaryAngle]
    ring
  have Fbound (j : ℕ) : ‖F j‖≤weightBill M lam j*(K*Real.sqrt EA*Real.sqrt EB) := by
    have w0 := weightBill_nonneg M hlam j
    have a0 : 0≤EA := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))
    have L : (∑ s∈range (blockCount M c),∑ h : ZMod c,‖A j s h‖^2)≤
        (weightBill M lam j)^2*EA := by
      dsimp only [EA]
      rw [mul_sum]
      apply sum_le_sum
      intro s hs
      rw [mul_sum]
      apply sum_le_sum
      intro h hh
      by_cases low : mode M c s h.val≤2*M
      · have aM : (M:ℝ)≤anchor M c s := by
          unfold anchor; exact_mod_cast (show M≤M+s*c by omega)
        have am : anchor M c s≤(mode M c s h.val:ℝ) := by
          unfold anchor mode; exact_mod_cast (show M+s*c≤M+s*c+h.val by omega)
        have mc : (mode M c s h.val:ℝ)-anchor M c s≤c := by
          unfold anchor mode
          simp only [Nat.cast_add,Nat.cast_mul]
          have hval : (h.val:ℝ)≤c := by exact_mod_cast (ZMod.val_lt h).le
          linarith only [hval]
        have T := leftWeight_norm hM hlam (by exact_mod_cast NeZero.pos c : 0<(c:ℝ))
          ⟨hθ.le,hθ'⟩ aM am (by exact_mod_cast low) mc j
        dsimp only [A]
        rw [norm_mul,mul_pow,mul_comm ((weightBill M lam j)^2)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) T 2) (sq_nonneg _)
      · simp [A,pad s h (lt_of_not_ge low)]
    have R : (∑ i∈range (M+1),‖B j i‖^2)≤EB := by
      apply sum_le_sum
      intro i hi
      have hI := mem_range.mp hi
      have hi' : ((M+i:ℕ):ℝ)∈Set.Icc (M:ℝ) (2*M) :=
        ⟨by exact_mod_cast Nat.le_add_right M i,by exact_mod_cast (show M+i≤2*M by omega)⟩
      have T := rightWeight_norm mp hlam hi' j
      dsimp only [B]
      rw [norm_mul,mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) T)
    have u := Real.sqrt_le_sqrt L
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq w0] at u
    have v := Real.sqrt_le_sqrt R
    calc
      _≤_ := separated_bound hcM hθ hθ' (A j) (B j)
      _≤(K*(weightBill M lam j*Real.sqrt EA))*Real.sqrt EB :=
        mul_le_mul (mul_le_mul_of_nonneg_left u (Real.sqrt_nonneg _)) v
          (Real.sqrt_nonneg _) (by dsimp [K]; positivity)
      _=_ := by ring
  exact H.norm_le_of_bounded ((weightBill_sum M lam).mul_right (K*Real.sqrt EA*Real.sqrt EB)) Fbound

def offset {c : ℕ} [NeZero c] (r : ℕ×ZMod c) := r.1*c+r.2.val
def cells (M c : ℕ) [NeZero c] : Finset (ℕ×ZMod c) :=
  range (blockCount M c) ×ˢ univ
def padded (M c : ℕ) [NeZero c] (a : ℕ → ℂ) (s : ℕ) (h : ZMod c) : ℂ :=
  if offset (s,h)≤M then a (M+offset (s,h)) else 0

private theorem reblock {V : Type*} [AddCommMonoid V] (M c : ℕ) [NeZero c] (f : ℕ → V) :
    (∑ r∈cells M c,if offset r≤M then f (offset r) else 0)=∑ i∈range (M+1),f i := by
  classical
  rw [←sum_filter]
  let back := fun i : ℕ => (i/c,((i%c):ZMod c))
  have hc := NeZero.pos c
  have e (i : ℕ) : offset (back i)=i := by
    dsimp [offset,back]
    rw [ZMod.val_natCast_of_lt (Nat.mod_lt i hc),Nat.mul_comm]
    exact Nat.div_add_mod i c
  apply sum_bij' (fun r _ => offset r) (fun i _ => back i)
  · intro r hr;exact mem_range.mpr (by have := (mem_filter.mp hr).2;omega)
  · intro i hi
    have hI := mem_range.mp hi
    apply mem_filter.mpr
    constructor
    · apply mem_product.mpr
      constructor
      · apply mem_range.mpr
        dsimp only [back,blockCount]
        have := Nat.div_le_div_right (c:=c) (show i≤M by omega)
        omega
      · exact mem_univ _
    · rw [e];omega
  · rintro ⟨s,h⟩ hr
    have hv := ZMod.val_lt h
    have off : offset (s,h)=h.val+c*s := by dsimp [offset];ring
    apply Prod.ext
    · dsimp only [back]
      rw [off,Nat.add_mul_div_left _ _ hc,Nat.div_eq_of_lt hv,zero_add]
    · dsimp only [back]
      rw [off,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hv,ZMod.natCast_zmod_val]
  · intro i hi;exact e i
  · intro r hr;rfl

def twistedForm (M c : ℕ) (lam θ : ℝ) (a b : ℕ → ℂ) : ℂ :=
  ∑ i∈range (M+1),∑ k∈range (M+1),
    (a (M+i)*b (M+k)*kloosterman c (M+i:ℕ) (M+k:ℕ))*
      fullFactor lam θ c (Real.sqrt (M+i:ℕ)) (Real.sqrt (M+k:ℕ))

/-- Fixed-modulus oscillatory estimate on M ≤ m,n ≤ 2M with the two
arbitrary complex coefficients in their original physical indices. -/
theorem twisted_form_bound {M c : ℕ} [NeZero c] (hcM : c≤M) {lam θ : ℝ}
    (hlam : 0≤lam) (hθ : 0<θ) (hθ' : θ≤2) (a b : ℕ → ℂ) :
    ‖twistedForm M c lam θ a b‖≤Real.exp (4*Real.pi)*
      (Real.sqrt ((c:ℝ)*budget M θ)*
        Real.sqrt (∑ i∈range (M+1),‖a (M+i)‖^2)*
        Real.sqrt (∑ i∈range (M+1),‖b (M+i)‖^2)) := by
  have modEq (s : ℕ) (h : ZMod c) : mode M c s h.val=M+offset (s,h) := by
    dsimp [mode,offset];omega
  have hp (s : ℕ) (h : ZMod c) (H : 2*M<mode M c s h.val) : padded M c a s h=0 := by
    rw [modEq] at H
    exact if_neg (by omega)
  have Ea : (∑ s∈range (blockCount M c),∑ h : ZMod c,‖padded M c a s h‖^2)=
      ∑ i∈range (M+1),‖a (M+i)‖^2 := by
    rw [←reblock M c (fun i => ‖a (M+i)‖^2)]
    simp only [cells,sum_product,padded]
    apply sum_congr rfl
    intro s hs
    apply sum_congr rfl
    intro h hh
    split_ifs <;>simp
  let f := fun i : ℕ => ∑ k∈range (M+1),
    (a (M+i)*b (M+k)*kloosterman c (M+i:ℕ) (M+k:ℕ))*
      fullFactor lam θ c (Real.sqrt (M+i:ℕ)) (Real.sqrt (M+k:ℕ))
  have E : blockForm M c lam θ (padded M c a) (fun i => b (M+i))=twistedForm M c lam θ a b := by
    change _=∑ i∈range (M+1),f i
    rw [←reblock M c f]
    simp only [blockForm,cells,sum_product,modEq,padded]
    apply sum_congr rfl
    intro s hs
    apply sum_congr rfl
    intro h hh
    split_ifs <;>simp [f]
  have H := block_form_bound hcM hlam hθ hθ' (padded M c a) (fun i => b (M+i)) hp
  rwa [E,Ea] at H

end ImbalancedChen.Part3.OriginalTwistedKloosterman20261113
end
