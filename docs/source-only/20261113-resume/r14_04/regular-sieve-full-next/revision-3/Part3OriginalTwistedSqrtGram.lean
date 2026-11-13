import ImbalancedChen.Part3OriginalTwistedSqrtIncrements
import ImbalancedChen.Part3IntervalHarmonicPairBound

/-! The full interval Gram matrix in the n variable of the original
square-root twist. Every additive residue and every contiguous c-block
occurs. The bounds do not require prime c. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalTwistedSqrtGram20261113
open Set Complex Finset
open OAI.Problem337.ExponentialSum (phase phase_neg phase_add phase_norm)
open OriginalTwistedSqrtIncrements20261113

def anchor (M c s : ℕ) : ℝ := (M+s*c:ℕ)

def rowAngle (M c : ℕ) (θ : ℝ) (s j i : ℕ) : ℝ :=
  (j:ℝ)/c*(M+i:ℕ)+2*θ/c*Real.sqrt (anchor M c s)*Real.sqrt (M+i:ℕ)

def gram (M c : ℕ) (θ : ℝ) (s j t k : ℕ) : ℂ :=
  ∑ i∈range (M+1),phase (rowAngle M c θ s j i-rowAngle M c θ t k i)

theorem gram_eq_products (M c : ℕ) (θ : ℝ) (s j t k : ℕ) :
    gram M c θ s j t k =
      ∑ i∈range (M+1),phase (rowAngle M c θ s j i)*star (phase (rowAngle M c θ t k i)) := by
  apply sum_congr rfl
  intro i hi
  rw [sub_eq_add_neg,phase_add,phase_neg]

theorem gram_symm (M c : ℕ) (θ : ℝ) (s j t k : ℕ) :
    ‖gram M c θ s j t k‖=‖gram M c θ t k s j‖ := by
  have E : gram M c θ t k s j=star (gram M c θ s j t k) := by
    simp only [gram,star_sum]
    apply sum_congr rfl
    intro i hi
    rw [show rowAngle M c θ t k i-rowAngle M c θ s j i =
      -(rowAngle M c θ s j i-rowAngle M c θ t k i) by ring,phase_neg]
  rw [E,norm_star]

private theorem gram_eq_kernel (M c : ℕ) (θ : ℝ) (s j t k : ℕ) :
    gram M c θ s j t k =
      kernel c θ (anchor M c s) (anchor M c t) ((j:ℝ)-k) M := by
  apply sum_congr rfl
  intro i hi
  congr 1
  unfold rowAngle angle
  ring

theorem gram_diag (M c : ℕ) (θ : ℝ) (s j : ℕ) :
    ‖gram M c θ s j s j‖=(M:ℝ)+1 := by
  simp [gram,phase]

private theorem anchor_mem {M c s : ℕ} (hs : s*c≤M) :
    anchor M c s∈Icc (M:ℝ) (2*M) := by
  unfold anchor
  constructor
  · exact_mod_cast (show M≤M+s*c by omega)
  · exact_mod_cast (show M+s*c≤2*M by omega)

private def invNat (x : ℕ) : ℝ := (x:ℝ)⁻¹

private theorem inv_nonneg_nat (x : ℕ) : 0≤invNat x := by unfold invNat; positivity

def charge (f : ℕ → ℝ) (j k : ℕ) : ℝ :=
  if k<j then f (j-k) else if j<k then f (k-j) else 0

private theorem charge_symm (f : ℕ → ℝ) (j k : ℕ) : charge f j k=charge f k j := by
  rcases lt_trichotomy k j with h|h|h
  · simp [charge,h,h.asymm]
  · simp [h]
  · simp [charge,h,h.asymm]

def residueCharge (c j k : ℕ) : ℝ :=
  charge (fun v => invNat v+invNat (c-v)) j k

def blockCharge (s t : ℕ) : ℝ := charge invNat s t

private theorem gram_residue_ordered {M c j k s t : ℕ} (hM : 0<M) (hc : 0<c)
    {θ : ℝ} (hθ : θ∈Icc 0 2) (hs : s*c≤M) (ht : t*c≤M) (hkj : k<j) (hj : j<c) :
    ‖gram M c θ s j t k‖≤12*c*residueCharge c j k := by
  have dpos : 0<(j-k:ℕ) := by omega
  have epos : 0<(c-(j-k):ℕ) := by omega
  have castD : ((j-k:ℕ):ℝ)=(j:ℝ)-k := Nat.cast_sub hkj.le
  have castE : ((c-(j-k):ℕ):ℝ)=(c:ℝ)-(j-k:ℕ) := Nat.cast_sub (by omega)
  rw [gram_eq_kernel,←castD]
  have H := kernel_residue hM (by exact_mod_cast hc : 0<(c:ℝ)) hθ
    (anchor_mem hs) (anchor_mem ht)
    (by exact_mod_cast (show 1≤j-k by omega) : 1≤((j-k:ℕ):ℝ))
    (show 1≤(c:ℝ)-(j-k:ℕ) by rw [←castE];exact_mod_cast (show 1≤c-(j-k) by omega))
  rw [←castE] at H
  rw [residueCharge,charge,if_pos hkj]
  apply H.trans
  set D : ℝ := (j-k:ℕ)
  set E : ℝ := (c-(j-k):ℕ)
  have dp : 0<D := by exact_mod_cast dpos
  have ep : 0<E := by exact_mod_cast epos
  change 12*(c:ℝ)/min D E≤12*c*(D⁻¹+E⁻¹)
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases le_total D E with h|h
  · rw [min_eq_left h];exact le_add_of_nonneg_right (inv_nonneg.mpr ep.le)
  · rw [min_eq_right h];exact le_add_of_nonneg_left (inv_nonneg.mpr dp.le)

theorem gram_residue {M c j k s t : ℕ} (hM : 0<M) (hc : 0<c)
    {θ : ℝ} (hθ : θ∈Icc 0 2) (hs : s*c≤M) (ht : t*c≤M)
    (hj : j<c) (hk : k<c) (hne : j≠k) :
    ‖gram M c θ s j t k‖≤12*c*residueCharge c j k := by
  rcases lt_or_gt_of_ne hne with h|h
  · rw [gram_symm]
    unfold residueCharge
    rw [charge_symm _ j k]
    exact gram_residue_ordered hM hc hθ ht hs h hk
  · exact gram_residue_ordered hM hc hθ hs ht h hj

private theorem gram_block_ordered {M c j s t : ℕ} (hM : 0<M) (hc : 0<c)
    {θ : ℝ} (hθ : 0<θ) (hθ' : θ≤2) (hs : s*c≤M) (ht : t*c≤M) (hts : t<s) :
    ‖gram M c θ s j t j‖≤24*M/θ*blockCharge s t := by
  have castD : ((s-t:ℕ):ℝ)=(s:ℝ)-t := Nat.cast_sub hts.le
  have dpos : 0<((s-t:ℕ):ℝ) := by exact_mod_cast (show 0<s-t by omega)
  have sM : s≤M := (calc s=s*1 := (Nat.mul_one _).symm
                          _≤s*c := Nat.mul_le_mul_left s hc).trans hs
  have sep : anchor M c s-anchor M c t=(c:ℝ)*(s-t:ℕ) := by
    rw [castD]
    simp only [anchor,Nat.cast_add,Nat.cast_mul]
    ring
  rw [gram_eq_kernel,sub_self]
  have H := kernel_block hM (by exact_mod_cast (show 1≤c by omega) : 1≤(c:ℝ))
    hθ hθ' (anchor_mem hs) (anchor_mem ht) dpos
    (by exact_mod_cast (show s-t≤M by omega) : ((s-t:ℕ):ℝ)≤M) sep
  apply H.trans_eq
  simp only [blockCharge,charge,if_pos hts,invNat,div_eq_mul_inv,mul_inv_rev]
  ring

theorem gram_block {M c j s t : ℕ} (hM : 0<M) (hc : 0<c)
    {θ : ℝ} (hθ : 0<θ) (hθ' : θ≤2) (hs : s*c≤M) (ht : t*c≤M) (hne : s≠t) :
    ‖gram M c θ s j t j‖≤24*M/θ*blockCharge s t := by
  rcases lt_or_gt_of_ne hne with h|h
  · rw [gram_symm]
    unfold blockCharge
    rw [charge_symm _ s t]
    exact gram_block_ordered hM hc hθ hθ' ht hs h
  · exact gram_block_ordered hM hc hθ hθ' hs ht h

/-- Sum over an injective subfamily, on the pinned host's finite-image API. -/
theorem sum_le_injected {I J : Type*} [DecidableEq J] {S : Finset I} {T : Finset J}
    {f : I → ℝ} {g : J → ℝ} (i : I → J) (hi : Set.InjOn i (S : Set I))
    (inside : S.image i ⊆ T) (each : ∀ a∈S, f a≤g (i a))
    (outside : ∀ b∈T, b∉S.image i → 0≤g b) :
    (∑ a∈S,f a)≤∑ b∈T,g b := by
  calc
    _≤∑ a∈S,g (i a) := sum_le_sum each
    _=∑ b∈S.image i,g b := (sum_image hi).symm
    _≤_ := sum_le_sum_of_subset_of_nonneg inside outside

private theorem charge_sum (f : ℕ → ℝ) (hf : ∀ x, 0≤f x) {N j : ℕ} (hj : j<N) :
    (∑ k∈range N,charge f j k)≤2*∑ d∈Icc 1 (N-1),f d := by
  let A := (range N).filter (fun k => k<j)
  let B := (range N).filter (fun k => j<k)
  have split : (∑ k∈range N,charge f j k)=
      (∑ k∈A,f (j-k))+(∑ k∈B,f (k-j)) := by
    simp only [A,B,sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    by_cases h : k<j
    · simp [charge,h,h.asymm]
    · simp [charge,h]
  have L : (∑ k∈A,f (j-k))≤∑ d∈Icc 1 (N-1),f d := by
    apply sum_le_injected (fun k => j-k)
    · intro x hx y hy h
      have hx' : x<j := (mem_filter.mp hx).2
      have hy' : y<j := (mem_filter.mp hy).2
      dsimp at h
      omega
    · intro d hd
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hd
      have h := (mem_filter.mp hk).2
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    · intro x hx;exact le_rfl
    · intro x hx h;exact hf x
  have R : (∑ k∈B,f (k-j))≤∑ d∈Icc 1 (N-1),f d := by
    apply sum_le_injected (fun k => k-j)
    · intro x hx y hy h
      have hx' : j<x := (mem_filter.mp hx).2
      have hy' : j<y := (mem_filter.mp hy).2
      dsimp at h
      omega
    · intro d hd
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hd
      have h := (mem_filter.mp hk).2
      have h' := mem_range.mp (mem_filter.mp hk).1
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    · intro x hx;exact le_rfl
    · intro x hx h;exact hf x
  rw [split]
  linarith only [L,R]

theorem residueCharge_sum {c j : ℕ} (hj : j<c) :
    (∑ k∈range c,residueCharge c j k)≤4*(1+Real.log c) := by
  have H := charge_sum (fun d => invNat d+invNat (c-d))
    (fun d => add_nonneg (inv_nonneg_nat _) (inv_nonneg_nat _)) hj
  simp only [sum_add_distrib,invNat,←one_div,
    IntervalHarmonicPairBoundSourceOnly.reciprocal_reflection_sum] at H
  change (∑ k∈range c,charge (fun d => invNat d+invNat (c-d)) j k)≤_
  convert H.trans (show 2*((∑ d∈Icc 1 (c-1),(1:ℝ)/d)+∑ d∈Icc 1 (c-1),(1:ℝ)/d)
    ≤4*(1+Real.log c) by
      linarith only [IntervalHarmonicPairBoundSourceOnly.reciprocal_sum_le_one_add_log c]) using 1

theorem blockCharge_sum {M N s : ℕ} (hs : s<N) (hN : N-1≤M) :
    (∑ t∈range N,blockCharge s t)≤2*(1+Real.log M) := by
  have H := charge_sum invNat inv_nonneg_nat hs
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _≤∑ d∈Icc 1 M,invNat d := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans hN⟩
      · intro d hd h;exact inv_nonneg_nat d
    _=(harmonic M:ℝ) := by
      simpa only [invNat,one_div] using IntervalHarmonicPairBoundSourceOnly.real_reciprocal_sum_eq_harmonic M
    _≤_ := harmonic_le_one_add_log M

def blockCount (M c : ℕ) := M/c+1

private theorem block_inside {M c s : ℕ} (hc : 0<c) (hs : s<blockCount M c) : s*c≤M :=
  (Nat.le_div_iff_mul_le hc).mp (show s≤M/c by unfold blockCount at hs;omega)

/-- The actual complete modulus-by-block row sum. Its sole logarithm
depends on the coefficient length. -/
theorem gram_row_sum {M c s j : ℕ} (hc : 0<c) (hcM : c≤M) {θ : ℝ}
    (hθ : 0<θ) (hθ' : θ≤2) (hs : s<blockCount M c) (hj : j<c) :
    (∑ t∈range (blockCount M c),∑ k∈range c,‖gram M c θ s j t k‖)≤
      244*M*(1+Real.log M)/θ := by
  let P := blockCount M c
  let l := 1+Real.log (M:ℝ)
  have hM := hc.trans_le hcM
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have cp : 0<(c:ℝ) := by exact_mod_cast hc
  have M1 : 1≤(M:ℝ) := by exact_mod_cast (show 1≤M by omega)
  have l1 : 1≤l := by dsimp [l]; linarith only [Real.log_nonneg M1]
  have l0 : 0≤l := by linarith
  have hs' := block_inside hc hs
  have Pbound : (P:ℝ)*c≤2*M := by
    have h := Nat.div_mul_le_self M c
    have h' : P*c≤2*M := by dsimp [P,blockCount];rw [Nat.add_mul,one_mul];omega
    exact_mod_cast h'
  have hlog : 1+Real.log (c:ℝ)≤l := add_le_add_right (Real.log_le_log cp (by exact_mod_cast hcM)) 1
  have one (t : ℕ) (ht : t<P) :
      (∑ k∈range c,‖gram M c θ s j t k‖) ≤
      (if t=s then (M:ℝ)+1 else 0)+24*M/θ*blockCharge s t+48*c*l := by
    have diag : ‖gram M c θ s j t j‖≤
        (if t=s then (M:ℝ)+1 else 0)+24*M/θ*blockCharge s t := by
      by_cases h : t=s
      · subst t; simp [gram_diag,blockCharge,charge]
      · simpa only [if_neg h,zero_add] using
          (gram_block (j:=j) hM hc hθ hθ' hs' (block_inside hc ht) (Ne.symm h))
    have off :
        (∑ k∈(range c).erase j,‖gram M c θ s j t k‖)≤48*c*l := by
      calc
        _≤∑ k∈(range c).erase j,12*c*residueCharge c j k := by
          apply sum_le_sum
          intro k hk
          exact gram_residue hM hc ⟨hθ.le,hθ'⟩ hs' (block_inside hc ht) hj
            (mem_range.mp (mem_erase.mp hk).2) (Ne.symm (mem_erase.mp hk).1)
        _≤∑ k∈range c,12*c*residueCharge c j k := by
          apply sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
          intro k hk h
          have eq : k=j := by simpa only [mem_erase,hk,and_true,not_not] using h
          simp [eq,residueCharge,charge]
        _=12*c*∑ k∈range c,residueCharge c j k := (mul_sum ..).symm
        _≤12*c*(4*(1+Real.log c)) :=
          mul_le_mul_of_nonneg_left (residueCharge_sum hj) (by positivity)
        _≤48*c*l := by
          have := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤48*c by positivity)
          linarith only [this]
    rw [←sum_erase_add (range c) _ (mem_range.mpr hj)]
    linarith only [off,diag]
  have G0 := sum_le_sum (s:=range P) (fun t ht => one t (mem_range.mp ht))
  have G : (∑ t∈range P,∑ k∈range c,‖gram M c θ s j t k‖)≤
      ((M:ℝ)+1)+(24*M/θ)*(∑ t∈range P,blockCharge s t)+(P:ℝ)*(48*c*l) := by
    apply G0.trans_eq
    rw [sum_add_distrib,sum_add_distrib,←mul_sum]
    simp [sum_ite_eq',hs,P]
  have Q := blockCharge_sum (M:=M) hs (by simp [blockCount,Nat.div_le_self])
  have BC := mul_le_mul_of_nonneg_left Q (show 0≤24*(M:ℝ)/θ by positivity)
  have PC := mul_le_mul_of_nonneg_right Pbound l0
  have a : (M:ℝ)+1≤2*M*l := by
    have := mul_le_mul_of_nonneg_left l1 (show 0≤2*(M:ℝ) by positivity)
    linarith
  change _≤244*M*l/θ
  apply (le_div_iff₀ hθ).mpr
  have bound : (∑ t∈range P,∑ k∈range c,‖gram M c θ s j t k‖)≤
      98*M*l+(24*M/θ)*(2*l) := by
    linarith only [G,BC,PC,a]
  have H := mul_le_mul_of_nonneg_right bound hθ.le
  have H' := mul_le_mul_of_nonneg_left hθ' (show 0≤98*(M:ℝ)*l by positivity)
  have E : (98*(M:ℝ)*l+(24*M/θ)*(2*l))*θ=98*M*l*θ+48*M*l := by
    field_simp [hθ.ne'] <;> ring
  rw [E] at H
  linarith only [H,H']

end ImbalancedChen.Part3.OriginalTwistedSqrtGram20261113
end
