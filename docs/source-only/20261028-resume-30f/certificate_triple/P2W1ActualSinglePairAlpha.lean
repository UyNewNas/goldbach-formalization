import ImbalancedChen.P2EnhancedLowerPrimeChildGeometry

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original alpha is computed from N,Q and the INTEGER old product.
Actual production singleChildren/pairChildren membership gives the
positive logarithmic denominators and the exact original updates.
Q is unchanged and alpha is never reset to 2. This is not a new
source-admission assumption, pair frozen-history supplier or K licence.
-/
namespace ImbalancedChen.P2W1ActualSinglePairAlpha
noncomputable section
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry

def actualAlpha (N : ℕ) (Q : ℝ) (old : List ℕ) : ℝ :=
  (Real.log (N : ℝ)-Real.log (parentProduct old : ℝ))/Real.log (residualLevel Q old)

private theorem ratio_update (a L x : ℝ) (hL : L≠0) (hgap : L-x≠0) :
    (a-x)/(L-x)=1+(a/L-1)/(1-x/L) := by
  have hn : 1-x/L≠0 := by
    intro h
    apply hgap
    have hh := congrArg (fun t : ℝ => t*L) h
    field_simp [hL] at hh
    linarith only [hh]
  field_simp [hL,hgap,hn]
  ring

theorem actual_single_alpha {rule : SingleRule} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : Fin (N+1)}
    (hp : p ∈ singleChildren rule N Q old chi) :
    0<1-relativePrime Q old p.val ∧
    actualAlpha N Q (singleWord old p.val)=
      1+(actualAlpha N Q old-1)/(1-relativePrime Q old p.val) := by
  have h := mem_singleChildren.mp hp
  have hw := h.2.1
  have hR := (parentWindow_logs hw).2.1
  have hL : 0<Real.log (residualLevel Q old) := Real.log_pos hR
  have hpR : (0 : ℝ)<p.val := Nat.cast_pos.mpr h.1.1.pos
  have hBR : (0 : ℝ)<parentProduct old := Nat.cast_pos.mpr hw.2.1
  have hc : 0<Real.log (residualLevel Q old)-Real.log (p.val : ℝ) := by
    have hl := Real.log_pos (single_actual_residual hp).1
    rwa [single_residual_level,Real.log_div (zero_lt_one.trans hR).ne' hpR.ne'] at hl
  have hg : 0<1-relativePrime Q old p.val := by
    have hh := div_pos hc hL
    unfold relativePrime
    convert hh using 1 <;> field_simp [hL.ne'] <;> ring
  refine ⟨hg,?_⟩
  unfold actualAlpha
  rw [single_residual_level,Real.log_div (zero_lt_one.trans hR).ne' hpR.ne']
  have hprod : Real.log (parentProduct (singleWord old p.val) : ℝ)=
      Real.log (parentProduct old : ℝ)+Real.log (p.val : ℝ) := by
    simp only [parentProduct,singleWord,List.prod_append,List.prod_cons,List.prod_nil,
      mul_one,Nat.cast_mul]
    exact Real.log_mul hBR.ne' hpR.ne'
  rw [hprod]
  convert ratio_update (Real.log (N : ℝ)-Real.log (parentProduct old : ℝ))
    (Real.log (residualLevel Q old)) (Real.log (p.val : ℝ)) hL.ne' hc.ne' using 1 <;>
    simp only [relativePrime] <;> ring

theorem actual_pair_alpha {bank : Fin 36} {piece : Fin 4} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : Fin (N+1) × Fin (N+1)}
    (hp : p ∈ pairChildren bank piece N Q old chi) :
    0<1-relativePrime Q old p.1.val-relativePrime Q old p.2.val ∧
    actualAlpha N Q (pairWord old p.1.val p.2.val)=
      1+(actualAlpha N Q old-1)/
        (1-relativePrime Q old p.1.val-relativePrime Q old p.2.val) := by
  have h := mem_pairChildren.mp hp
  have hw := h.2.1
  have hR := (parentWindow_logs hw).2.1
  have hL : 0<Real.log (residualLevel Q old) := Real.log_pos hR
  have hs : (0 : ℝ)<p.1.val := Nat.cast_pos.mpr h.1.1.1.pos
  have hl : (0 : ℝ)<p.2.val := Nat.cast_pos.mpr h.1.2.1.pos
  have hBR : (0 : ℝ)<parentProduct old := Nat.cast_pos.mpr hw.2.1
  have hc : 0<Real.log (residualLevel Q old)-
      (Real.log (p.2.val : ℝ)+Real.log (p.1.val : ℝ)) := by
    have hx := Real.log_pos (pair_actual_residual hp).1
    rwa [pair_residual_level,Real.log_div (zero_lt_one.trans hR).ne' (mul_pos hl hs).ne',
      Real.log_mul hl.ne' hs.ne'] at hx
  have hg : 0<1-relativePrime Q old p.1.val-relativePrime Q old p.2.val := by
    have hh := div_pos hc hL
    unfold relativePrime
    convert hh using 1 <;> field_simp [hL.ne'] <;> ring
  refine ⟨hg,?_⟩
  unfold actualAlpha
  rw [pair_residual_level,Real.log_div (zero_lt_one.trans hR).ne' (mul_pos hl hs).ne',
    Real.log_mul hl.ne' hs.ne']
  have hprod : Real.log (parentProduct (pairWord old p.1.val p.2.val) : ℝ)=
      Real.log (parentProduct old : ℝ)+Real.log (p.2.val : ℝ)+Real.log (p.1.val : ℝ) := by
    simp only [parentProduct,pairWord,List.prod_append,List.prod_cons,List.prod_nil,
      mul_one,Nat.cast_mul]
    rw [Real.log_mul hBR.ne' (mul_pos hl hs).ne',Real.log_mul hl.ne' hs.ne']
    ring
  rw [hprod]
  convert ratio_update (Real.log (N : ℝ)-Real.log (parentProduct old : ℝ))
    (Real.log (residualLevel Q old))
    (Real.log (p.2.val : ℝ)+Real.log (p.1.val : ℝ)) hL.ne' hc.ne' using 1 <;>
    simp only [relativePrime] <;> field_simp [hL.ne'] <;> ring

private theorem updated_alpha_mono {A u : ℝ} (hA : 2≤A) (hu : 0≤u) (hg : 0<1-u) :
    A≤1+(A-1)/(1-u) := by
  have hh : A-1≤(A-1)/(1-u) := by
    apply (le_div_iff₀ hg).mpr
    have hm := mul_nonneg (show 0≤A-1 by linarith) hu
    nlinarith only [hm]
  linarith only [hh]

theorem actual_single_alpha_mono {rule : SingleRule} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : Fin (N+1)} (hp : p ∈ singleChildren rule N Q old chi)
    (ha : 2≤actualAlpha N Q old) :
    actualAlpha N Q old≤actualAlpha N Q (singleWord old p.val) := by
  have h := mem_singleChildren.mp hp
  have hu : 0≤relativePrime Q old p.val := div_nonneg
    (Real.log_nonneg (by exact_mod_cast h.1.1.one_lt.le))
    (Real.log_pos (parentWindow_logs h.2.1).2.1).le
  rw [(actual_single_alpha hp).2]
  exact updated_alpha_mono ha hu (actual_single_alpha hp).1

theorem actual_pair_alpha_mono {bank : Fin 36} {piece : Fin 4} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : Fin (N+1) × Fin (N+1)}
    (hp : p ∈ pairChildren bank piece N Q old chi) (ha : 2≤actualAlpha N Q old) :
    actualAlpha N Q old≤actualAlpha N Q (pairWord old p.1.val p.2.val) := by
  have h := mem_pairChildren.mp hp
  have hs : 0≤relativePrime Q old p.1.val := div_nonneg
    (Real.log_nonneg (by exact_mod_cast h.1.1.1.one_lt.le))
    (Real.log_pos (parentWindow_logs h.2.1).2.1).le
  have hl : 0≤relativePrime Q old p.2.val := div_nonneg
    (Real.log_nonneg (by exact_mod_cast h.1.2.1.one_lt.le))
    (Real.log_pos (parentWindow_logs h.2.1).2.1).le
  rw [(actual_pair_alpha hp).2]
  have hh := updated_alpha_mono ha (add_nonneg hs hl)
    (by linarith only [(actual_pair_alpha hp).1])
  convert hh using 1 <;> congr 1 <;> ring

end
end ImbalancedChen.P2W1ActualSinglePairAlpha
