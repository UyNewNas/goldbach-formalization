import ImbalancedChen.Part3ActualOriginalSpectralScales
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual occupied source scales satisfy the original D0/D1/D2 power
gaps with explicit absolute dyadic constants. This uses the original
four MediumAdmissible monomials, not a desired bare/spectral estimate.
No fixed positive x^epsilon is relabelled as a vanishing subpower.
-/

namespace ImbalancedChen.Part3.ActualSpectralMonomialMargins20261028
noncomputable section
open Classical Finset
open ActualOriginalSpectralScales20261028 MediumGlobalDyadicOwnership20261028

private theorem divide_original_monomial {x u t : ℝ} (hx : 0 < x) (m : ℕ)
    (h : u < x^((m : ℝ)-t)) : u/x^m < x^(-t) := by
  calc
    _ < x^((m : ℝ)-t)/x^m := div_lt_div_of_pos_right h (pow_pos hx m)
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_sub hx]
      congr 1
      ring

private theorem two_rough_power_cost {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) :
    (2*R)^(2+2*theta)*(2*S)^(5-2*theta) =
      128*(R^(2+2*theta)*S^(5-2*theta)) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hS]
  calc
    _ = (2 : ℝ)^(2+2*theta)*(2 : ℝ)^(5-2*theta)*
        (R^(2+2*theta)*S^(5-2*theta)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        show (2+2*theta)+(5-2*theta) = (7 : ℝ) by ring]
      norm_num

/-- The true actual rough owner is dominated by the original source
lengths with only constants 8,128,128. The source q remains Q1. -/
theorem actual_D0_D1_D2_margins {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (z y : ℝ) (k : Key) (hk : k ∈ keyBank atom z y) :
    D0 atom k < 8*atom.scale^(-8*sigma) ∧
      D1 atom k < 128*atom.scale^(-15*sigma) ∧
      D2 atom k < 128*atom.scale^(-15*sigma) := by
  obtain ⟨hN,hM,hQ,hS,hR,hx,haLo,haHi,hQN,hgeom,hfirst,hsecond,hrest⟩ := hA
  have hN0 : 0 ≤ atom.U := zero_le_one.trans hN
  have hQ0 : 0 ≤ atom.Q1 := zero_le_one.trans hQ
  have hR0 : 0 ≤ atom.Q3 := zero_le_one.trans hR
  have hS0 : 0 ≤ atom.Q2 := zero_le_one.trans hS
  have hx0 : 0 < atom.scale := by change 0 < atom.U*atom.V; positivity
  obtain ⟨hr,hs,hw⟩ := actual_rough_owner_geometry hA z y k hk
  have hr0 : 0 ≤ roughR k := zero_le_one.trans (rough_scales_one_le k).1
  have hs0 : 0 ≤ roughS k := zero_le_one.trans (rough_scales_one_le k).2
  have hr2 := pow_le_pow_left₀ hr0 hr 2
  have hs5 := pow_le_pow_left₀ hs0 hs 5
  have hnum0 : atom.U^2*(roughR k)^2*roughS k ≤
      8*(atom.U^2*atom.Q2*atom.Q3^2) := by
    calc
      _ ≤ atom.U^2*(2*atom.Q3)^2*(2*atom.Q2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr2 (sq_nonneg _)) hs hs0 (by positivity)
      _ = _ := by ring
  have hnum1 : (atom.residue.natAbs : ℝ)^theta*atom.U*atom.Q1*
      (roughR k)^2*(roughS k)^5 ≤
      128*((atom.residue.natAbs : ℝ)^theta*atom.U*atom.Q1*atom.Q2^5*atom.Q3^2) := by
    calc
      _ ≤ (atom.residue.natAbs : ℝ)^theta*atom.U*atom.Q1*
          (2*atom.Q3)^2*(2*atom.Q2)^5 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr2 (by positivity)) hs5
          (pow_nonneg hs0 5) (by positivity)
      _ = _ := by ring
  have hrp := Real.rpow_le_rpow hr0 hr (by norm_num [theta] : 0 ≤ 2+2*theta)
  have hsp := Real.rpow_le_rpow hs0 hs (by norm_num [theta] : 0 ≤ 5-2*theta)
  have hnum2 : atom.U^(1+2*theta)*atom.Q1*(roughR k)^(2+2*theta)*
      (roughS k)^(5-2*theta) ≤
      128*(atom.U^(1+2*theta)*atom.Q1*atom.Q2^(5-2*theta)*atom.Q3^(2+2*theta)) := by
    calc
      _ = (atom.U^(1+2*theta)*atom.Q1)*
          ((roughR k)^(2+2*theta)*(roughS k)^(5-2*theta)) := by ring
      _ ≤ (atom.U^(1+2*theta)*atom.Q1)*
          ((2*atom.Q3)^(2+2*theta)*(2*atom.Q2)^(5-2*theta)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hrp hsp (Real.rpow_nonneg hs0 _) (by positivity)) (by positivity)
      _ = _ := by rw [two_rough_power_cost hR0 hS0]; ring
  have hg0 := divide_original_monomial hx0 1 hgeom
  have hg1 := divide_original_monomial hx0 2 (by simpa only [theta] using hfirst)
  have hg2 := divide_original_monomial hx0 2 (by simpa only [theta] using hsecond)
  refine ⟨?_,?_,?_⟩
  · calc
      D0 atom k ≤ 8*(atom.U^2*atom.Q2*atom.Q3^2/atom.scale) := by
        unfold D0
        convert div_le_div_of_nonneg_right hnum0 hx0.le using 1 <;> ring
      _ < _ := by simpa only [pow_one] using mul_lt_mul_of_pos_left hg0 (by norm_num : (0 : ℝ) < 8)
  · calc
      D1 atom k ≤ 128*((atom.residue.natAbs : ℝ)^theta*atom.U*atom.Q1*
          atom.Q2^5*atom.Q3^2/atom.scale^2) := by
        unfold D1
        convert div_le_div_of_nonneg_right hnum1 (sq_nonneg atom.scale) using 1 <;> ring
      _ < _ := mul_lt_mul_of_pos_left hg1 (by norm_num)
  · calc
      D2 atom k ≤ 128*(atom.U^(1+2*theta)*atom.Q1*atom.Q2^(5-2*theta)*
          atom.Q3^(2+2*theta)/atom.scale^2) := by
        unfold D2
        convert div_le_div_of_nonneg_right hnum2 (sq_nonneg atom.scale) using 1 <;> ring
      _ < _ := mul_lt_mul_of_pos_left hg2 (by norm_num)

/-- The original Bspec^2<x gate has the same strict power gap;
the harmless factor4 is displayed for a later uniform threshold. -/
theorem actual_spectralB_sq_margin {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (z y : ℝ) (k : Key) (hk : k ∈ keyBank atom z y) :
    (spectralB atom k)^2 < 4*atom.scale^(1-8*sigma) := by
  obtain ⟨hN,hM,hQ,hS,hR,hx,haLo,haHi,hQN,hgeom,hrest⟩ := hA
  have hr := (actual_rough_owner_geometry hA z y k hk).1
  have hr0 : 0 ≤ roughR k := zero_le_one.trans (rough_scales_one_le k).1
  have hbase : atom.U^2*atom.Q3^2 ≤ atom.U^2*atom.Q2*atom.Q3^2 := by
    have h := mul_le_mul_of_nonneg_left hS (show 0 ≤ atom.U^2*atom.Q3^2 by positivity)
    convert h using 1 <;> ring
  calc
    _ ≤ atom.U^2*(2*atom.Q3)^2 := by
      unfold spectralB
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg _)
    _ = 4*(atom.U^2*atom.Q3^2) := by ring
    _ ≤ 4*(atom.U^2*atom.Q2*atom.Q3^2) := mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ < _ := mul_lt_mul_of_pos_left hgeom (by norm_num)

end
end ImbalancedChen.Part3.ActualSpectralMonomialMargins20261028
