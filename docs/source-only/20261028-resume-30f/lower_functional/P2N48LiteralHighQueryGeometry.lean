import ImbalancedChen.P2N48OriginalStrictLogMassAndOmegaPorts

/-! SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
Pure original n48 integer endpoint geometry. No Omega arrays, query value,
finite guard or row checker is assumed or evaluated. This independent
constructor/range file is intended for the F Omega scan supplier.
-/
namespace ImbalancedChen.P2N48LiteralHighQueryGeometry
noncomputable section
open P2N48SavedParentRowRecost P2N48TiedParentMassReduction
open P2N48OriginalStrictLogMassAndOmegaPorts

private theorem source_endpoint_bounds (r : SourceRow) (ht : r.term.val=1) :
    36480≤leftEnd r 0 ∧ rightEnd r 0≤56640 ∧
      20016≤leftEnd r 1 ∧ rightEnd r 1≤36480 ∧
      20016≤leftEnd r 2 ∧ rightEnd r 2≤36480 ∧
      20016≤leftEnd r 3 ∧ rightEnd r 3≤36480 := by
  have hx : r.ix.val≤47 := by omega
  have hy : r.iy.val≤47 := by omega
  have hz : r.iz.val≤47 := by omega
  have hw : r.iw.val≤47 := by omega
  simp [leftEnd,rightEnd,width,highLo,lowLo,ht] <;> omega

theorem rawQueryLower_original_integer_formula (r : SourceRow) :
    rawQueryLower r=((240000 : ℚ)-
      (rightEnd r 0+rightEnd r 1+rightEnd r 2+rightEnd r 3 : ℕ))/(rightEnd r 2 : ℚ) := by
  unfold rawQueryLower upperQ
  push_cast
  field_simp [show (rightEnd r 2 : ℚ)≠0 by exact_mod_cast (rightEnd_pos r 2).ne'] <;> ring

theorem rawQueryUpper_original_integer_formula (r : SourceRow) :
    rawQueryUpper r=((240000 : ℚ)-
      (leftEnd r 0+leftEnd r 1+leftEnd r 2+leftEnd r 3 : ℕ))/(leftEnd r 2 : ℚ) := by
  unfold rawQueryUpper lowerQ
  push_cast
  have hL : (leftEnd r 2 : ℚ)≠0 := by
    have hpos : 0<leftEnd r 2 := by simp [leftEnd,lowLo]; omega
    exact_mod_cast hpos.ne'
  field_simp [hL] <;> ring

/-- Literal raw queries (not favorable clipped replacements) lie in [2,8]
for every original high-band n48 box, including ALL tied patterns. -/
theorem high_row_raw_query_range (r : SourceRow) (ht : r.term.val=1) :
    (2 : ℚ)≤rawQueryLower r ∧ rawQueryLower r≤rawQueryUpper r ∧ rawQueryUpper r≤8 := by
  obtain ⟨hl0,hr0,hl1,hr1,hl2,hr2,hl3,hr3⟩ := source_endpoint_bounds r ht
  have hR : (0 : ℚ)<(rightEnd r 2 : ℚ) := by exact_mod_cast rightEnd_pos r 2
  have hL : (0 : ℚ)<(leftEnd r 2 : ℚ) := by exact_mod_cast (show 0<leftEnd r 2 by omega)
  have hLR (j : Fin 4) : leftEnd r j≤rightEnd r j := by unfold rightEnd; omega
  have hDen : (leftEnd r 2 : ℚ)≤(rightEnd r 2 : ℚ) := by exact_mod_cast hLR 2
  have hsumR : rightEnd r 0+rightEnd r 1+3*rightEnd r 2+rightEnd r 3≤240000 := by omega
  have hsumL : 240000≤leftEnd r 0+leftEnd r 1+9*leftEnd r 2+leftEnd r 3 := by omega
  have hsumLR : leftEnd r 0+leftEnd r 1+leftEnd r 2+leftEnd r 3≤
      rightEnd r 0+rightEnd r 1+rightEnd r 2+rightEnd r 3 :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (hLR 0) (hLR 1)) (hLR 2)) (hLR 3)
  rw [rawQueryLower_original_integer_formula,rawQueryUpper_original_integer_formula]
  have hA : 2*(rightEnd r 2 : ℚ)≤240000-
      (rightEnd r 0+rightEnd r 1+rightEnd r 2+rightEnd r 3 : ℕ) := by
    have h : (rightEnd r 0 : ℚ)+rightEnd r 1+3*rightEnd r 2+rightEnd r 3≤240000 := by exact_mod_cast hsumR
    push_cast
    linarith
  have hAB : (240000 : ℚ)-(rightEnd r 0+rightEnd r 1+rightEnd r 2+rightEnd r 3 : ℕ)≤
      240000-(leftEnd r 0+leftEnd r 1+leftEnd r 2+leftEnd r 3 : ℕ) := by
    have h : ((leftEnd r 0+leftEnd r 1+leftEnd r 2+leftEnd r 3 : ℕ) : ℚ)≤
        ((rightEnd r 0+rightEnd r 1+rightEnd r 2+rightEnd r 3 : ℕ) : ℚ) := by exact_mod_cast hsumLR
    linarith
  have hB : (0 : ℚ)≤240000-(leftEnd r 0+leftEnd r 1+leftEnd r 2+leftEnd r 3 : ℕ) := by
    have hp : (0 : ℚ)≤2*(rightEnd r 2 : ℚ) := by positivity
    exact hp.trans (hA.trans hAB)
  refine ⟨(le_div_iff₀ hR).2 hA,?_,?_⟩
  · exact (div_le_div_of_nonneg_right hAB hR.le).trans
      (div_le_div_of_nonneg_left hB hL hDen)
  · apply (div_le_iff₀ hL).2
    have h : (240000 : ℚ)≤(leftEnd r 0 : ℚ)+leftEnd r 1+9*leftEnd r 2+leftEnd r 3 := by exact_mod_cast hsumL
    push_cast
    linarith

end
end ImbalancedChen.P2N48LiteralHighQueryGeometry
