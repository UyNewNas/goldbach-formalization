import ImbalancedChen.P4ASymmetricNewOnlyLeaf
import ImbalancedChen.ActualThirdOriginalP4ABalancedSymmetricLeaf

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
Proposed installation: ImbalancedChen.P4ASymmetricNewOnlySameReader.

Minimal either-mu-side SAME-reader completion of the actual symmetric
NEW-only branch. The prior actual NEW-only analytic theorem has no mu
hypothesis. Here the general ratio log and mass suppliers replace the
above-mu log/mass suppliers; actual NEW query soundness is supplied from
the SAME table reader and the literal storedGridNew.hi/P160 operand.

No OLD query/chord/mean, hquery, final leaf integral or K bound is assumed.
The original mean_upper high<=2 early return is exactly its NEW `out`.
The finite dispatcher may apply this theorem when that return is selected;
the bound actually holds independently of the selected OLD high value.
Factor4 and the ONE original mass /2 remain inside literalSymmetricMass,
followed by literalSymmetricUpper's original final UP.
-/

namespace ImbalancedChen.P4ASymmetricNewOnlyLeafSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites OriginalThirdP4ABalancedSymmetricLeaf

/-- The exact finite-dispatch ABI. The log ratio and positive lower endpoint
are the original integer/interval guards; the NEW query is proved internally
using table.blocks, so caller-supplied values cannot select a second reader. -/
theorem original_same_reader_symmetric_new_only_integer_upper
    (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hratio : x1 ≤ 2*x0)
    (hpositive : 0 < (originalLnUnit ((x1:ℝ)/(x0:ℝ))).lo) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ), compactKernel t) ≤
      value (literalSymmetricUpper x0 x1 z0 z1
        (readQueryHi160 (assembledRead table.blocks)
          (storedGridNew x0 x1 z0 z1).hi P160)) := by
  have hx0 := positive_grid_binding x0 a ha (symmetric_positive hg).1
  have hx0R : (0:ℝ) < (x0:ℝ) := by exact_mod_cast hx0
  have haR : (a:ℝ)=(x0:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [ha]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hbR : (b:ℝ)=(x1:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hb]
    simp only [Rat.cast_div, Rat.cast_intCast]
  have hratioEq : (b:ℝ)/(a:ℝ)=(x1:ℝ)/(x0:ℝ) := by
    rw [haR, hbR]
    exact producer_log_ratio _ _ _ (by norm_num) hx0R.ne'
  have hratioRaw : (x1:ℝ)/(x0:ℝ) ≤ 2 :=
    (div_le_iff₀ hx0R).mpr (by exact_mod_cast hratio)
  have hratioPhysical : (b:ℝ)/(a:ℝ) ≤ 2 := by
    simpa only [hratioEq] using hratioRaw
  have hpositivePhysical : 0 < (originalLnUnit ((b:ℝ)/(a:ℝ))).lo := by
    simpa only [hratioEq] using hpositive
  have hlog := original_positive256_ln_sound
    ((le_div_iff₀ (symmetric_positive hg).1).mpr (by linarith [hg.width_xy]))
    hratioPhysical
  have hquery := symmetric_saved_tent_new_query table x0 x1 z0 z1 a b c d
    ha hb hc hd hg
  let out := readQueryHi160 (assembledRead table.blocks)
    (storedGridNew x0 x1 z0 z1).hi P160
  have hout : actualExtendedThirdLowerFactor
      (newMean (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) ≤ value out :=
    actual_new_factor_upper_of_original_query hlog hpositivePhysical hquery
  have hout0 : 0 ≤ value out := (actualExtendedThirdLowerFactor_nonneg _).trans hout
  have hmass := (literal_symmetric_mass_encloses_ratio x0 x1 z0 z1 a b c d
    ha hb hc hd hg hratioPhysical).2
  calc
    _ ≤ prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)*value out :=
      original_symmetric_new_only_leaf_upper hg hout
    _ ≤ value (literalSymmetricMass x0 x1 z0 z1).hi*value out :=
      mul_le_mul_of_nonneg_right hmass hout0
    _ = value out*value (literalSymmetricMass x0 x1 z0 z1).hi := by ring
    _ ≤ value (literalSymmetricUpper x0 x1 z0 z1 out) := literal_product_UP_ge _ _

/-- Compatibility spelling agreed with the below-mu finite-dispatch author.
The proposition and every argument are identical to the primary ABI above. -/
theorem original_stored_symmetric_new_only_same_reader_integer_upper_general
    (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hratio : x1 ≤ 2*x0)
    (hpositive : 0 < (originalLnUnit ((x1:ℝ)/(x0:ℝ))).lo) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ), compactKernel t) ≤
      value (literalSymmetricUpper x0 x1 z0 z1
        (readQueryHi160 (assembledRead table.blocks)
          (storedGridNew x0 x1 z0 z1).hi P160)) := by
  exact original_same_reader_symmetric_new_only_integer_upper table x0 x1 z0 z1
    a b c d ha hb hc hd hg hratio hpositive

end
end ImbalancedChen.P4ASymmetricNewOnlyLeafSourceOnly
