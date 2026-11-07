import ImbalancedChen.Part3ActualPoincareMaassLocalFinite

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The genuine coordinate upperMaass is complex linear on arbitrary H
functions whose zero extensions are C2 on the positive chart. No finite
tensor restriction, linearity premise, quotient graph assumption or
whole-plane-to-automorphic relabeling is used.
-/

namespace ImbalancedChen.Part3.ActualUpperMaassLinearity20261025a

noncomputable section
open Set
open scoped UpperHalfPlane BigOperators
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.ActualPoincareMaassLocalFinite20261025a

theorem extendUpper_add (F G : UpperHalfPlane → ℂ) :
    extendUpper (F + G) = extendUpper F + extendUpper G := by
  funext p
  by_cases hp : 0 < p.2 <;> simp [extendUpper, hp]

theorem extendUpper_smul (c : ℂ) (F : UpperHalfPlane → ℂ) :
    extendUpper (c • F) = c • extendUpper F := by
  funext p
  by_cases hp : 0 < p.2 <;> simp [extendUpper, hp]

theorem chartMaass_add (F G : ℝ × ℝ → ℂ)
    (hF : ContDiffOn ℝ 2 F positiveChart) (hG : ContDiffOn ℝ 2 G positiveChart)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    chartMaass (F + G) p = chartMaass F p + chartMaass G p := by
  let V : Fin 2 → (ℝ × ℝ → ℂ) := ![F, G]
  have hV : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      ContDiffOn ℝ 2 (V i) positiveChart := by
    intro i _
    fin_cases i
    · exact hF
    · exact hG
  simpa only [V, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.add_apply] using chartMaass_finsetSum Finset.univ V hV hp

/-- Scalar multiplication commutes even with the total derivative
convention, by the actual field-valued constant-multiple derivative rule. -/
theorem chartMaass_smul (c : ℂ) (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    chartMaass (c • F) p = c • chartMaass F p := by
  simp only [chartMaass, Pi.smul_apply, smul_eq_mul,
    deriv_const_mul_field', deriv_const_mul_field]
  ring

theorem upperMaass_add (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart) :
    upperMaass (F + G) = upperMaass F + upperMaass G := by
  funext z
  rw [upperMaass, extendUpper_add]
  exact chartMaass_add (extendUpper F) (extendUpper G) hF hG
    (Complex.measurableEquivRealProd (z : ℂ)) z.im_pos

theorem upperMaass_smul (c : ℂ) (F : UpperHalfPlane → ℂ) :
    upperMaass (c • F) = c • upperMaass F := by
  funext z
  rw [upperMaass, extendUpper_smul]
  exact chartMaass_smul c (extendUpper F) _

theorem upperMaass_zero : upperMaass (0 : UpperHalfPlane → ℂ) = 0 := by
  funext z
  simp [upperMaass, extendUpper, chartMaass]

end
end ImbalancedChen.Part3.ActualUpperMaassLinearity20261025a
