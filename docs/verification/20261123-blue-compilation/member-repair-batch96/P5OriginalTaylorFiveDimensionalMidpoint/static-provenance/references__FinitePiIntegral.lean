import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini for finite real coordinate spaces

These identities extract the first, first two, or last coordinates with
Lebesgue measure on every coordinate. Only the original integrand is assumed
integrable; the second extraction uses almost-everywhere integrable slices.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory

/-- The empty real coordinate space has total volume one. -/
theorem integral_fin_zero (f : (Fin 0 → ℝ) → ℝ) :
    (∫ v, f v) = f Fin.elim0 := by
  rw [Measure.volume_pi_eq_dirac (Fin.elim0 : Fin 0 → ℝ), integral_dirac]

/-- Extract the first coordinate of an integrable finite-dimensional function. -/
theorem integral_fin_succ {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : Integrable f) :
    (∫ x, f x) = ∫ a : ℝ, ∫ v : Fin n → ℝ, f (Fin.cons a v) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove _ 0
  have hg : Integrable (fun z : ℝ × (Fin n → ℝ) => f (e.symm z)) :=
    he.symm.integrable_comp_of_integrable hf
  calc
    (∫ x, f x) = ∫ z : ℝ × (Fin n → ℝ), f (e.symm z) :=
      (he.symm.integral_comp' f).symm
    _ = ∫ a : ℝ, ∫ v : Fin n → ℝ, f (e.symm (a, v)) := integral_prod _ hg
    _ = _ := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

/-- Extract two initial coordinates, applying the second Fubini identity only
on the almost-everywhere set of integrable first-coordinate slices. -/
theorem integral_fin_pair {n : ℕ} (f : (Fin (n + 2) → ℝ) → ℝ)
    (hf : Integrable f) :
    (∫ x, f x) = ∫ a : ℝ, ∫ b : ℝ, ∫ v : Fin n → ℝ,
      f (Fin.cons a (Fin.cons b v)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove _ 0
  have hg : Integrable (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      f (Fin.cons z.1 z.2)) := by
    simpa [Function.comp_def, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv]
      using he.symm.integrable_comp_of_integrable hf
  rw [integral_fin_succ f hf]
  apply integral_congr_ae
  filter_upwards [hg.prod_right_ae] with a ha
  exact integral_fin_succ (fun v => f (Fin.cons a v)) ha

/-- Extract the last coordinate while preserving the order of all preceding
coordinates. -/
theorem integral_fin_last {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : Integrable f) :
    (∫ x, f x) = ∫ q : ℝ, ∫ v : Fin n → ℝ, f (Fin.snoc v q) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove _ (Fin.last n)
  have hg : Integrable (fun z : ℝ × (Fin n → ℝ) => f (e.symm z)) :=
    he.symm.integrable_comp_of_integrable hf
  calc
    (∫ x, f x) = ∫ z : ℝ × (Fin n → ℝ), f (e.symm z) :=
      (he.symm.integral_comp' f).symm
    _ = ∫ q : ℝ, ∫ v : Fin n → ℝ, f (e.symm (q, v)) := integral_prod _ hg
    _ = _ := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

end

end ImbalancedChen
