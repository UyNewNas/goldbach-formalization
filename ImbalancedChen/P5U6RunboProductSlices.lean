import ImbalancedChen.CurrentChenUpsilon6LogDomain
import ImbalancedChen.CurrentChenUpsilon6KernelBuffer
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE_ONLY / UNCOMPILED. Exact integral slicing for the corrected Runbo U6
product restriction. Coordinates retain their arithmetic labels: x 0 = u is
the first prime, x 1 = t is the second prime. The product gate is always
u + t <= 833/2500 - eta, never an individual upper bound substituted for it.

The generic Fubini theorem assumes only ordinary integrability of its kernel;
the reciprocal-mass specialization discharges this from the actual module.
At eta = 0 the exact slicing changes at u = 243/2500. Both endpoint choices
are preserved literally; no arithmetic boundary is declared empty.
This does not supply h248, its arithmetic mean, or the adopted L6 enclosure.
-/

namespace ImbalancedChen.P5U6RunboProductSlicesSourceOnly

noncomputable section

open MeasureTheory Set
open Classical

abbrev Point := Fin 2 → ℝ

/-- Exact vertical section of the original product-restricted domain. -/
def productSlice (eta u : ℝ) : Set ℝ :=
  Ico (19 / 125 : ℝ) (59 / 250) ∩ Iic ((833 / 2500 : ℝ) - eta - u)

theorem measurableSet_productSlice (eta u : ℝ) :
    MeasurableSet (productSlice eta u) :=
  measurableSet_Ico.inter measurableSet_Iic

theorem measurableSet_productDomain (eta : ℝ) :
    MeasurableSet (currentChenUpsilon6LogDomain eta) := by
  exact measurableSet_currentChenUpsilon6LogRectangle.inter
    (isClosed_le ((continuous_apply 0).add (continuous_apply 1))
      continuous_const).measurableSet

/-- The moving slice retains the inclusive product wall and both original
half-open prime bands. This is an exact set identity for every real eta. -/
theorem productDomain_vec_iff (eta u t : ℝ) :
    ![u, t] ∈ currentChenUpsilon6LogDomain eta ↔
      u ∈ Ico (417 / 5000 : ℝ) (19 / 125) ∧ t ∈ productSlice eta u := by
  simp only [currentChenUpsilon6LogDomain, mem_inter_iff,
    mem_currentChenUpsilon6LogRectangle, Matrix.cons_val_zero,
    Matrix.cons_val_one, mem_setOf_eq, productSlice, mem_Ico, mem_Iic]
  constructor
  · rintro ⟨⟨ha, hh, ht, hd⟩, hp⟩
    exact ⟨⟨ha, hh⟩, ⟨⟨ht, hd⟩, by linarith only [hp]⟩⟩
  · rintro ⟨⟨ha, hh⟩, ⟨⟨ht, hd⟩, hp⟩⟩
    exact ⟨⟨ha, hh, ht, hd⟩, by linarith only [hp]⟩

/-- Genuine Fubini for the original corrected domain, applicable to the
future h248 kernel once that kernel's integrability has been proved. -/
theorem integral_productDomain_eq_nested (eta : ℝ) (f : Point → ℝ)
    (hf : IntegrableOn f currentChenUpsilon6LogRectangle) :
    (∫ x in currentChenUpsilon6LogDomain eta, f x) =
      ∫ u in Ico (417 / 5000 : ℝ) (19 / 125),
        ∫ t in productSlice eta u, f ![u, t] := by
  let S := currentChenUpsilon6LogDomain eta
  let F := S.indicator f
  have hS : MeasurableSet S := measurableSet_productDomain eta
  have hF : Integrable F :=
    (hf.mono_set inter_subset_left).integrable_indicator hS
  let E := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinTwo _
  have hPF : Integrable (fun p : ℝ × ℝ => F (E.symm p)) :=
    (hE.symm.integrable_comp_emb E.symm.measurableEmbedding).mpr hF
  have hvec (u t : ℝ) : E.symm (u, t) = ![u, t] := by
    ext i
    fin_cases i <;> rfl
  have hpoint (u t : ℝ) : F ![u, t] =
      (Ico (417 / 5000 : ℝ) (19 / 125)).indicator
        (fun u => (productSlice eta u).indicator (fun t => f ![u, t]) t) u := by
    change S.indicator f ![u, t] = _
    by_cases hu : u ∈ Ico (417 / 5000 : ℝ) (19 / 125)
    · by_cases ht : t ∈ productSlice eta u
      · have hut : ![u, t] ∈ S := (productDomain_vec_iff eta u t).mpr ⟨hu, ht⟩
        rw [indicator_of_mem hut, indicator_of_mem hu, indicator_of_mem ht]
      · have hut : ![u, t] ∉ S := fun h => ht ((productDomain_vec_iff eta u t).mp h).2
        rw [indicator_of_notMem hut, indicator_of_mem hu, indicator_of_notMem ht]
    · have hut : ![u, t] ∉ S := fun h => hu ((productDomain_vec_iff eta u t).mp h).1
      rw [indicator_of_notMem hut, indicator_of_notMem hu]
  calc
    (∫ x in currentChenUpsilon6LogDomain eta, f x) = ∫ x, F x :=
      (integral_indicator hS).symm
    _ = ∫ p : ℝ × ℝ, F (E.symm p) := (hE.symm.integral_comp' F).symm
    _ = ∫ u : ℝ, ∫ t : ℝ, F (E.symm (u, t)) := integral_prod _ hPF
    _ = ∫ u : ℝ, ∫ t : ℝ, F ![u, t] := by simp only [hvec]
    _ = ∫ u : ℝ, (Ico (417 / 5000 : ℝ) (19 / 125)).indicator
        (fun u => ∫ t in productSlice eta u, f ![u, t]) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u ∈ Ico (417 / 5000 : ℝ) (19 / 125)
      · rw [indicator_of_mem hu]
        simp_rw [hpoint, indicator_of_mem hu]
        exact integral_indicator (measurableSet_productSlice eta u)
      · rw [indicator_of_notMem hu]
        simp_rw [hpoint, indicator_of_notMem hu]
        exact integral_zero ℝ ℝ
    _ = _ := integral_indicator measurableSet_Ico

/-- The first exact strip has no active product truncation. The endpoint
u = 243/2500 belongs here; the upper t endpoint remains excluded. -/
theorem productSlice_zero_of_le {u : ℝ} (hu : u ≤ (243 / 2500 : ℝ)) :
    productSlice 0 u = Ico (19 / 125 : ℝ) (59 / 250) := by
  ext t
  constructor
  · exact fun ht => ht.1
  · intro ht
    refine ⟨ht, ?_⟩
    change t ≤ (833 / 2500 : ℝ) - 0 - u
    have ht' := ht.2
    linarith

/-- Past the exact transition, the product wall is the upper endpoint.
It is weak, hence Icc rather than Ico. No null-wall argument is needed. -/
theorem productSlice_zero_of_gt {u : ℝ} (hu : (243 / 2500 : ℝ) < u) :
    productSlice 0 u = Icc (19 / 125 : ℝ) ((833 / 2500 : ℝ) - u) := by
  ext t
  constructor
  · intro ht
    exact ⟨ht.1.1, by simpa only [sub_zero] using ht.2⟩
  · intro ht
    refine ⟨⟨ht.1, ?_⟩, ?_⟩
    · have ht' := ht.2
      linarith
    · simpa only [sub_zero] using ht.2

/-- Exact rectangle/taper decomposition of the corrected Runbo integral.
No permutation factor, Jacobian, or factor 2 is introduced. -/
theorem integral_productDomain_zero_eq_split (f : Point → ℝ)
    (hf : IntegrableOn f currentChenUpsilon6LogRectangle) :
    (∫ x in currentChenUpsilon6LogDomain 0, f x) =
      ∫ u in Ico (417 / 5000 : ℝ) (19 / 125),
        if u ≤ (243 / 2500 : ℝ) then
          ∫ t in Ico (19 / 125 : ℝ) (59 / 250), f ![u, t]
        else
          ∫ t in Icc (19 / 125 : ℝ) ((833 / 2500 : ℝ) - u), f ![u, t] := by
  rw [integral_productDomain_eq_nested 0 f hf]
  apply setIntegral_congr_fun measurableSet_Ico
  intro u _
  by_cases hu : u ≤ (243 / 2500 : ℝ)
  · rw [if_pos hu, productSlice_zero_of_le hu]
  · rw [if_neg hu, productSlice_zero_of_gt (lt_of_not_ge hu)]

/-- Concrete reciprocal mass: integrability comes from the literal positive
box, so this specialization has no analytic premise at all. -/
theorem reciprocal_mass_zero_eq_split :
    (∫ x in currentChenUpsilon6LogDomain 0, 1 / (x 0 * x 1)) =
      ∫ u in Ico (417 / 5000 : ℝ) (19 / 125),
        if u ≤ (243 / 2500 : ℝ) then
          ∫ t in Ico (19 / 125 : ℝ) (59 / 250), 1 / (u * t)
        else
          ∫ t in Icc (19 / 125 : ℝ) ((833 / 2500 : ℝ) - u), 1 / (u * t) := by
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
    integral_productDomain_zero_eq_split (fun x : Point => 1 / (x 0 * x 1))
      integrableOn_currentChenUpsilon6LogRectangle

/-- The actual ordinary kernel also obeys the same exact integral geometry.
This is a geometric identity, not a second proof of its arithmetic mean. -/
theorem ordinary_kernel_zero_eq_split :
    (∫ x in currentChenUpsilon6LogDomain 0, currentChenUpsilon6OrdinaryKernel x) =
      ∫ u in Ico (417 / 5000 : ℝ) (19 / 125),
        if u ≤ (243 / 2500 : ℝ) then
          ∫ t in Ico (19 / 125 : ℝ) (59 / 250), currentChenUpsilon6OrdinaryKernel ![u, t]
        else
          ∫ t in Icc (19 / 125 : ℝ) ((833 / 2500 : ℝ) - u),
            currentChenUpsilon6OrdinaryKernel ![u, t] := by
  exact integral_productDomain_zero_eq_split currentChenUpsilon6OrdinaryKernel
    integrableOn_currentChenUpsilon6OrdinaryKernel

end

end ImbalancedChen.P5U6RunboProductSlicesSourceOnly
