import ImbalancedChen.Part3AEPeriodicChartCanonicalDescent
import ImbalancedChen.Part3LocalSmoothWeakDerivativeUniqueness

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The SAME raw local weak horizontal derivative of a true period-one value
is integer-periodic AE. The proof shifts an actual compact smooth test,
uses genuine real-plane translation invariance and the ordinary shifted
Frechet derivative, and then applies local weak-test uniqueness. Local L1
of the shifted raw field is derived on compact translated sets. No
periodicity of the derivative, H1 seam trace or boundary value is assumed.
This supplies the missing canonical raw-field descent input for arbitrary
actual normalized cusp frames once their quotient value period is known.
-/
namespace ImbalancedChen.Part3.PeriodicValueWeakDerivativePeriodAE20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open ProductConvolutionSecondDerivatives20261026a PeriodicCompactChartTests20261026b
open LocalSmoothWeakDerivativeUniqueness20261026b

def horizontalShift (t : ℝ) : Plane := (t, 0)

@[simp] theorem add_horizontalShift (p : Plane) (t : ℝ) :
    p + horizontalShift t = (p.1 + t, p.2) := by
  ext <;> simp [horizontalShift]

private theorem shifted_locallyIntegrable {a t : ℝ} {D : Plane → ℂ}
    (hD : LocallyIntegrableOn D {p : Plane | a < p.2} volume) :
    LocallyIntegrableOn (fun p : Plane => D (p + horizontalShift t))
      {p : Plane | a < p.2} volume := by
  have hΩ : IsOpen {p : Plane | a < p.2} := isOpen_lt continuous_const continuous_snd
  rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
  intro K hKU hK
  let K' : Set Plane := (fun p : Plane => p + horizontalShift t) '' K
  have hK' : IsCompact K' := hK.image (continuous_id.add continuous_const)
  have hKU' : K' ⊆ {p : Plane | a < p.2} := by
    rintro q ⟨p, hp, rfl⟩
    simpa only [horizontalShift, Prod.snd_add, add_zero] using hKU hp
  have hi : Integrable (K'.indicator D) (volume : Measure Plane) :=
    (integrable_indicator_iff hK'.measurableSet).mpr (hD.integrableOn_compact_subset hKU' hK')
  have hit := (hi.comp_add_right (horizontalShift t)).integrableOn K
  apply hit.congr
  filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
  exact indicator_of_mem (show p + horizontalShift t ∈ K' from ⟨p, hp, rfl⟩) D

private theorem shifted_test_tsupport {a t : ℝ} {Ψ : Plane → ℂ}
    (hs : tsupport Ψ ⊆ {p : Plane | a < p.2}) :
    tsupport (fun p : Plane => Ψ (p - horizontalShift t)) ⊆ {p : Plane | a < p.2} := by
  intro p hp
  have h := hs (tsupport_comp_subset_preimage Ψ (continuous_id.sub continuous_const) hp)
  simpa only [horizontalShift, Prod.snd_sub, sub_zero] using h

private theorem directional_shift (t : ℝ) (Ψ : Plane → ℂ) (p : Plane) :
    directional xDirection (fun q : Plane => Ψ (q - horizontalShift t)) p =
      directional xDirection Ψ (p - horizontalShift t) := by
  simp only [directional, sub_eq_add_neg, fderiv_comp_add_right]

/-- A shifted raw derivative is a weak derivative of the SAME value,
because the value is truly invariant under that horizontal translation. -/
theorem shifted_raw_weak_of_value_invariant {a t : ℝ} {F D : Plane → ℂ}
    (hvalue : ∀ p : Plane, a < p.2 → F (p + horizontalShift t) = F p)
    (hw : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2} F D) :
    HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2} F
      (fun p : Plane => D (p + horizontalShift t)) := by
  intro Ψ hΨ hc hs
  let Ψt : Plane → ℂ := fun p => Ψ (p - horizontalShift t)
  have hΨt : ContDiff ℝ ∞ Ψt := hΨ.comp (contDiff_id.sub contDiff_const)
  have hct : HasCompactSupport Ψt := by
    simpa only [Ψt, sub_eq_add_neg, Function.comp_def] using
      hc.comp_homeomorph (Homeomorph.addRight (-horizontalShift t))
  have hst : tsupport Ψt ⊆ {p : Plane | a < p.2} := shifted_test_tsupport hs
  have hleft :
      (∫ p : Plane, star (Ψ p) * D (p + horizontalShift t)) =
      ∫ p : Plane, star (Ψt p) * D p := by
    have h := integral_add_right_eq_self
      (fun q : Plane => star (Ψ (q - horizontalShift t)) * D q) (horizontalShift t)
    simpa only [add_sub_cancel_right, Ψt] using h
  have hright :
      (∫ p : Plane, star (directional xDirection Ψt p) * F p) =
      ∫ p : Plane, star (directional xDirection Ψ p) * F p := by
    simp_rw [Ψt, directional_shift]
    calc
      _ = ∫ p : Plane, star (directional xDirection Ψ p) * F (p + horizontalShift t) := by
        have h := integral_add_right_eq_self
          (fun q : Plane => star (directional xDirection Ψ (q - horizontalShift t)) * F q)
          (horizontalShift t)
        simpa only [add_sub_cancel_right] using h.symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by
          by_cases hp : a < p.2
          · rw [hvalue p hp]
          · have hn : p ∉ tsupport Ψ := fun h => hp (hs h)
            have hz : directional xDirection Ψ p = 0 := by
              simp only [directional, fderiv_of_notMem_tsupport ℝ hn, ContinuousLinearMap.zero_apply]
            simp [hz]
  rw [hleft]
  exact (hw Ψt hΨt hct hst).trans (congrArg Neg.neg hright)

/-- Local weak derivative uniqueness produces translation AE invariance
of the ORIGINAL raw derivative witness. -/
theorem raw_weak_derivative_translation_ae {a t : ℝ} {F D : Plane → ℂ}
    (hD : LocallyIntegrableOn D {p : Plane | a < p.2} volume)
    (hvalue : ∀ p : Plane, a < p.2 → F (p + horizontalShift t) = F p)
    (hw : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2} F D) :
    ∀ᵐ p ∂(volume : Measure Plane).restrict {p : Plane | a < p.2},
      D (p + horizontalShift t) = D p := by
  have hwt := shifted_raw_weak_of_value_invariant hvalue hw
  have he := local_ae_eq_of_smooth_test_pairings
    (isOpen_lt continuous_const continuous_snd) (shifted_locallyIntegrable hD) hD
    (fun Ψ hΨ hc hs => (hwt Ψ hΨ hc hs).trans (hw Ψ hΨ hc hs).symm)
  exact (ae_restrict_iff' (isOpen_lt continuous_const continuous_snd).measurableSet).mpr he

/-- ALL integer periods of the SAME derivative are DERIVED from the true
period-one VALUE and local distributional differentiation. -/
theorem periodic_value_raw_derivative_integer_period_ae {a : ℝ} {F D : Plane → ℂ}
    (hD : LocallyIntegrableOn D {p : Plane | a < p.2} volume)
    (hperiodF : ∀ y : ℝ, a < y → Function.Periodic (fun x : ℝ => F (x, y)) 1)
    (hw : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2} F D) :
    ∀ k : ℤ, ∀ᵐ p ∂(volume : Measure Plane).restrict {p : Plane | a < p.2},
      D (p.1 + (k : ℝ), p.2) = D p := by
  intro k
  have hv : ∀ p : Plane, a < p.2 → F (p + horizontalShift (k : ℝ)) = F p := by
    intro p hp
    have h := (hperiodF p.2 hp).int_mul k p.1
    simpa only [add_horizontalShift, mul_one] using h
  simpa only [add_horizontalShift] using
    raw_weak_derivative_translation_ae hD hv hw

end
end ImbalancedChen.Part3.PeriodicValueWeakDerivativePeriodAE20261026b
