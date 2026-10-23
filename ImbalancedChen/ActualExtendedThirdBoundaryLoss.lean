import ImbalancedChen.ActualExtendedThirdStripIntegral
import ImbalancedChen.ActualExtendedThirdFiniteTailIntegral

/-!
# Whole-domain vanishing of the two actual extended-third boundary strips

The true finite physical kernel and the literal ideal kernel share a paid
canonical small-z tail bound. Above the fixed cutoff the previously proved
bounded-kernel strip estimate applies. The final tolerance chooses the cutoff
first, then the buffer and common mesh. No tail estimate or vanishing boundary
loss is supplied as a hypothesis.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory
open VariableEnvelope
open scoped Classical ENNReal

def actualExtendedThirdWallClosedTailMass (physical : Bool) (e : ℝ) (m : ℕ) (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in actualExtendedThirdClosedOrderRegion h,
    ENNReal.ofReal |actualExtendedThirdWallKernel physical e m t|

theorem actualExtendedThirdWallClosedTailMass_le (physical : Bool) {e h : ℝ} {m : ℕ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (hh : 0 < h) (hs : h ≤ thirdPrefixTailMargin / 4) :
    actualExtendedThirdWallClosedTailMass physical e m h ≤
      ENNReal.ofReal (18 * h / (thirdPrefixTailMargin - h) ^ 2 *
        (Real.log (thirdPrefixRho / h) ^ 2 + 2 * Real.log (thirdPrefixRho / h) + 2)) := by
  cases physical
  · have hmass : actualExtendedThirdWallClosedTailMass false e m h =
        actualExtendedThirdOrderedTailMass e h := by
      unfold actualExtendedThirdWallClosedTailMass actualExtendedThirdOrderedTailMass
      rw [setLIntegral_congr (actualExtendedThirdClosedOrderRegion_ae_eq h)]
      apply setLIntegral_congr_fun (measurableSet_actualExtendedThirdOrderedTailRegion h)
      intro t ht
      change ENNReal.ofReal |actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)| = _
      rw [abs_of_nonneg (actualExtendedThirdGatedKernel_nonneg_on_region e h ht)]
    rw [hmass, actualExtendedThirdOrderedTailMass_eq_core he hs]
    exact actualExtendedThirdIdealTailMass_le_eighteen he hh hs
  · change actualExtendedThirdFiniteClosedTailMass e m h ≤ _
    rw [actualExtendedThirdFiniteClosedTailMass_eq_ordered,
      actualExtendedThirdFiniteOrderedTailMass_eq_core he0 he hs]
    exact actualExtendedThirdFiniteNestedTailMass_le he0 he hh hs

theorem actualExtendedThirdWallClosedTailMass_uniform_small {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ thirdPrefixTailMargin / 4 ∧
      ∀ e : ℝ, 0 ≤ e → e ≤ 1 / 384 → ∀ m : ℕ, ∀ physical : Bool,
        actualExtendedThirdWallClosedTailMass physical e m h ≤ ENNReal.ofReal ε := by
  have hupper : Tendsto (fun h : ℝ => ENNReal.ofReal
      (18 * h / (thirdPrefixTailMargin - h) ^ 2 *
        (Real.log (thirdPrefixRho / h) ^ 2 +
          2 * Real.log (thirdPrefixRho / h) + 2)))
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (tendsto_roughActivationTailEnvelope_zero
        (a := thirdPrefixRho) (c := thirdPrefixTailMargin)
        (by norm_num [thirdPrefixRho]) (by norm_num [thirdPrefixTailMargin]))
  have hevent := hupper.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  have hsmall : Iio (thirdPrefixTailMargin / 4) ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num [thirdPrefixTailMargin]))
  have hpos : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
  obtain ⟨h, hh, hs, hb⟩ := Filter.Eventually.exists
    (Filter.Eventually.and (f := 𝓝[>] (0 : ℝ)) hpos
      (Filter.Eventually.and hsmall hevent))
  exact ⟨h, hh, hs.le, fun e he0 he m physical =>
    (actualExtendedThirdWallClosedTailMass_le physical he0 he hh hs.le).trans hb.le⟩

def actualExtendedThirdFullWallStrip (a δ : ℝ) : Set (Fin 3 → ℝ) :=
  actualExtendedThirdClosedOrderRegion thirdPrefixRho ∩ {t | a - δ < t 0 ∧ t 0 ≤ a}

def actualExtendedThirdFullWallMass (physical : Bool) (e : ℝ) (m : ℕ) (a δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in actualExtendedThirdFullWallStrip a δ,
    ENNReal.ofReal |actualExtendedThirdWallKernel physical e m t|

/-- Split the actual full strip at h. An overlap on z = h is harmless for
this upper bound; no unproved null-face assertion is needed. -/
theorem actualExtendedThirdFullWallMass_le_split (physical : Bool) (e h a δ : ℝ) (m : ℕ) :
    actualExtendedThirdFullWallMass physical e m a δ ≤
      actualExtendedThirdWallClosedTailMass physical e m h +
        actualExtendedThirdWallMass physical e m h a δ := by
  have hsub : actualExtendedThirdFullWallStrip a δ ⊆
      actualExtendedThirdClosedOrderRegion h ∪ actualExtendedThirdWallStrip h a δ := by
    intro t ht
    by_cases hz : t 2 ≤ h
    · exact Or.inl ⟨ht.1.1, hz, ht.1.2.2.1, ht.1.2.2.2.1, ht.1.2.2.2.2⟩
    · exact Or.inr ⟨⟨(lt_of_not_ge hz).le, ht.1.2.2.1, ht.1.2.2.2.1,
        ht.1.2.2.2.2⟩, ht.2⟩
  exact (lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)

/-- The complete actual mu-transition and rho-stop losses vanish together.
The cutoff precedes every buffer and mesh choice, and the same finite lookup
appears in both its tail and compact integrals. -/
theorem actualExtendedThirdFullBoundaryLoss_uniform_small {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ thirdPrefixTailMargin / 4 ∧
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 384 ∧ ∃ m₀ : ℕ,
        ∀ e : ℝ, 0 ≤ e → e ≤ e₀ → ∀ m : ℕ, m₀ ≤ m → ∀ physical : Bool,
          actualExtendedThirdFullWallMass physical e m mu
              (4 * e + actualExtendedThirdDyadicStep m) ≤ ENNReal.ofReal ε ∧
            actualExtendedThirdFullWallMass physical e m thirdPrefixRho
              (4 * e + actualExtendedThirdDyadicStep m) ≤ ENNReal.ofReal ε := by
  obtain ⟨h, hh, hs, htail⟩ := actualExtendedThirdWallClosedTailMass_uniform_small (half_pos hε)
  obtain ⟨e₁, he₁, m₀, hm₀⟩ := actualExtendedThirdBoundaryStrips_uniform_small hh (half_pos hε)
  refine ⟨h, hh, hs, min e₁ (1 / 384), lt_min he₁ (by norm_num), min_le_right _ _, m₀, ?_⟩
  intro e he0 he m hm physical
  have he₁' : e ≤ e₁ := he.trans (min_le_left _ _)
  have he' : e ≤ 1 / 384 := he.trans (min_le_right _ _)
  have ht := htail e he0 he' m physical
  have hc := hm₀ e he0 he₁' m hm physical
  have hadd : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
    congr 1
    ring
  constructor
  · exact (actualExtendedThirdFullWallMass_le_split physical e h mu _ m).trans
      ((add_le_add ht hc.1).trans_eq hadd)
  · exact (actualExtendedThirdFullWallMass_le_split physical e h thirdPrefixRho _ m).trans
      ((add_le_add ht hc.2).trans_eq hadd)

end

end ImbalancedChen
