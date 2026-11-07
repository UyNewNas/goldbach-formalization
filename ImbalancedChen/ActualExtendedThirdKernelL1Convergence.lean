import ImbalancedChen.ActualExtendedThirdCompactKernelApproximation
import ImbalancedChen.ActualExtendedThirdBoundaryLoss

/-!
# Whole-domain L1 approximation by the actual finite robust correction

The full difference uses the exact finite lookup and the unbuffered ideal
kernel. A single small-z cutoff is chosen first. On its complement, the
actual two strips pay both kernels using independent buffer and strip-width
parameters; the remaining compact region uses the proved uniform estimate.

No integrability, null-wall, selector-limit or uniform-tail assumption is
supplied by the caller. The conclusion is an absolute nonnegative Lebesgue
mass bound on the full original closed ordered domain. Arithmetic density,
factorization actions and the final hUpper coefficient are not claimed.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical ENNReal

def actualExtendedThirdKernelDifferenceMassOn (e : ℝ) (m : ℕ)
    (s : Set (Fin 3 → ℝ)) : ℝ≥0∞ :=
  ∫⁻ t in s, ENNReal.ofReal |actualExtendedThirdFiniteKernel e m t -
    actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)|

private theorem differenceMass_le_two_masses (e : ℝ) (m : ℕ) (s : Set (Fin 3 → ℝ)) :
    actualExtendedThirdKernelDifferenceMassOn e m s ≤
      (∫⁻ t in s, ENNReal.ofReal |actualExtendedThirdFiniteKernel e m t|) +
        ∫⁻ t in s, ENNReal.ofReal |actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)| := by
  have hf : Measurable (fun t : Fin 3 → ℝ =>
      ENNReal.ofReal |actualExtendedThirdFiniteKernel e m t|) := by
    simpa only [Real.norm_eq_abs] using
      (measurable_actualExtendedThirdFiniteKernel e m).norm.ennreal_ofReal
  calc
    _ ≤ ∫⁻ t in s, ENNReal.ofReal |actualExtendedThirdFiniteKernel e m t| +
        ENNReal.ofReal |actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)| := by
      apply lintegral_mono
      intro t
      exact (ENNReal.ofReal_le_ofReal (abs_sub _ _)).trans_eq
        (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _))
    _ = _ := lintegral_add_left hf _

/-- The ideal kernel buffer is zero even when the physical buffer and the
width are nonzero. The two parameters are not silently identified. -/
theorem actualExtendedThirdKernelDifferenceWallMass_le
    {e h a δ : ℝ} {m : ℕ} (hh : 0 < h) (hδ : 0 ≤ δ) :
    actualExtendedThirdKernelDifferenceMassOn e m (actualExtendedThirdWallStrip h a δ) ≤
      ENNReal.ofReal (2 * actualExtendedThirdCompactKernelBound h * (δ * thirdPrefixRho ^ 2)) := by
  have hB : 0 ≤ actualExtendedThirdCompactKernelBound h * (δ * thirdPrefixRho ^ 2) := by
    exact mul_nonneg (actualExtendedThirdCompactKernelBound_pos hh).le
      (mul_nonneg hδ (sq_nonneg _))
  calc
    _ ≤ actualExtendedThirdWallMass true e m h a δ +
        actualExtendedThirdWallMass false 0 m h a δ := differenceMass_le_two_masses e m _
    _ ≤ ENNReal.ofReal (actualExtendedThirdCompactKernelBound h * (δ * thirdPrefixRho ^ 2)) +
        ENNReal.ofReal (actualExtendedThirdCompactKernelBound h * (δ * thirdPrefixRho ^ 2)) :=
      add_le_add (actualExtendedThirdWallMass_le true hh hδ)
        (actualExtendedThirdWallMass_le false hh hδ)
    _ = _ := by
      rw [← ENNReal.ofReal_add hB hB]
      congr 1
      ring

private def compactRectangle : Set (Fin 3 → ℝ) :=
  Set.univ.pi (fun _ => Icc (0 : ℝ) thirdPrefixRho)

private theorem compactRectangle_volume :
    volume compactRectangle = ENNReal.ofReal (thirdPrefixRho ^ 3) := by
  have hr : 0 ≤ thirdPrefixRho := by norm_num [thirdPrefixRho]
  have heq : volume compactRectangle =
      ENNReal.ofReal thirdPrefixRho * ENNReal.ofReal thirdPrefixRho *
        ENNReal.ofReal thirdPrefixRho := by
    rw [compactRectangle, volume_pi_pi, Fin.prod_univ_three]
    change volume (Icc 0 thirdPrefixRho) * volume (Icc 0 thirdPrefixRho) *
      volume (Icc 0 thirdPrefixRho) = _
    simp only [Real.volume_Icc, sub_zero]
  rw [heq, ← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_mul (mul_nonneg hr hr)]
  congr 1
  ring

theorem actualExtendedThirdCompactOrder_volume_le {h : ℝ} (hh : 0 < h) :
    volume (actualExtendedThirdCompactOrder h) ≤ ENNReal.ofReal (thirdPrefixRho ^ 3) := by
  rw [← compactRectangle_volume]
  apply measure_mono
  intro t ht i _hi
  have hz0 : 0 ≤ t 2 := hh.le.trans ht.1
  have hy0 : 0 ≤ t 1 := hz0.trans ht.2.1
  have hx0 : 0 ≤ t 0 := hy0.trans ht.2.2.1
  have hy : t 1 ≤ thirdPrefixRho := ht.2.2.1.trans ht.2.2.2
  have hz : t 2 ≤ thirdPrefixRho := ht.2.1.trans hy
  fin_cases i
  · exact ⟨hx0, ht.2.2.2⟩
  · exact ⟨hy0, hy⟩
  · exact ⟨hz0, hz⟩

def actualExtendedThirdCompactGoodRegion (h δ : ℝ) : Set (Fin 3 → ℝ) :=
  actualExtendedThirdCompactOrder h \ (actualExtendedThirdWallStrip h mu δ ∪
    actualExtendedThirdWallStrip h thirdPrefixRho δ)

theorem measurableSet_actualExtendedThirdCompactGoodRegion (h δ : ℝ) :
    MeasurableSet (actualExtendedThirdCompactGoodRegion h δ) :=
  (isClosed_actualExtendedThirdCompactOrder h).measurableSet.diff
    ((measurableSet_actualExtendedThirdWallStrip h mu δ).union
      (measurableSet_actualExtendedThirdWallStrip h thirdPrefixRho δ))

private theorem differenceMass_cover (e h δ : ℝ) (m : ℕ) :
    actualExtendedThirdKernelDifferenceMassOn e m
        (actualExtendedThirdClosedOrderRegion thirdPrefixRho) ≤
      ((actualExtendedThirdKernelDifferenceMassOn e m (actualExtendedThirdClosedOrderRegion h) +
        actualExtendedThirdKernelDifferenceMassOn e m (actualExtendedThirdCompactGoodRegion h δ)) +
          actualExtendedThirdKernelDifferenceMassOn e m (actualExtendedThirdWallStrip h mu δ)) +
        actualExtendedThirdKernelDifferenceMassOn e m
          (actualExtendedThirdWallStrip h thirdPrefixRho δ) := by
  let S := actualExtendedThirdClosedOrderRegion h
  let G := actualExtendedThirdCompactGoodRegion h δ
  let M := actualExtendedThirdWallStrip h mu δ
  let R := actualExtendedThirdWallStrip h thirdPrefixRho δ
  have hsub : actualExtendedThirdClosedOrderRegion thirdPrefixRho ⊆ ((S ∪ G) ∪ M) ∪ R := by
    intro t ht
    by_cases hz : t 2 ≤ h
    · exact Or.inl (Or.inl (Or.inl ⟨ht.1, hz, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩))
    · have hc : t ∈ actualExtendedThirdCompactOrder h :=
        ⟨(lt_of_not_ge hz).le, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩
      by_cases hm : t ∈ M
      · exact Or.inl (Or.inr hm)
      · by_cases hr : t ∈ R
        · exact Or.inr hr
        · exact Or.inl (Or.inl (Or.inr ⟨hc, fun hu => hu.elim hm hr⟩))
  have hmono : actualExtendedThirdKernelDifferenceMassOn e m
      (actualExtendedThirdClosedOrderRegion thirdPrefixRho) ≤
      actualExtendedThirdKernelDifferenceMassOn e m (((S ∪ G) ∪ M) ∪ R) :=
    lintegral_mono_set hsub
  apply hmono.trans
  calc
    _ ≤ actualExtendedThirdKernelDifferenceMassOn e m ((S ∪ G) ∪ M) +
        actualExtendedThirdKernelDifferenceMassOn e m R := lintegral_union_le _ _ _
    _ ≤ (actualExtendedThirdKernelDifferenceMassOn e m (S ∪ G) +
        actualExtendedThirdKernelDifferenceMassOn e m M) +
          actualExtendedThirdKernelDifferenceMassOn e m R :=
      add_le_add (lintegral_union_le _ _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add (lintegral_union_le _ _ _) le_rfl) le_rfl

/-- Full absolute L1 approximation, with one cutoff preceding all subsequent
buffers and meshes. Every set and kernel is the literal actual constructor. -/
theorem actualExtendedThirdKernelDifferenceMass_uniform_small {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ thirdPrefixTailMargin / 4 ∧
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 384 ∧ ∃ m₀ : ℕ,
        ∀ e : ℝ, 0 ≤ e → e ≤ e₀ → ∀ m : ℕ, m₀ ≤ m →
          actualExtendedThirdKernelDifferenceMassOn e m
            (actualExtendedThirdClosedOrderRegion thirdPrefixRho) ≤ ENNReal.ofReal ε := by
  obtain ⟨h, hh, hs, htail⟩ :=
    actualExtendedThirdWallClosedTailMass_uniform_small (by positivity : 0 < ε / 8)
  let C : ℝ := actualExtendedThirdCompactKernelBound h * thirdPrefixRho ^ 2
  have hC : 0 ≤ C := mul_nonneg (actualExtendedThirdCompactKernelBound_pos hh).le (sq_nonneg _)
  let δ : ℝ := ε / (16 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (16 * (C + 1)) = ε :=
    div_mul_cancel₀ _ (by positivity : 16 * (C + 1) ≠ 0)
  let ν : ℝ := ε / (4 * (thirdPrefixRho ^ 3 + 1))
  have hrhop : 0 < thirdPrefixRho := by norm_num [thirdPrefixRho]
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνeq : ν * (4 * (thirdPrefixRho ^ 3 + 1)) = ε :=
    div_mul_cancel₀ _ (by norm_num [thirdPrefixRho])
  obtain ⟨e₁, he₁, he₁cap, m₁, happ⟩ :=
    actualExtendedThirdFiniteKernel_uniform_approx_off_strips hh hν
  obtain ⟨m₂, hm₂⟩ := Filter.eventually_atTop.mp
    (tendsto_actualExtendedThirdDyadicStep.eventually (gt_mem_nhds (half_pos hδ)))
  refine ⟨h, hh, hs, min e₁ (δ / 8), lt_min he₁ (by positivity),
    (min_le_left _ _).trans he₁cap, max m₁ m₂, ?_⟩
  intro e he0 he m hm
  have he₁' : e ≤ e₁ := he.trans (min_le_left _ _)
  have hecap : e ≤ 1 / 384 := he₁'.trans he₁cap
  have hme₁ : m₁ ≤ m := (le_max_left _ _).trans hm
  have hme₂ : m₂ ≤ m := (le_max_right _ _).trans hm
  let width : ℝ := 4 * e + actualExtendedThirdDyadicStep m
  have hw0 : 0 ≤ width := by
    dsimp [width]
    exact add_nonneg (mul_nonneg (by norm_num) he0) (actualExtendedThirdDyadicStep_pos m).le
  have hwidth : width ≤ δ := by
    have heb := he.trans (min_le_right _ _)
    dsimp [width]
    linarith [hm₂ m hme₂]
  have hsmall : actualExtendedThirdKernelDifferenceMassOn e m
      (actualExtendedThirdClosedOrderRegion h) ≤ ENNReal.ofReal (ε / 4) := by
    calc
      _ ≤ actualExtendedThirdWallClosedTailMass true e m h +
          actualExtendedThirdWallClosedTailMass false 0 m h := differenceMass_le_two_masses e m _
      _ ≤ ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8) :=
        add_le_add (htail e he0 hecap m true) (htail 0 le_rfl (by norm_num) m false)
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 8) (by positivity : 0 ≤ ε / 8)]
        congr 1
        ring
  have hwallnum : 2 * actualExtendedThirdCompactKernelBound h *
      (width * thirdPrefixRho ^ 2) ≤ ε / 8 := by
    have hcw : C * width ≤ C * δ := mul_le_mul_of_nonneg_left hwidth hC
    change 2 * actualExtendedThirdCompactKernelBound h *
      (width * thirdPrefixRho ^ 2) ≤ ε / 8
    dsimp [C] at hcw hδeq
    nlinarith only [hcw, hδeq, hδ.le]
  have hmu : actualExtendedThirdKernelDifferenceMassOn e m
      (actualExtendedThirdWallStrip h mu width) ≤ ENNReal.ofReal (ε / 8) :=
    (actualExtendedThirdKernelDifferenceWallMass_le hh hw0).trans
      (ENNReal.ofReal_le_ofReal hwallnum)
  have hrho : actualExtendedThirdKernelDifferenceMassOn e m
      (actualExtendedThirdWallStrip h thirdPrefixRho width) ≤ ENNReal.ofReal (ε / 8) :=
    (actualExtendedThirdKernelDifferenceWallMass_le hh hw0).trans
      (ENNReal.ofReal_le_ofReal hwallnum)
  have hgood : actualExtendedThirdKernelDifferenceMassOn e m
      (actualExtendedThirdCompactGoodRegion h width) ≤ ENNReal.ofReal (ε / 4) := by
    have hv : volume (actualExtendedThirdCompactGoodRegion h width) ≤
        ENNReal.ofReal (thirdPrefixRho ^ 3) :=
      (measure_mono (Set.sdiff_subset : actualExtendedThirdCompactGoodRegion h width ⊆
        actualExtendedThirdCompactOrder h)).trans (actualExtendedThirdCompactOrder_volume_le hh)
    calc
      _ ≤ ∫⁻ _t in actualExtendedThirdCompactGoodRegion h width, ENNReal.ofReal ν := by
        apply setLIntegral_mono' (measurableSet_actualExtendedThirdCompactGoodRegion h width)
        intro t ht
        apply ENNReal.ofReal_le_ofReal
        apply happ e he0 he₁' m hme₁ t ht.1
        · intro hn
          exact ht.2 (Or.inl hn)
        · intro hn
          exact ht.2 (Or.inr hn)
      _ = ENNReal.ofReal ν * volume (actualExtendedThirdCompactGoodRegion h width) := by simp
      _ ≤ ENNReal.ofReal ν * ENNReal.ofReal (thirdPrefixRho ^ 3) := mul_le_mul_right hv _
      _ = ENNReal.ofReal (ν * thirdPrefixRho ^ 3) := (ENNReal.ofReal_mul hν.le).symm
      _ ≤ ENNReal.ofReal (ε / 4) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith only [hνeq, hν.le]
  apply (differenceMass_cover e h width m).trans
  apply (add_le_add (add_le_add (add_le_add hsmall hgood) hmu) hrho).trans
  calc
    ((ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) + ENNReal.ofReal (ε / 8)) +
        ENNReal.ofReal (ε / 8) = ENNReal.ofReal (3 * ε / 4) := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 4) (by positivity : 0 ≤ ε / 4),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 4 + ε / 4) (by positivity : 0 ≤ ε / 8),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ (ε / 4 + ε / 4) + ε / 8)
          (by positivity : 0 ≤ ε / 8)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)

end

end ImbalancedChen
