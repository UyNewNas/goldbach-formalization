import ImbalancedChen.ActualExtendedThirdFinitePhysicalKernel

/-!
# Vanishing actual transition and first-stop strips at fixed cutoff

The precise strips have width `4e + mesh`, at x = mu and x = rho. Below
the fixed cutoff h, the preceding module supplies a genuine canonical tail
bound uniform over all actual finite lookups. Above h, both the literal
ideal kernel and this actual finite physical kernel are uniformly bounded.
The strip volume and absolute integral are paid directly, with no assumed
integrability, null-strip estimate, or selector regularity.

The cutoff is fixed first. For each positive tolerance a buffer threshold
and a common grid threshold then work for both actual strips and kernels.
This is an analytic boundary estimate, not the same-policy arithmetic mean.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical BigOperators ENNReal

def actualExtendedThirdCompactOrder (h : ℝ) : Set (Fin 3 → ℝ) :=
  {t | h ≤ t 2 ∧ t 2 ≤ t 1 ∧ t 1 ≤ t 0 ∧ t 0 ≤ thirdPrefixRho}

theorem isClosed_actualExtendedThirdCompactOrder (h : ℝ) :
    IsClosed (actualExtendedThirdCompactOrder h) := by
  have hx : Continuous (fun t : Fin 3 → ℝ => t 0) := continuous_apply 0
  have hy : Continuous (fun t : Fin 3 → ℝ => t 1) := continuous_apply 1
  have hz : Continuous (fun t : Fin 3 → ℝ => t 2) := continuous_apply 2
  exact (isClosed_le continuous_const hz).inter ((isClosed_le hz hy).inter
    ((isClosed_le hy hx).inter (isClosed_le hx continuous_const)))

def actualExtendedThirdWallStrip (h a δ : ℝ) : Set (Fin 3 → ℝ) :=
  actualExtendedThirdCompactOrder h ∩ {t | a - δ < t 0 ∧ t 0 ≤ a}

theorem measurableSet_actualExtendedThirdWallStrip (h a δ : ℝ) :
    MeasurableSet (actualExtendedThirdWallStrip h a δ) :=
  (isClosed_actualExtendedThirdCompactOrder h).measurableSet.inter
    (((isOpen_lt continuous_const (continuous_apply 0)).measurableSet).inter
      (isClosed_le (continuous_apply 0) continuous_const).measurableSet)

private def stripRectangle (a δ : ℝ) : Set (Fin 3 → ℝ) :=
  Set.univ.pi (fun i => Icc (![a - δ, 0, 0] i) (![a, thirdPrefixRho, thirdPrefixRho] i))

private theorem stripRectangle_volume {a δ : ℝ} (hδ : 0 ≤ δ) :
    volume (stripRectangle a δ) = ENNReal.ofReal (δ * thirdPrefixRho ^ 2) := by
  have hrho : 0 ≤ thirdPrefixRho := by norm_num [thirdPrefixRho]
  have hdiff : a - (a - δ) = δ := by ring
  have hrect : volume (stripRectangle a δ) =
      ENNReal.ofReal δ * ENNReal.ofReal thirdPrefixRho * ENNReal.ofReal thirdPrefixRho := by
    rw [stripRectangle, volume_pi_pi, Fin.prod_univ_three]
    change volume (Icc (a - δ) a) * volume (Icc 0 thirdPrefixRho) *
      volume (Icc 0 thirdPrefixRho) = _
    simp only [Real.volume_Icc, hdiff, sub_zero]
  rw [hrect, ← ENNReal.ofReal_mul hδ, ← ENNReal.ofReal_mul (mul_nonneg hδ hrho)]
  congr 1
  ring

theorem actualExtendedThirdWallStrip_volume_le {h a δ : ℝ} (hh : 0 < h) (hδ : 0 ≤ δ) :
    volume (actualExtendedThirdWallStrip h a δ) ≤ ENNReal.ofReal (δ * thirdPrefixRho ^ 2) := by
  rw [← stripRectangle_volume (a := a) hδ]
  apply measure_mono
  intro t ht i _hi
  have hz0 : 0 ≤ t 2 := hh.le.trans ht.1.1
  have hy0 : 0 ≤ t 1 := hz0.trans ht.1.2.1
  have hy : t 1 ≤ thirdPrefixRho := ht.1.2.2.1.trans ht.1.2.2.2
  have hz : t 2 ≤ thirdPrefixRho := ht.1.2.1.trans hy
  fin_cases i
  · exact ⟨ht.2.1.le, ht.2.2⟩
  · exact ⟨hy0, hy⟩
  · exact ⟨hz0, hz⟩

/-- The two concrete analytic kernels whose boundary losses must be paid. -/
def actualExtendedThirdWallKernel (physical : Bool) (e : ℝ) (m : ℕ) (t : Fin 3 → ℝ) : ℝ :=
  if physical then actualExtendedThirdFiniteKernel e m t
  else actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)

theorem measurable_actualExtendedThirdWallKernel (physical : Bool) (e : ℝ) (m : ℕ) :
    Measurable (actualExtendedThirdWallKernel physical e m) := by
  cases physical
  · exact measurable_actualExtendedThirdGatedKernel e
  · exact measurable_actualExtendedThirdFiniteKernel e m

theorem actualExtendedThirdWallKernel_abs_le (physical : Bool) {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdCompactOrder h) :
    |actualExtendedThirdWallKernel physical e m t| ≤ actualExtendedThirdCompactKernelBound h := by
  have hz := ht.1
  have hy := hz.trans ht.2.1
  have hx := hy.trans ht.2.2.1
  cases physical
  · exact actualExtendedThirdGatedKernel_abs_le hh hx hy hz
  · exact actualExtendedThirdFiniteKernel_abs_le hh hx hy hz

def actualExtendedThirdWallMass (physical : Bool) (e : ℝ) (m : ℕ) (h a δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in actualExtendedThirdWallStrip h a δ,
    ENNReal.ofReal |actualExtendedThirdWallKernel physical e m t|

theorem actualExtendedThirdWallMass_le (physical : Bool) {e h a δ : ℝ} {m : ℕ}
    (hh : 0 < h) (hδ : 0 ≤ δ) :
    actualExtendedThirdWallMass physical e m h a δ ≤
      ENNReal.ofReal (actualExtendedThirdCompactKernelBound h * (δ * thirdPrefixRho ^ 2)) := by
  calc
    actualExtendedThirdWallMass physical e m h a δ ≤
        ∫⁻ _t in actualExtendedThirdWallStrip h a δ,
          ENNReal.ofReal (actualExtendedThirdCompactKernelBound h) := by
      apply setLIntegral_mono' (measurableSet_actualExtendedThirdWallStrip h a δ)
      intro t ht
      exact ENNReal.ofReal_le_ofReal (actualExtendedThirdWallKernel_abs_le physical hh ht.1)
    _ = ENNReal.ofReal (actualExtendedThirdCompactKernelBound h) *
        volume (actualExtendedThirdWallStrip h a δ) := by simp
    _ ≤ ENNReal.ofReal (actualExtendedThirdCompactKernelBound h) *
        ENNReal.ofReal (δ * thirdPrefixRho ^ 2) :=
      mul_le_mul_right (actualExtendedThirdWallStrip_volume_le hh hδ) _
    _ = ENNReal.ofReal (actualExtendedThirdCompactKernelBound h * (δ * thirdPrefixRho ^ 2)) :=
      (ENNReal.ofReal_mul (actualExtendedThirdCompactKernelBound_pos hh).le).symm

/-- Finite absolute mass supplies genuine Bochner integrability of both
actual kernels on the strip. A divergent real integral is never used. -/
theorem integrableOn_actualExtendedThirdWallKernel (physical : Bool) {e h a δ : ℝ} {m : ℕ}
    (hh : 0 < h) (hδ : 0 ≤ δ) :
    IntegrableOn (actualExtendedThirdWallKernel physical e m) (actualExtendedThirdWallStrip h a δ) := by
  refine ⟨(measurable_actualExtendedThirdWallKernel physical e m).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [Real.norm_eq_abs, actualExtendedThirdWallMass] using
    lt_of_le_of_lt (actualExtendedThirdWallMass_le (e := e) (a := a) (m := m) physical hh hδ)
      ENNReal.ofReal_lt_top

/-- For this fixed h, the buffer and common mesh thresholds are chosen
after the tolerance. Both exact source strips use width 4e + mesh. -/
theorem actualExtendedThirdBoundaryStrips_uniform_small {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) :
    ∃ e₀ : ℝ, 0 < e₀ ∧ ∃ m₀ : ℕ, ∀ e : ℝ, 0 ≤ e → e ≤ e₀ →
      ∀ m : ℕ, m₀ ≤ m → ∀ physical : Bool,
        actualExtendedThirdWallMass physical e m h mu
            (4 * e + actualExtendedThirdDyadicStep m) ≤ ENNReal.ofReal ε ∧
          actualExtendedThirdWallMass physical e m h thirdPrefixRho
            (4 * e + actualExtendedThirdDyadicStep m) ≤ ENNReal.ofReal ε := by
  let C : ℝ := actualExtendedThirdCompactKernelBound h * thirdPrefixRho ^ 2
  have hC : 0 ≤ C := mul_nonneg (actualExtendedThirdCompactKernelBound_pos hh).le (sq_nonneg _)
  let δ : ℝ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (C + 1) = ε := by
    exact div_mul_cancel₀ _ (by positivity : C + 1 ≠ 0)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    (tendsto_actualExtendedThirdDyadicStep.eventually (gt_mem_nhds (half_pos hδ)))
  refine ⟨δ / 8, by positivity, m₀, ?_⟩
  intro e he0 he m hm physical
  have hwidth : 4 * e + actualExtendedThirdDyadicStep m ≤ δ := by linarith [hm₀ m hm]
  have hwidth0 : 0 ≤ 4 * e + actualExtendedThirdDyadicStep m :=
    add_nonneg (mul_nonneg (by norm_num) he0) (actualExtendedThirdDyadicStep_pos m).le
  have hnum : actualExtendedThirdCompactKernelBound h *
      ((4 * e + actualExtendedThirdDyadicStep m) * thirdPrefixRho ^ 2) ≤ ε := by
    calc
      _ = C * (4 * e + actualExtendedThirdDyadicStep m) := by dsimp [C]; ring
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hwidth hC
      _ = ε - δ := by nlinarith [hδeq]
      _ ≤ ε := sub_le_self _ hδ.le
  exact ⟨(actualExtendedThirdWallMass_le physical hh hwidth0).trans (ENNReal.ofReal_le_ofReal hnum),
    (actualExtendedThirdWallMass_le physical hh hwidth0).trans (ENNReal.ofReal_le_ofReal hnum)⟩

end

end ImbalancedChen
