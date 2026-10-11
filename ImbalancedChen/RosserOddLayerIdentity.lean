import ImbalancedChen.RosserOddTailIntegral
import ImbalancedChen.RosserOddMeshIntegral
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserBoundarySourceSuccLayer

/-!
# Exact identification of every fixed odd continuous Rosser layer

Extracting the terminal coordinate by measure-preserving Fubini turns the
actual odd-region Lebesgue integral into its genuine tail-region integral.
The proved tail recursion then identifies the boundary-mass supplier.
Suzuki's proved source identity applies on its stated residual interval.
No integral identity, convergence statement, or slice integrability is
assumed as an additional input.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MeasureTheory Set
open MathlibNt.SieveTheory.LinearSieve

theorem rosserOddKernel_snoc (k : ℕ) (v : Fin (2 * k) → ℝ) (q : ℝ) :
    rosserOddKernel k (Fin.snoc v q) = q⁻¹ * q⁻¹ * rosserOddTailDensity k v := by
  simp [rosserOddKernel, rosserOddLogDensity, rosserOddTailDensity,
    Fin.prod_univ_castSucc, one_div]
  ring

/-- At every positive terminal coordinate below one, the actual region
slice has exactly the supplier's boundary mass and terminal density. -/
theorem integral_rosserOddKernel_slice (k : ℕ) (s q : ℝ) (hs : 0 < s)
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    (∫ v : Fin (2 * k) → ℝ,
      (rosserOddLogRegion k s).indicator (rosserOddKernel k) (Fin.snoc v q)) =
      q⁻¹ * q⁻¹ * upperRosserBoundaryMass k s q := by
  calc
    (∫ v : Fin (2 * k) → ℝ,
        (rosserOddLogRegion k s).indicator (rosserOddKernel k) (Fin.snoc v q)) =
        q⁻¹ * q⁻¹ * rosserOddTailIntegral k s q 1 := by
      change _ = q⁻¹ * q⁻¹ * ∫ v in rosserOddTailRegion k s q 1, rosserOddTailDensity k v
      rw [← integral_indicator (measurableSet_rosserOddTailRegion k s q 1),
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      by_cases hv : v ∈ rosserOddTailRegion k s q 1
      · have hx : Fin.snoc v q ∈ rosserOddLogRegion k s :=
          (mem_rosserOddLogRegion_snoc hs).mpr ⟨hq.1, hq.2, hv⟩
        rw [indicator_of_mem hx, indicator_of_mem hv, rosserOddKernel_snoc]
      · have hx : Fin.snoc v q ∉ rosserOddLogRegion k s := by
          intro hx
          exact hv ((mem_rosserOddLogRegion_snoc hs).mp hx).2.2
        rw [indicator_of_notMem hx, indicator_of_notMem hv, mul_zero]
    _ = _ := by rw [rosserOddTailIntegral_eq_boundaryMassAux k s q 1 hq.1,
      upperRosserBoundaryMass]

/-- Every fixed odd-dimensional region integral equals the actual
recursive boundary-mass integral, for every positive residual level. -/
theorem rosserOddLayerIntegral_eq_boundaryMass (k : ℕ) (s : ℝ) (hs : 0 < s) :
    rosserOddLayerIntegral k s =
      ∫ q in Ioo (0 : ℝ) 1, q⁻¹ * q⁻¹ * upperRosserBoundaryMass k s q := by
  have hi : Integrable ((rosserOddLogRegion k s).indicator (rosserOddKernel k)) :=
    (integrableOn_rosserOddKernel_region hs).integrable_indicator
      (measurableSet_rosserOddLogRegion k s)
  change (∫ x in rosserOddLogRegion k s, rosserOddKernel k x) = _
  rw [← integral_indicator (measurableSet_rosserOddLogRegion k s),
    integral_fin_last _ hi, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hq]
    exact integral_rosserOddKernel_slice k s q hs hq
  · rw [indicator_of_notMem hq]
    apply integral_eq_zero_of_ae
    filter_upwards [] with v
    have hx : Fin.snoc v q ∉ rosserOddLogRegion k s := by
      intro hx
      have hx' := (mem_rosserOddLogRegion_snoc hs).mp hx
      exact hq ⟨hx'.1, hx'.2.1⟩
    exact indicator_of_notMem hx _

/-- On the provider's residual interval the genuine region integral is
Suzuki's actual odd source layer, including pair depth zero. -/
theorem rosserOddLayerIntegral_eq_suzukiLayer (k : ℕ) (s : ℝ)
    (hslo : 3 / 2 ≤ s) (hshi : s ≤ 4) :
    rosserOddLayerIntegral k s =
      MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer 1 2 (2 * k + 1) s := by
  rw [rosserOddLayerIntegral_eq_boundaryMass k s (by linarith)]
  exact MathlibNt.SieveTheory.SuzukiUpperRosserBoundarySourceLayerIdentity.of_succ
    suzukiUpperRosserBoundarySourceSuccLayerIdentity k s hslo hshi

/-- All fixed odd layers at residual three have their exact source identity. -/
theorem rosserOddLayerIntegral_at_three_eq_suzukiLayer (k : ℕ) :
    rosserOddLayerIntegral k 3 =
      MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer 1 2 (2 * k + 1) 3 :=
  rosserOddLayerIntegral_eq_suzukiLayer k 3 (by norm_num) (by norm_num)

/-- The zero-depth shell is empty at residual three. -/
theorem rosserOddLayerIntegral_zero_at_three : rosserOddLayerIntegral 0 3 = 0 := by
  rw [rosserOddLayerIntegral_eq_boundaryMass 0 3 (by norm_num)]
  exact integral_upperRosserBoundaryMass_eq_zero_of_pow_le 0 (by norm_num)

end

end ImbalancedChen
