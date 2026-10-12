import ImbalancedChen.RosserEvenLogRegion
import ImbalancedChen.RosserOddTailIntegral
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserBoundarySourceSuccLayer

/-!
# Genuine even Rosser layer integrals

For residual level greater than one, the literal even boundary region lies
in a compact box bounded away from every coordinate hyperplane. Extracting
the largest and terminal coordinates gives the actual odd-tail boundary
mass integral. Slice integrability is obtained almost everywhere from
Fubini, not supplied as an additional analytic premise.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MeasureTheory Set
open MathlibNt.SieveTheory.LinearSieve

def rosserEvenLogDensity (k : ℕ) (x : Fin (2 * k + 2) → ℝ) : ℝ := ∏ i, 1 / x i

def rosserEvenKernel (k : ℕ) (x : Fin (2 * k + 2) → ℝ) : ℝ :=
  rosserEvenLogDensity k x * (1 / x (Fin.last (2 * k + 1)))

def rosserEvenLayerIntegral (k : ℕ) (s : ℝ) : ℝ :=
  ∫ x in rosserEvenLogRegion k s, rosserEvenKernel k x

theorem integrableOn_rosserEvenKernel_region {k : ℕ} {s : ℝ} (hs : 1 < s) :
    IntegrableOn (rosserEvenKernel k) (rosserEvenLogRegion k s) := by
  let B : Set (Fin (2 * k + 2) → ℝ) :=
    Set.univ.pi (fun _ => Set.Icc ((s - 1) / 3 ^ (k + 1)) 1)
  have hpos : 0 < (s - 1) / (3 : ℝ) ^ (k + 1) := by positivity
  have hrec (i : Fin (2 * k + 2)) : ContinuousOn (fun x => 1 / x i) B :=
    continuousOn_const.div (continuous_apply i).continuousOn (fun x hx =>
      (lt_of_lt_of_le hpos (Set.mem_pi.mp hx i trivial).1).ne')
  have hc : ContinuousOn (rosserEvenKernel k) B :=
    (continuousOn_finsetProd Finset.univ (fun i _ => hrec i)).mul (hrec _)
  exact (hc.integrableOn_compact (isCompact_rosserEvenLogBox k s)).mono_set
    (rosserEvenLogRegion_subset_positive_box k s hs)

/-- First and last coordinate extraction uses only integrability of the
original function, with the second extraction on almost-everywhere slices. -/
theorem integral_fin_first_last {n : ℕ} (f : (Fin (n + 2) → ℝ) → ℝ)
    (hf : Integrable f) :
    (∫ x, f x) = ∫ t : ℝ, ∫ q : ℝ, ∫ v : Fin n → ℝ,
      f (Fin.cons t (Fin.snoc v q)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove _ 0
  have hg : Integrable (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      f (Fin.cons z.1 z.2)) := by
    simpa [Function.comp_def, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv]
      using he.symm.integrable_comp_of_integrable hf
  rw [integral_fin_succ f hf]
  apply integral_congr_ae
  filter_upwards [hg.prod_right_ae] with t ht
  exact integral_fin_last (fun v => f (Fin.cons t v)) ht

theorem rosserEvenKernel_cons_snoc (k : ℕ) (t q : ℝ) (v : Fin (2 * k) → ℝ) :
    rosserEvenKernel k (Fin.cons t (Fin.snoc v q)) =
      t⁻¹ * (q⁻¹ * q⁻¹ * rosserOddTailDensity k v) := by
  unfold rosserEvenKernel rosserEvenLogDensity rosserOddTailDensity
  rw [Fin.prod_univ_succ]
  simp [Fin.prod_univ_castSucc, one_div]
  ring

theorem integral_rosserEvenKernel_slice (k : ℕ) (s t q : ℝ) (hs : 1 < s)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) t) :
    (∫ v : Fin (2 * k) → ℝ,
      (rosserEvenLogRegion k s).indicator (rosserEvenKernel k)
        (Fin.cons t (Fin.snoc v q))) =
      t⁻¹ * (q⁻¹ * q⁻¹ * upperRosserBoundaryMassAux k (s - t) q t) := by
  calc
    (∫ v : Fin (2 * k) → ℝ,
      (rosserEvenLogRegion k s).indicator (rosserEvenKernel k)
        (Fin.cons t (Fin.snoc v q))) =
        t⁻¹ * (q⁻¹ * q⁻¹ * rosserOddTailIntegral k (s - t) q t) := by
      change _ = t⁻¹ * (q⁻¹ * q⁻¹ *
        ∫ v in rosserOddTailRegion k (s - t) q t, rosserOddTailDensity k v)
      rw [← integral_indicator (measurableSet_rosserOddTailRegion k (s - t) q t),
        ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      by_cases hv : v ∈ rosserOddTailRegion k (s - t) q t
      · have hx := (mem_rosserEvenLogRegion_cons_snoc hs).mpr ⟨hq.1, hq.2, ht.2, hv⟩
        rw [indicator_of_mem hx, indicator_of_mem hv, rosserEvenKernel_cons_snoc]
      · have hx : Fin.cons t (Fin.snoc v q) ∉ rosserEvenLogRegion k s := by
          intro hx
          exact hv ((mem_rosserEvenLogRegion_cons_snoc hs).mp hx).2.2.2
        rw [indicator_of_notMem hx, indicator_of_notMem hv, mul_zero, mul_zero]
    _ = _ := by rw [rosserOddTailIntegral_eq_boundaryMassAux k (s - t) q t hq.1]

/-- This identifies the actual even-region integral with the inherited
odd-tail source integral, without a convergence or source-identity premise. -/
theorem rosserEvenLayerIntegral_eq_boundarySource (k : ℕ) (s : ℝ) (hs : 1 < s) :
    rosserEvenLayerIntegral k s =
      ∫ t in Ioo (0 : ℝ) 1, t⁻¹ * upperRosserBoundarySourceIntegral k (s - t) t := by
  have hi : Integrable ((rosserEvenLogRegion k s).indicator (rosserEvenKernel k)) :=
    (integrableOn_rosserEvenKernel_region hs).integrable_indicator
      (measurableSet_rosserEvenLogRegion k s)
  change (∫ x in rosserEvenLogRegion k s, rosserEvenKernel k x) = _
  rw [← integral_indicator (measurableSet_rosserEvenLogRegion k s),
    integral_fin_first_last _ hi, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem ht]
    unfold upperRosserBoundarySourceIntegral
    rw [← integral_indicator measurableSet_Ioo, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with q
    by_cases hq : q ∈ Ioo (0 : ℝ) t
    · rw [indicator_of_mem hq]
      exact integral_rosserEvenKernel_slice k s t q hs ht hq
    · rw [indicator_of_notMem hq, mul_zero]
      apply integral_eq_zero_of_ae
      filter_upwards [] with v
      apply indicator_of_notMem
      intro hx
      have hx' := (mem_rosserEvenLogRegion_cons_snoc hs).mp hx
      exact hq ⟨hx'.1, hx'.2.1⟩
  · rw [indicator_of_notMem ht]
    apply integral_eq_zero_of_ae
    filter_upwards [] with q
    apply integral_eq_zero_of_ae
    filter_upwards [] with v
    apply indicator_of_notMem
    intro hx
    have hx' := (mem_rosserEvenLogRegion_cons_snoc hs).mp hx
    exact ht ⟨hx'.1.trans hx'.2.1, hx'.2.2.1⟩

end

end ImbalancedChen
