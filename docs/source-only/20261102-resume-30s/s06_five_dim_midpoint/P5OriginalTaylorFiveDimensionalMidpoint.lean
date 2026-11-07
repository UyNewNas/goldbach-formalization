import ImbalancedChen.P5OriginalSignedMidpoint
import ImbalancedChen.FinitePiIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original five-dimensional box midpoint conversion. The private finite
coordinate induction only tensors the already proved one-dimensional
signed Peano bound. No new one-dimensional remainder proof is introduced.
Every integration below is genuine restricted Lebesgue integration.
-/

namespace ImbalancedChen.P5OriginalTaylorFiveDimensionalMidpoint
noncomputable section
open Set MeasureTheory
open scoped BigOperators Classical

private def closedBox {n : ℕ} (l u : Fin n → ℝ) : Set (Fin n → ℝ) := Icc l u

private theorem closedBox_eq_pi {n : ℕ} (l u : Fin n → ℝ) :
    closedBox l u = univ.pi (fun i => Icc (l i) (u i)) := by
  ext t
  simp only [closedBox, mem_Icc, mem_pi, mem_univ, forall_true_left]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩,
    fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

private theorem mem_closedBox {n : ℕ} {l u t : Fin n → ℝ} :
    t ∈ closedBox l u ↔ ∀ i, t i ∈ Icc (l i) (u i) := by
  rw [closedBox_eq_pi]
  simp

private theorem cons_mem_closedBox {n : ℕ} {l u : Fin (n+1) → ℝ}
    {a : ℝ} {t : Fin n → ℝ} (ha : a ∈ Icc (l 0) (u 0))
    (ht : t ∈ closedBox (fun i => l i.succ) (fun i => u i.succ)) :
    Fin.cons a t ∈ closedBox l u := by
  rw [mem_closedBox] at ht ⊢
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using ha
  · simpa using ht j

private theorem midpoint_mem {n : ℕ} {l u : Fin n → ℝ}
    (hlu : ∀ i, l i ≤ u i) :
    (fun i => (l i + u i)/2) ∈ closedBox l u := by
  rw [mem_closedBox]
  intro i
  constructor <;> linarith [hlu i]

private theorem update_cons_succ {n : ℕ} (a x : ℝ) (t : Fin n → ℝ) (i : Fin n) :
    Function.update (Fin.cons a t) i.succ x = Fin.cons a (Function.update t i x) := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · by_cases h : k = i
    · subst k
      simp
    · simp [Function.update, h, Ne.symm h]

/-- Restricted-product Fubini, including integrability of the outer integral.
This is only the coordinate dictionary needed in the finite midpoint proof. -/
private theorem box_fubini {n : ℕ} (l u : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hc : ContinuousOn f (closedBox l u)) :
    (∫ t in closedBox l u, f t) =
      ∫ a in Icc (l 0) (u 0),
        ∫ v in closedBox (fun i => l i.succ) (fun i => u i.succ), f (Fin.cons a v) ∧
    IntegrableOn (fun a =>
      ∫ v in closedBox (fun i => l i.succ) (fun i => u i.succ), f (Fin.cons a v))
      (Icc (l 0) (u 0)) := by
  let μ : Fin (n+1) → Measure ℝ := fun i => volume.restrict (Icc (l i) (u i))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have he : MeasurePreserving e (Measure.pi μ)
      ((μ 0).prod (Measure.pi (fun i : Fin n => μ i.succ))) := by
    simpa only [Fin.zero_succAbove] using measurePreserving_piFinSuccAbove μ 0
  have hf : Integrable f (Measure.pi μ) := by
    have h := hc.integrableOn_compact (show IsCompact (closedBox l u) from isCompact_Icc)
    rw [IntegrableOn, closedBox_eq_pi, volume_pi, Measure.restrict_pi_pi] at h
    exact h
  have hg : Integrable (fun z : ℝ × (Fin n → ℝ) => f (Fin.cons z.1 z.2))
      ((μ 0).prod (Measure.pi (fun i : Fin n => μ i.succ))) := by
    simpa [Function.comp_def, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using he.symm.integrable_comp_of_integrable hf
  have htail (a : ℝ) :
      (∫ v in closedBox (fun i => l i.succ) (fun i => u i.succ), f (Fin.cons a v)) =
        ∫ v, f (Fin.cons a v) ∂Measure.pi (fun i : Fin n => μ i.succ) := by
    rw [closedBox_eq_pi, volume_pi, Measure.restrict_pi_pi]
    rfl
  constructor
  · rw [closedBox_eq_pi, volume_pi, Measure.restrict_pi_pi]
    calc
      (∫ t, f t ∂Measure.pi μ) =
          ∫ z : ℝ × (Fin n → ℝ), f (Fin.cons z.1 z.2)
            ∂((μ 0).prod (Measure.pi (fun i : Fin n => μ i.succ))) := by
        simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
          using (he.symm.integral_comp' f).symm
      _ = ∫ a in Icc (l 0) (u 0),
          ∫ v in closedBox (fun i => l i.succ) (fun i => u i.succ), f (Fin.cons a v) := by
        simp_rw [htail]
        exact integral_prod _ hg
  · simp_rw [htail]
    exact hg.integral_prod_left

/-- Finite coordinate induction used only at dimension five below. Its
one-coordinate premise is supplied there by the existing Peano theorem,
not retained by any exported Taylor-integral terminal. -/
private theorem successive_midpoints (n : ℕ) (l u e : Fin n → ℝ)
    (f : (Fin n → ℝ) → ℝ) (hlu : ∀ i, l i ≤ u i)
    (hc : ContinuousOn f (closedBox l u))
    (haxis : ∀ t ∈ closedBox l u, ∀ i,
      (u i-l i) * (f (Function.update t i ((l i+u i)/2))-e i) ≤
        ∫ x in Icc (l i) (u i), f (Function.update t i x)) :
    (∏ i, u i-l i) * (f (fun i => (l i+u i)/2)-∑ i, e i) ≤
      ∫ t in closedBox l u, f t := by
  induction n generalizing l u e f with
  | zero =>
      have hb : closedBox l u = univ := by
        ext t
        simp [mem_closedBox]
      rw [hb, setIntegral_univ, integral_fin_zero]
      have hm : (fun i : Fin 0 => (l i+u i)/2) = Fin.elim0 := by
        ext i
        exact Fin.elim0 i
      simp [hm]
  | succ n ih =>
      let lt : Fin n → ℝ := fun i => l i.succ
      let ut : Fin n → ℝ := fun i => u i.succ
      let et : Fin n → ℝ := fun i => e i.succ
      let ct : Fin n → ℝ := fun i => (lt i+ut i)/2
      let V : ℝ := ∏ i : Fin n, ut i-lt i
      let E : ℝ := ∑ i : Fin n, et i
      have hV : 0 ≤ V := Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hlu i.succ))
      have hct : ct ∈ closedBox lt ut := midpoint_mem (fun i => hlu i.succ)
      have hslice (a : ℝ) (ha : a ∈ Icc (l 0) (u 0)) :
          ContinuousOn (fun v => f (Fin.cons a v)) (closedBox lt ut) := by
        exact hc.comp (by fun_prop) (fun v hv => cons_mem_closedBox ha hv)
      have htail (a : ℝ) (ha : a ∈ Icc (l 0) (u 0)) :
          V * (f (Fin.cons a ct)-E) ≤
            ∫ v in closedBox lt ut, f (Fin.cons a v) := by
        apply ih lt ut et (fun v => f (Fin.cons a v)) (fun i => hlu i.succ) (hslice a ha)
        intro t ht i
        simpa [lt, ut, et, update_cons_succ] using
          haxis (Fin.cons a t) (cons_mem_closedBox ha ht) i.succ
      have hcm : ContinuousOn (fun a => f (Fin.cons a ct)) (Icc (l 0) (u 0)) := by
        exact hc.comp (by fun_prop) (fun a ha => cons_mem_closedBox ha hct)
      have him := hcm.integrableOn_Icc
      have hlow := ((hcm.sub continuousOn_const).const_mul V).integrableOn_Icc
      obtain ⟨hFubini, hi⟩ := box_fubini l u f hc
      have hmono := setIntegral_mono_on hlow hi measurableSet_Icc htail
      have h0 := haxis (Fin.cons ((l 0+u 0)/2) ct)
        (cons_mem_closedBox (by constructor <;> linarith [hlu 0]) hct) 0
      have hup (x : ℝ) :
          Function.update (Fin.cons ((l 0+u 0)/2) ct) 0 x = Fin.cons x ct := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      simp_rw [hup] at h0
      rw [integral_const_mul, integral_sub him (integrableOn_const (isCompact_Icc.measure_ne_top))]
        at hmono
      have hconst : (∫ a in Icc (l 0) (u 0), E) = (u 0-l 0)*E := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hlu 0)]
        simp [intervalIntegral.integral_const, smul_eq_mul]
      rw [hconst] at hmono
      have hstep := mul_le_mul_of_nonneg_left h0 hV
      rw [hFubini]
      have hmid : (fun i => (l i+u i)/2) = Fin.cons ((l 0+u 0)/2) ct := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ, hmid]
      change (u 0-l 0)*V*(f (Fin.cons ((l 0+u 0)/2) ct)-(e 0+E)) ≤ _
      nlinarith only [hstep, hmono]

/-- The genuine five-dimensional integral, with its exact Lebesgue volume
and the original 1/24 diagonal remainder. No mixed derivative is used. -/
theorem five_dimensional_midpoint_lower
    (l u M : Fin 5 → ℝ) (f : (Fin 5 → ℝ) → ℝ)
    (f' f'' : (Fin 5 → ℝ) → Fin 5 → ℝ → ℝ)
    (hlu : ∀ i, l i ≤ u i)
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ t ∈ Icc l u, ∀ i, ∀ x ∈ Icc (l i) (u i),
      HasDerivAt (fun y => f (Function.update t i y)) (f' t i x) x)
    (hdd : ∀ t ∈ Icc l u, ∀ i, ∀ x ∈ Icc (l i) (u i),
      HasDerivAt (f' t i) (f'' t i x) x)
    (hcc : ∀ t ∈ Icc l u, ∀ i, ContinuousOn (f'' t i) (Icc (l i) (u i)))
    (hM : ∀ t ∈ Icc l u, ∀ i, ∀ x ∈ Icc (l i) (u i), |f'' t i x| ≤ M i) :
    (∏ i, u i-l i) *
        (f (fun i => (l i+u i)/2) - (∑ i, (u i-l i)^2*M i)/24) ≤
      ∫ t in Icc l u, f t := by
  have h := successive_midpoints 5 l u (fun i => (u i-l i)^2*M i/24)
    f hlu hc (by
      intro t ht i
      have hPeano := P5OriginalSignedMidpoint.midpoint_bounds (hlu i)
        (hd t ht i) (hdd t ht i) (hcc t ht i)
        (fun x hx => abs_le.mp (hM t ht i x hx))
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hlu i)]
      convert hPeano.1 using 1 <;> ring)
  convert h using 1
  rw [Finset.sum_div]

end
end ImbalancedChen.P5OriginalTaylorFiveDimensionalMidpoint

