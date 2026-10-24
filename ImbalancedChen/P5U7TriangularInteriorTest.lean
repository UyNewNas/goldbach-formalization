import ImbalancedChen.P5U7OriginalSourceMass
import ImbalancedChen.ActualPrimePolyhedralTestFunctions
import ImbalancedChen.CurrentChenUpsilon9HarmonicMean

/-!
# Original U7 ordered triangular prime test, on a fixed interior

SOURCE ONLY / UNCOMPILED. The source is the literal original ordered pair
`chenY7PrimeSelector`; the additional strict logarithmic wall only makes a
fixed interior truncation. The finite sum keeps each original marked pair.
There is no source-mass asymptotic, boundary removal, or PP hypothesis here.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory Set
open scoped Classical BigOperators

/-- A fixed interior of the original U7 ordered triangle. The first wall
is the actual strict `p₁<p₂`; the second lies inside the original strict
square-root wall. -/
def p5U7TriangularInteriorForms : Fin 2 → (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ![ContinuousLinearMap.proj 0 - ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 0 + (2 : ℝ) • ContinuousLinearMap.proj 1]

def p5U7TriangularInteriorBounds (eta : ℝ) : Fin 2 → ℝ := ![0, 1 - eta]

def p5U7TriangularInterior (eta : ℝ) : Set (Fin 2 → ℝ) :=
  primeAffineGateRegion p5U7TriangularInteriorForms
    (p5U7TriangularInteriorBounds eta)

theorem p5U7TriangularInteriorForms_ne_zero :
    ∀ j, p5U7TriangularInteriorForms j ≠ 0 := by
  intro j hj
  have h := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L ![1, 0]) hj
  fin_cases j <;> norm_num [p5U7TriangularInteriorForms] at h

theorem mem_p5U7TriangularInterior_iff (eta : ℝ) (x : Fin 2 → ℝ) :
    x ∈ p5U7TriangularInterior eta ↔
      x 0 < x 1 ∧ x 0 + 2 * x 1 < 1 - eta := by
  simp only [p5U7TriangularInterior, primeAffineGateRegion, mem_ofPred_eq,
    Fin.forall_fin_two, p5U7TriangularInteriorForms,
    p5U7TriangularInteriorBounds, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith

/-- The actual original pair selector, restricted by a fixed positive
interior logarithmic margin; no prime label is identified with a product. -/
def p5U7TriangularInteriorPairs (N : ℕ) (eta : ℝ) : Finset (ℕ × ℕ) :=
  (chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).filter fun t =>
    actualPrimeTupleLog N ![t.1, t.2] ∈ p5U7TriangularInterior eta

private theorem p5U7_log_order_iff {N : ℕ} (hN : 2 ≤ N)
    (p : Fin 2 → ℕ) (hp : ∀ i, 0 < p i) :
    actualPrimeTupleLog N p 0 < actualPrimeTupleLog N p 1 ↔ p 0 < p 1 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hNr
  change Real.log (p 0 : ℝ) / Real.log (N : ℝ) <
      Real.log (p 1 : ℝ) / Real.log (N : ℝ) ↔ p 0 < p 1
  rw [div_lt_div_iff_of_pos_right hlog,
    Real.log_lt_log_iff (by exact_mod_cast hp 0) (by exact_mod_cast hp 1)]
  exact Nat.cast_lt

/-- Exact ownership of the original ordered pair in the common logarithmic
prime box. The cube has half-open faces, while the strict diagonal and
the fixed interior wall are retained as actual arithmetic tests. -/
theorem p5U7TriangularInteriorPairs_tuple_mem_iff {N : ℕ} (hN : 2 ≤ N)
    (eta : ℝ) (heta : 0 ≤ eta) (p : Fin 2 → ℕ) :
    (p 0, p 1) ∈ p5U7TriangularInteriorPairs N eta ↔
      p ∈ (actualPrimeBoxTuples N (fun _ : Fin 2 => (59 / 250 : ℝ))
        (fun _ => (1 / 2 : ℝ))).filter
          (fun p => actualPrimeTupleLog N p ∈ p5U7TriangularInterior eta) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNr.le
  have hpow : (N : ℝ) ^ (1 / 2 : ℝ) < N := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hNr (by norm_num : (1 / 2 : ℝ) < 1)
  constructor
  · intro ht
    obtain ⟨hsel, hregion⟩ := Finset.mem_filter.mp ht
    obtain ⟨hc, hlo, horder, hcap⟩ := Finset.mem_filter.mp hsel
    obtain ⟨hc0, hc1⟩ := Finset.mem_product.mp hc
    have hp0 := mem_chenAdditivePrimeCarrier.mp hc0
    have hp1 := mem_chenAdditivePrimeCarrier.mp hc1
    have hp0one : (1 : ℝ) ≤ p 0 := by exact_mod_cast hp0.2.1.one_le
    have hupper1 : (p 1 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        _ < Real.sqrt ((N : ℝ) / (p 0 : ℝ)) := hcap
        _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (div_le_self hNp.le hp0one)
        _ = _ := Real.sqrt_eq_rpow _
    have hupper0 : (p 0 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) :=
      (by exact_mod_cast horder : (p 0 : ℝ) < p 1).trans hupper1
    refine Finset.mem_filter.mpr ⟨mem_actualPrimeBoxTuples_iff.mpr ?_, hregion⟩
    intro i
    fin_cases i
    · exact ⟨hp0.2.1, hp0.2.1.coprime_iff_not_dvd.mp hp0.2.2, hlo, hupper0⟩
    · exact ⟨hp1.2.1, hp1.2.1.coprime_iff_not_dvd.mp hp1.2.2,
        hlo.trans (by exact_mod_cast horder.le), hupper1⟩
  · intro hp
    obtain ⟨hbox, hregion⟩ := Finset.mem_filter.mp hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hbox
    have hpos : ∀ i, 0 < p i := fun i => (hi i).1.pos
    have horder : p 0 < p 1 :=
      (p5U7_log_order_iff hN p hpos).mp
        ((mem_p5U7TriangularInterior_iff eta _).mp hregion).1
    have hcaplog : actualPrimeTupleLog N p 0 +
        2 * actualPrimeTupleLog N p 1 < 1 := by
      have hh := ((mem_p5U7TriangularInterior_iff eta _).mp hregion).2
      linarith only [hh, heta]
    have hcap : (p 1 : ℝ) < Real.sqrt ((N : ℝ) / (p 0 : ℝ)) :=
      (currentChenUpsilon9_sqrt_log_iff hN (hpos 0) (hpos 1)).mpr hcaplog
    have hcarrier (i : Fin 2) : p i ∈ chenAdditivePrimeCarrier N := by
      apply mem_chenAdditivePrimeCarrier.mpr
      refine ⟨?_, (hi i).1, (hi i).1.coprime_iff_not_dvd.mpr (hi i).2.1⟩
      exact_mod_cast (hi i).2.2.2.trans hpow
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hcarrier 0, hcarrier 1⟩,
        (hi 0).2.2.1, horder, hcap⟩, hregion⟩

/-- A marked-pair test. Every occurrence of a literal original pair is
summed separately, including when a later rough quotient shares a product. -/
def p5U7TriangularInteriorTestSum (N : ℕ) (eta : ℝ)
    (f : (Fin 2 → ℝ) → ℝ) : ℝ :=
  ∑ t ∈ p5U7TriangularInteriorPairs N eta,
    (1 / ((t.1 : ℝ) - 1)) * (1 / ((t.2 : ℝ) - 1)) *
      f (actualPrimeTupleLog N ![t.1, t.2])

theorem p5U7TriangularInteriorTestSum_eq_primeBox {N : ℕ} (hN : 2 ≤ N)
    (eta : ℝ) (heta : 0 ≤ eta) (f : (Fin 2 → ℝ) → ℝ) :
    p5U7TriangularInteriorTestSum N eta f =
      actualPrimeBoxTestSum N (fun _ : Fin 2 => (59 / 250 : ℝ))
        (fun _ => (1 / 2 : ℝ))
        ((p5U7TriangularInterior eta).indicator f) := by
  let T := (actualPrimeBoxTuples N (fun _ : Fin 2 => (59 / 250 : ℝ))
    (fun _ => (1 / 2 : ℝ))).filter
      (fun p => actualPrimeTupleLog N p ∈ p5U7TriangularInterior eta)
  calc
    _ = ∑ p ∈ T, (∏ i, 1 / ((p i : ℝ) - 1)) * f (actualPrimeTupleLog N p) := by
      refine Finset.sum_bij (fun t _ => ![t.1, t.2]) ?_ ?_ ?_ ?_
      · intro t ht
        exact (p5U7TriangularInteriorPairs_tuple_mem_iff hN eta heta ![t.1,t.2]).mp ht
      · intro t _ u _ htu
        apply Prod.ext
        · simpa using congrFun htu 0
        · simpa using congrFun htu 1
      · intro p hp
        refine ⟨(p 0,p 1),
          (p5U7TriangularInteriorPairs_tuple_mem_iff hN eta heta p).mpr hp, ?_⟩
        funext i
        fin_cases i <;> rfl
      · intro t ht
        simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
    _ = _ := by
      unfold T actualPrimeBoxTestSum
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hr : actualPrimeTupleLog N p ∈ p5U7TriangularInterior eta
      · rw [if_pos hr, Set.indicator_of_mem hr]
      · rw [if_neg hr, Set.indicator_of_notMem hr, mul_zero]

/-- Continuous extension of the exact manuscript Omega integrand after
the two reciprocal prime weights have been taken out. -/
def p5U7TriangularOmegaTest (x : Fin 2 → ℝ) : ℝ :=
  x 0 * x 1 * p5U7OmegaKernel 1 (x 0) (x 1)

theorem p5U7TriangularOmegaTest_continuousOn_cube :
    ContinuousOn p5U7TriangularOmegaTest
      (Set.univ.pi (fun _ : Fin 2 => Icc (59 / 250 : ℝ) (1 / 2 : ℝ))) := by
  let C : Set (Fin 2 → ℝ) := Set.univ.pi
    (fun _ : Fin 2 => Icc (59 / 250 : ℝ) (1 / 2 : ℝ))
  have hpair : ContinuousOn (fun x : Fin 2 → ℝ => (x 0, x 1)) C :=
    ((continuous_apply 0).prodMk (continuous_apply 1)).continuousOn
  have hOmega : ContinuousOn
      (fun x : Fin 2 → ℝ => p5U7OmegaKernel 1 (x 0) (x 1)) C :=
    (p5U7Omega_kernel_continuousOn_positive 1).comp hpair (by
      intro x hx
      exact ⟨by linarith [(hx 0 (Set.mem_univ _)).1],
        by linarith [(hx 1 (Set.mem_univ _)).1]⟩)
  exact ((continuous_apply 0).continuousOn.mul
    (continuous_apply 1).continuousOn).mul hOmega

def p5U7TriangularInteriorOmegaIntegral (eta : ℝ) : ℝ :=
  ∫ x in logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
      (fun _ => (1 / 2 : ℝ)) ∩ p5U7TriangularInterior eta,
    p5U7OmegaKernel 1 (x 0) (x 1)

/-- Fixed-margin triangular transport of the literal marked pair test
to the original coefficient-one Omega kernel. This is an interior theorem;
it does not assert that the full original arithmetic mass has this limit. -/
theorem tendsto_p5U7TriangularInteriorOmegaTest (eta : ℝ) (heta : 0 ≤ eta) :
    Tendsto (fun N : ℕ =>
      p5U7TriangularInteriorTestSum N eta p5U7TriangularOmegaTest)
      atTop (𝓝 (p5U7TriangularInteriorOmegaIntegral eta)) := by
  have hlim := tendsto_actualPrimeBoxTestSum_cube_affineGates
    (by norm_num : (0 : ℝ) < 59 / 250)
    (by norm_num : (59 / 250 : ℝ) < 1 / 2)
    p5U7TriangularInteriorForms (p5U7TriangularInteriorBounds eta)
    p5U7TriangularInteriorForms_ne_zero p5U7TriangularOmegaTest
    p5U7TriangularOmegaTest_continuousOn_cube
  have hI : (∫ x in logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
      (fun _ => (1 / 2 : ℝ)) ∩ p5U7TriangularInterior eta,
      p5U7TriangularOmegaTest x * ∏ i, 1 / x i) =
      p5U7TriangularInteriorOmegaIntegral eta := by
    unfold p5U7TriangularInteriorOmegaIntegral
    apply setIntegral_congr_fun
      ((measurableSet_logPrimeBox _ _).inter
        (measurableSet_primeAffineGateRegion _ _))
    intro x hx
    have hbox := mem_logPrimeBox.mp hx.1
    have ht : x 0 ≠ 0 := ne_of_gt (by linarith [(hbox 0).1])
    have hu : x 1 ≠ 0 := ne_of_gt (by linarith [(hbox 1).1])
    simp only [p5U7TriangularOmegaTest, Fin.prod_univ_two]
    field_simp [ht, hu] <;> ring
  rw [← hI]
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (p5U7TriangularInteriorTestSum_eq_primeBox hN eta heta _).symm

end

end ImbalancedChen
