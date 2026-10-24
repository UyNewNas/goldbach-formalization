import ImbalancedChen.P5U7OriginalSourceMass
import ImbalancedChen.ActualPrimeIcoCellTestFunctions
import ImbalancedChen.CurrentChenUpsilon9HarmonicMean

/-!
SOURCE_ONLY / UNCOMPILED. A fixed positive interior margin for the original
U7 ordered pair. The source is the actual target-linked two-prime box: both
primes exclude divisors of N, and the logarithmic tests retain p1<p2 and
p1*p2^(2+eta)<N. No s-to-one boundary removal or rough-count error estimate
is made here. The double-prime test is transported to the genuine K=1
Buchstab integral on precisely this interior support.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory Set LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7InteriorForms (eta : ℝ) : Fin 2 → (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ![ContinuousLinearMap.proj 0 - ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 0 + (2 + eta) • ContinuousLinearMap.proj 1]

def p5U7InteriorBounds : Fin 2 → ℝ := ![0, 1]

def p5U7InteriorRegion (eta : ℝ) : Set (Fin 2 → ℝ) :=
  primeAffineGateRegion (p5U7InteriorForms eta) p5U7InteriorBounds

theorem p5U7InteriorRegion_iff (eta : ℝ) (x : Fin 2 → ℝ) :
    x ∈ p5U7InteriorRegion eta ↔
      x 0 < x 1 ∧ x 0 + (2 + eta) * x 1 < 1 := by
  constructor
  · intro h
    have h0 := h (0 : Fin 2)
    have h1 := h (1 : Fin 2)
    change x 0 - x 1 < 0 at h0
    change x 0 + (2 + eta) * x 1 < 1 at h1
    exact ⟨by linarith, h1⟩
  · rintro ⟨h0, h1⟩ j
    fin_cases j
    · change x 0 - x 1 < 0
      linarith
    · change x 0 + (2 + eta) * x 1 < 1
      exact h1

theorem p5U7InteriorForms_ne_zero (eta : ℝ) :
    ∀ j, p5U7InteriorForms eta j ≠ 0 := by
  intro j h
  have hh := congrArg (fun F : (Fin 2 → ℝ) →L[ℝ] ℝ => F ![1, 0]) h
  fin_cases j <;> norm_num [p5U7InteriorForms] at hh

/-- The original pair order and square-root wall follow from the stronger
fixed-eta interior gate; the upper wall remains strict. -/
theorem p5U7Interior_subset_original {eta : ℝ} (heta : 0 ≤ eta)
    {x : Fin 2 → ℝ}
    (hbox : x ∈ logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
      (fun _ => (1 / 2 : ℝ)))
    (hint : x ∈ p5U7InteriorRegion eta) :
    p5U7OmegaSupport (x 0) (x 1) := by
  have h0 := (mem_logPrimeBox.mp hbox) 0
  have h1 := (mem_logPrimeBox.mp hbox) 1
  obtain ⟨horder, hcap⟩ := (p5U7InteriorRegion_iff eta x).mp hint
  have hpos : 0 < x 1 := by linarith [h1.1]
  refine ⟨h0.1, horder.le, ?_⟩
  have hstrict : x 0 + 2 * x 1 < 1 := by linarith [mul_nonneg heta.le hpos.le]
  linarith

/-- The interior test is attached to the actual original ordered labels. -/
def p5U7InteriorSelector (N : ℕ) (eta : ℝ) : Finset (ℕ × ℕ) :=
  (chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).filter fun t =>
    actualPrimeTupleLog N ![t.1, t.2] ∈ p5U7InteriorRegion eta

private theorem p5U7Interior_log_order_iff {N p q : ℕ}
    (hN : 2 ≤ N) (hp : 0 < p) (hq : 0 < q) :
    actualPrimeTupleLog N ![p, q] 0 < actualPrimeTupleLog N ![p, q] 1 ↔ p < q := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  change Real.log (p : ℝ) / Real.log (N : ℝ) <
    Real.log (q : ℝ) / Real.log (N : ℝ) ↔ p < q
  rw [div_lt_div_iff_of_pos_right (Real.log_pos hNr),
    Real.log_lt_log_iff hpR hqR]
  exact Nat.cast_lt

/-- The fixed-margin filter of the original labelled selector is exactly
the target-linked two-prime box with the same logarithmic test. -/
theorem p5U7Interior_selector_iff_box {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta : 0 ≤ eta) (p : Fin 2 → ℕ) :
    (p 0, p 1) ∈ p5U7InteriorSelector N eta ↔
      p ∈ (actualPrimeBoxTuples N
        (fun _ : Fin 2 => (59 / 250 : ℝ)) (fun _ => (1 / 2 : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈ p5U7InteriorRegion eta) := by
  have hvec : ![p 0, p 1] = p := by
    funext i
    fin_cases i <;> rfl
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hpow : (N : ℝ) ^ (1 / 2 : ℝ) < N := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hNr (by norm_num : (1 / 2 : ℝ) < 1)
  constructor
  · intro ht
    obtain ⟨hsel, hint⟩ := Finset.mem_filter.mp ht
    obtain ⟨hc, hD, horder, hcap⟩ := Finset.mem_filter.mp hsel
    obtain ⟨hc0, hc1⟩ := Finset.mem_product.mp hc
    have hp0 := mem_chenAdditivePrimeCarrier.mp hc0
    have hp1 := mem_chenAdditivePrimeCarrier.mp hc1
    have hp0One : (1 : ℝ) ≤ p 0 := by exact_mod_cast hp0.2.1.one_le
    have hupper1 : (p 1 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        _ < Real.sqrt ((N : ℝ) / (p 0 : ℝ)) := hcap
        _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (div_le_self hNp.le hp0One)
        _ = _ := Real.sqrt_eq_rpow _
    have hupper0 : (p 0 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) :=
      (by exact_mod_cast horder : (p 0 : ℝ) < p 1).trans hupper1
    refine Finset.mem_filter.mpr ⟨mem_actualPrimeBoxTuples_iff.mpr ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨hp0.2.1, hp0.2.1.coprime_iff_not_dvd.mp hp0.2.2, hD, hupper0⟩
      · exact ⟨hp1.2.1, hp1.2.1.coprime_iff_not_dvd.mp hp1.2.2,
          hD.trans (by exact_mod_cast horder.le), hupper1⟩
    · simpa only [hvec] using hint
  · intro hp
    obtain ⟨hbox, hint⟩ := Finset.mem_filter.mp hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hbox
    have hp0 := hi (0 : Fin 2)
    have hp1 := hi (1 : Fin 2)
    have hpos : ∀ i, 0 < p i := fun i => (hi i).1.pos
    have hlogbox := ((mem_actualPrimeBoxTuples_log_iff
      (show 1 < N by omega) _ _ p).mp hbox).2
    have hregion := (p5U7InteriorRegion_iff eta (actualPrimeTupleLog N p)).mp hint
    have horder : p 0 < p 1 :=
      (p5U7Interior_log_order_iff hN (hpos 0) (hpos 1)).mp hregion.1
    have hstrict := p5U7Interior_subset_original heta hlogbox hint
    have hcaplog : actualPrimeTupleLog N p 0 +
        2 * actualPrimeTupleLog N p 1 < 1 := by linarith [hstrict.2.2]
    have hcap : (p 1 : ℝ) < Real.sqrt ((N : ℝ) / (p 0 : ℝ)) :=
      (currentChenUpsilon9_sqrt_log_iff hN (hpos 0) (hpos 1)).mpr hcaplog
    have hcarrier (i : Fin 2) : p i ∈ chenAdditivePrimeCarrier N := by
      apply mem_chenAdditivePrimeCarrier.mpr
      refine ⟨?_, (hi i).1, (hi i).1.coprime_iff_not_dvd.mpr (hi i).2.1⟩
      exact_mod_cast (hi i).2.2.2.trans hpow
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hcarrier 0, hcarrier 1⟩,
        hp0.2.2.1, horder, hcap⟩, ?_⟩
    simpa only [hvec] using hint

def p5U7InteriorTest (x : Fin 2 → ℝ) : ℝ :=
  buchstab ((1 - x 0 - x 1) / x 1) / x 1

theorem p5U7InteriorTest_continuousOn :
    ContinuousOn p5U7InteriorTest
      (Set.univ.pi (fun _ : Fin 2 => Icc (59 / 250 : ℝ) (1 / 2))) := by
  let C : Set (Fin 2 → ℝ) :=
    Set.univ.pi (fun _ : Fin 2 => Icc (59 / 250 : ℝ) (1 / 2))
  have hpos : ∀ x ∈ C, x 1 ≠ 0 := by
    intro x hx
    exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59 / 250)
      (hx 1 (Set.mem_univ _)).1).ne'
  have harg : ContinuousOn
      (fun x : Fin 2 → ℝ => (1 - x 0 - x 1) / x 1) C :=
    ((continuousOn_const.sub (continuous_apply 0).continuousOn).sub
      (continuous_apply 1).continuousOn).div
        (continuous_apply 1).continuousOn hpos
  exact (continuous_buchstab.comp_continuousOn harg).div
    (continuous_apply 1).continuousOn hpos

def p5U7InteriorDoubleTestSum (N : ℕ) (eta : ℝ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 2 => (59 / 250 : ℝ))
    (fun _ => (1 / 2 : ℝ))
    ((p5U7InteriorRegion eta).indicator p5U7InteriorTest)

def p5U7InteriorLabelledTestSum (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,
    (1 / ((t.1 : ℝ) - 1)) * (1 / ((t.2 : ℝ) - 1)) *
      p5U7InteriorTest (actualPrimeTupleLog N ![t.1, t.2])

/-- Exact finite reindexing, before the prime-limit theorem. Every original
ordered pair retains its label and target-N exclusion. -/
theorem p5U7InteriorLabelledTestSum_eq_box {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta : 0 ≤ eta) :
    p5U7InteriorLabelledTestSum N eta = p5U7InteriorDoubleTestSum N eta := by
  let T := (actualPrimeBoxTuples N
    (fun _ : Fin 2 => (59 / 250 : ℝ)) (fun _ => (1 / 2 : ℝ))).filter
      (fun p => actualPrimeTupleLog N p ∈ p5U7InteriorRegion eta)
  have heq : p5U7InteriorLabelledTestSum N eta =
      ∑ p ∈ T, (∏ i, 1 / ((p i : ℝ) - 1)) *
        p5U7InteriorTest (actualPrimeTupleLog N p) := by
    unfold p5U7InteriorLabelledTestSum
    refine Finset.sum_bij (fun t _ => ![t.1, t.2]) ?_ ?_ ?_ ?_
    · intro t ht
      exact (p5U7Interior_selector_iff_box hN heta ![t.1, t.2]).mp ht
    · intro t _ u _ htu
      apply Prod.ext
      · simpa using congrFun htu 0
      · simpa using congrFun htu 1
    · intro p hp
      refine ⟨(p 0, p 1),
        (p5U7Interior_selector_iff_box hN heta p).mpr hp, ?_⟩
      funext i
      fin_cases i <;> rfl
    · intro t _
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
  rw [heq]
  unfold p5U7InteriorDoubleTestSum actualPrimeBoxTestSum T
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : actualPrimeTupleLog N p ∈ p5U7InteriorRegion eta
  · rw [if_pos hp, indicator_of_mem hp]
  · rw [if_neg hp, indicator_of_notMem hp, mul_zero]

def p5U7InteriorOmegaIntegral (eta : ℝ) : ℝ :=
  ∫ x in logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
      (fun _ => (1 / 2 : ℝ)) ∩ p5U7InteriorRegion eta,
    p5U7OmegaKernel 1 (x 0) (x 1)

theorem p5U7Interior_test_density_eq_omega (eta : ℝ) :
    (∫ x in logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
        (fun _ => (1 / 2 : ℝ)) ∩ p5U7InteriorRegion eta,
      p5U7InteriorTest x * ∏ i, 1 / x i) =
        p5U7InteriorOmegaIntegral eta := by
  unfold p5U7InteriorOmegaIntegral
  apply setIntegral_congr_fun
    ((measurableSet_logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
      (fun _ => (1 / 2 : ℝ))).inter
      (measurableSet_primeAffineGateRegion (p5U7InteriorForms eta) p5U7InteriorBounds))
  intro x hx
  have h0 : 0 < x 0 := by
    have h := (mem_logPrimeBox.mp hx.1) 0
    linarith [h.1]
  have h1 : 0 < x 1 := by
    have h := (mem_logPrimeBox.mp hx.1) 1
    linarith [h.1]
  simp only [p5U7InteriorTest, p5U7OmegaKernel, p5U7OmegaArgument,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
  field_simp [h0.ne', h1.ne']
  <;> ring

/-- The fixed-eta interior double test has a genuine original Omega
integral limit. The arithmetic object is an actual two-prime sum, not a
surrogate density or an assumed mass limit. -/
theorem tendsto_p5U7InteriorDoubleTestSum (eta : ℝ) :
    Tendsto (fun N : ℕ => p5U7InteriorDoubleTestSum N eta) atTop
      (𝓝 (p5U7InteriorOmegaIntegral eta)) := by
  rw [← p5U7Interior_test_density_eq_omega eta]
  exact tendsto_actualPrimeBoxTestSum_cube_affineGates
    (by norm_num : (0 : ℝ) < 59 / 250)
    (by norm_num : (59 / 250 : ℝ) < 1 / 2)
    (p5U7InteriorForms eta) p5U7InteriorBounds
    (p5U7InteriorForms_ne_zero eta)
    p5U7InteriorTest p5U7InteriorTest_continuousOn

/-- Fixed positive-eta original labelled double-prime transport. The
rough-count boundary error and removal of this margin remain separate. -/
theorem tendsto_p5U7InteriorLabelledTestSum {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun N : ℕ => p5U7InteriorLabelledTestSum N eta) atTop
      (𝓝 (p5U7InteriorOmegaIntegral eta)) := by
  apply (tendsto_p5U7InteriorDoubleTestSum eta).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (p5U7InteriorLabelledTestSum_eq_box hN heta.le).symm

end

end ImbalancedChen
