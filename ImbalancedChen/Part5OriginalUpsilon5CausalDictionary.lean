import ImbalancedChen.VariableEnvelopeConsequences
import ImbalancedChen.CurrentChenPairHarmonicMean
import ImbalancedChen.ActualRosserLowerLimit

/-!
Original U5 causal-level dictionary. SOURCE ONLY: never compiled.

The root occurrence in section 4 of global-chen-lower-completion-20261010
uses V=max(v(t),v(t+u),Lambda-3a/8), not the ordinary level 1/2.
Here u is the smaller prime coordinate and t the larger coordinate.
The exact strict triangle and all original rational constants are retained.

This proves finite geometric and integral identities. It does not identify
an arbitrary correction h with the adopted h248 table, prove its averaged
count semantics, or provide the same-coefficient compiled density estimate.
-/

namespace ImbalancedChen.Part5OriginalUpsilon5CausalDictionary

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open MathlibNt.SieveTheory

def a : ℝ := 417 / 5000
def h : ℝ := 19 / 125

/-- The two-label domain already used by the literal fifth selector. -/
def triangle : Set (Fin 2 → ℝ) :=
  logPrimeBox (fun _ : Fin 2 => a) (fun _ => h) ∩
    primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)

theorem mem_triangle {x : Fin 2 → ℝ} :
    x ∈ triangle ↔ a ≤ x 0 ∧ x 0 < x 1 ∧ x 1 < h := by
  simp only [triangle, mem_inter_iff, mem_currentChenPairOrderRegion,
    mem_logPrimeBox]
  constructor
  · rintro ⟨hx, h01⟩
    exact ⟨(hx 0).1, h01, (hx 1).2⟩
  · rintro ⟨h0, h01, h1⟩
    refine ⟨?_, h01⟩
    intro i
    fin_cases i
    · exact ⟨h0, h01.trans h1⟩
    · exact ⟨h0.trans h01.le, h1⟩

theorem measurableSet_triangle : MeasurableSet triangle :=
  (measurableSet_logPrimeBox _ _).inter
    (measurableSet_primeAffineGateRegion _ _)

/-- On U5, t<h<mu, so this is exactly the enhanced branch of the root. -/
def level (u t : ℝ) : ℝ :=
  max (VariableEnvelope.v t)
    (max (VariableEnvelope.v (t + u)) (VariableEnvelope.B a))

def residual (x : Fin 2 → ℝ) : ℝ := level (x 0) (x 1) - x 0 - x 1
def argument (x : Fin 2 → ℝ) : ℝ := residual x / a
def alpha (x : Fin 2 → ℝ) : ℝ := (1 - x 0 - x 1) / residual x

theorem original_cutoff_square : h < 2 * a := by norm_num [a, h]

/-- Exact enhanced level: its first branch remains the original v(t). -/
theorem level_bounds {u t : ℝ}
    (hu : a ≤ u) (hut : u ≤ t) (ht : t ≤ h) :
    (1 + t) / 2 ≤ level u t ∧ level u t ≤ (1 + t + u) / 2 := by
  have htmu : t ≤ VariableEnvelope.mu := by
    dsimp [h, VariableEnvelope.mu] at *
    linarith
  have hv : VariableEnvelope.v t = (1 + t) / 2 := by
    simpa only [VariableEnvelope.A] using VariableEnvelope.v_eq_A htmu
  have hu0 : 0 ≤ u := by dsimp [a] at hu; linarith
  constructor
  · unfold level
    rw [hv]
    exact le_max_left _ _
  · unfold level
    apply max_le
    · rw [hv]
      linarith
    · apply max_le
      · rw [VariableEnvelope.v_eq_min]
        exact (min_le_left _ _).trans (by dsimp [VariableEnvelope.A]; linarith)
      · dsimp [VariableEnvelope.B, VariableEnvelope.cap, a] at *
        linarith

/-- Explicit positive residual margins; these hold on the closed triangle. -/
theorem residual_bounds {x : Fin 2 → ℝ}
    (hu : a ≤ x 0) (hut : x 0 ≤ x 1) (ht : x 1 ≤ h) :
    (34 / 125 : ℝ) ≤ residual x ∧ residual x ≤ 2083 / 5000 := by
  obtain ⟨hl, hh⟩ := level_bounds hu hut ht
  have huhi : x 0 ≤ h := hut.trans ht
  have htlo : a ≤ x 1 := hu.trans hut
  dsimp [residual]
  dsimp [a, h] at *
  constructor <;> linarith

theorem residual_pos {x : Fin 2 → ℝ} (hx : x ∈ triangle) : 0 < residual x := by
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp hx
  exact lt_of_lt_of_le (by norm_num) (residual_bounds hu hut.le ht.le).1

/-- Both selected full-square gates hold at this actual enhanced level. -/
theorem selected_full_squares {x : Fin 2 → ℝ} (hx : x ∈ triangle) :
    2 * x 1 < level (x 0) (x 1) ∧
      x 1 + 2 * x 0 < level (x 0) (x 1) := by
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp hx
  have hv := (level_bounds hu hut.le ht.le).1
  have huhi : x 0 ≤ h := hut.le.trans ht.le
  dsimp [a, h] at *
  constructor <;> linarith

/-- The cutoff square is admitted with a strict, fixed margin. -/
theorem cutoff_square {x : Fin 2 → ℝ} (hx : x ∈ triangle) :
    x 0 + x 1 + 2 * a < level (x 0) (x 1) := by
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp hx
  have hR := (residual_bounds hu hut.le ht.le).1
  dsimp [residual, a] at *
  linarith

/-- The original enhanced U5 needs the canonical lower factor through s=5. -/
theorem argument_mem {x : Fin 2 → ℝ} (hx : x ∈ triangle) :
    argument x ∈ Icc (2 : ℝ) 5 := by
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp hx
  obtain ⟨hl, hh⟩ := residual_bounds hu hut.le ht.le
  have ha : 0 < a := by norm_num [a]
  constructor
  · apply (le_div_iff₀ ha).mpr
    dsimp [a]
    linarith
  · apply (div_le_iff₀ ha).mpr
    dsimp [a]
    linarith

/-- Parent alpha remains at least two at the actual enhanced physical level. -/
theorem alpha_ge_two {x : Fin 2 → ℝ} (hx : x ∈ triangle) : 2 ≤ alpha x := by
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp hx
  have hv := (level_bounds hu hut.le ht.le).2
  apply (le_div_iff₀ (residual_pos hx)).mpr
  dsimp [residual]
  linarith

/-- The residual cutoff is exactly a, before any rounding reserve. -/
theorem residual_div_argument {x : Fin 2 → ℝ} (hx : x ∈ triangle) :
    residual x / argument x = a := by
  have ha : a ≠ 0 := by norm_num [a]
  unfold argument
  field_simp [ha, (residual_pos hx).ne']

/-- The normalized classical lower amplitude, including its second interval. -/
def lowerAmplitude (s : ℝ) : ℝ :=
  s * suzukiContinuousLowerFactor s / (2 * Real.exp Real.eulerMascheroniConstant)

def kernel (corr : ℝ → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  4 * (lowerAmplitude (argument x) + corr (argument x)) / residual x

def canonicalKernel (corr : ℝ → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) / a) *
      suzukiContinuousLowerFactor (argument x) +
    4 * corr (argument x) / residual x

/-- Exact density normalization at the enhanced residual, for every correction.
There is no count-mean or correction-soundness premise in this identity. -/
theorem kernel_eq_canonical {x : Fin 2 → ℝ} (hx : x ∈ triangle)
    (corr : ℝ → ℝ) : kernel corr x = canonicalKernel corr x := by
  have ha : a ≠ 0 := by norm_num [a]
  have hR : residual x ≠ 0 := (residual_pos hx).ne'
  unfold kernel canonicalKernel lowerAmplitude argument
  rw [Real.exp_neg]
  field_simp [ha, hR, Real.exp_ne_zero] <;> ring

theorem lowerAmplitude_eq_log {s : ℝ} (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    lowerAmplitude s = Real.log (s - 1) := by
  rw [lowerAmplitude, suzukiContinuousLowerFactor_firstInterval_eq s hs hs4]
  field_simp [show s ≠ 0 by linarith, Real.exp_ne_zero] <;> ring

/-- The logarithmic formula is licensed only on its proper first interval. -/
theorem kernel_eq_log_of_argument_le_four {x : Fin 2 → ℝ}
    (hx : x ∈ triangle) (hx4 : argument x ≤ 4) (corr : ℝ → ℝ) :
    kernel corr x =
      4 * (Real.log (argument x - 1) + corr (argument x)) / residual x := by
  rw [kernel, lowerAmplitude_eq_log (argument_mem hx).1 hx4]

/-- A strict interior witness rules out silently using the first interval everywhere. -/
theorem second_interval_witness :
    (![9 / 100, 1 / 10] : Fin 2 → ℝ) ∈ triangle ∧
      argument (![9 / 100, 1 / 10] : Fin 2 → ℝ) = 675 / 139 ∧
      (4 : ℝ) < argument (![9 / 100, 1 / 10] : Fin 2 → ℝ) := by
  norm_num [mem_triangle, a, h, argument, residual, level,
    VariableEnvelope.v_eq_min, VariableEnvelope.A, VariableEnvelope.C,
    VariableEnvelope.B, VariableEnvelope.cap]

/-- A real integral of the original enhanced kernel, not a numerical endpoint. -/
def integral (corr : ℝ → ℝ) : ℝ :=
  ∫ x in triangle, kernel corr x * ∏ i, 1 / x i

/-- Exact integral dictionary with the original reciprocal-prime measure.
The equality needs no integrability assumption because the integrands agree. -/
theorem integral_eq_canonical (corr : ℝ → ℝ) :
    integral corr = ∫ x in triangle, canonicalKernel corr x * ∏ i, 1 / x i := by
  apply setIntegral_congr_fun measurableSet_triangle
  intro x hx
  rw [kernel_eq_canonical hx]

end

end ImbalancedChen.Part5OriginalUpsilon5CausalDictionary
