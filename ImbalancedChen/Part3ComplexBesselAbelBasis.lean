import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# Positive-axis Abel constancy and explicit basis coefficients

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

For two genuine twice differentiable solutions of the same complex-order
modified Bessel equation, q times their Wronskian is constant. If it is
nonzero at q=1, any third genuine solution has explicit constant basis
coefficients computed at q=1. The proof differentiates the determinant
and uses connectedness of the positive half-line, then elementary linear
algebra. No final special-function identity or coefficient is a premise.
-/

namespace ImbalancedChen.Part3.ComplexBesselAbelBasis

noncomputable section
open Set Filter
open scoped Topology

def weightedWronskian (f g : ℝ → ℂ) (q : ℝ) : ℂ :=
  (q : ℂ) * (f q * deriv g q - deriv f q * g q)

def PositiveBesselSolution (ν : ℂ) (f : ℝ → ℂ) : Prop :=
  ∀ q : ℝ, 0 < q →
    HasDerivAt f (deriv f q) q ∧
    HasDerivAt (deriv f) (deriv (deriv f) q) q ∧
    (q : ℂ) ^ 2 * deriv (deriv f) q + (q : ℂ) * deriv f q -
      ((q : ℂ) ^ 2 + ν ^ 2) * f q = 0

/-- Abel's identity proved from the actual differential equations. -/
theorem weightedWronskian_hasDerivAt_zero {ν : ℂ} {f g : ℝ → ℂ}
    (hf : PositiveBesselSolution ν f) (hg : PositiveBesselSolution ν g)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (weightedWronskian f g) 0 q := by
  obtain ⟨hf₁, hf₂, hfODE⟩ := hf q hq
  obtain ⟨hg₁, hg₂, hgODE⟩ := hg q hq
  have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 q := by
    simpa only [Complex.ofReal_one] using (hasDerivAt_id q).ofReal_comp
  let D : ℂ := f q * deriv g q - deriv f q * g q +
    (q : ℂ) * (f q * deriv (deriv g) q - deriv (deriv f) q * g q)
  have hd : HasDerivAt (weightedWronskian f g) D q := by
    convert hid.mul ((hf₁.mul hg₂).sub (hf₂.mul hg₁)) using 1 <;>
      dsimp [weightedWronskian, D] <;> ring
  have hqD : (q : ℂ) * D = 0 := by
    dsimp [D]
    linear_combination (f q) * hgODE - (g q) * hfODE
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hD : D = 0 := (mul_eq_zero.mp hqD).resolve_left hqC
  simpa only [hD] using hd

/-- The same coefficient holds at every positive real argument. -/
theorem weightedWronskian_eq {ν : ℂ} {f g : ℝ → ℂ}
    (hf : PositiveBesselSolution ν f) (hg : PositiveBesselSolution ν g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    weightedWronskian f g a = weightedWronskian f g b := by
  have hd : DifferentiableOn ℝ (weightedWronskian f g) (Ioi (0 : ℝ)) := by
    intro q hq
    exact (weightedWronskian_hasDerivAt_zero hf hg hq).differentiableAt.differentiableWithinAt
  have hz : EqOn (deriv (weightedWronskian f g)) 0 (Ioi (0 : ℝ)) := by
    intro q hq
    exact (weightedWronskian_hasDerivAt_zero hf hg hq).deriv
  exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hd hz ha hb

/-- Explicit coefficient formula at q=1; it is a conclusion of Abel
constancy, not an assumed representation of the third solution. -/
theorem solution_eq_basis_at_one {ν : ℂ} {f g h : ℝ → ℂ}
    (hf : PositiveBesselSolution ν f) (hg : PositiveBesselSolution ν g)
    (hh : PositiveBesselSolution ν h)
    (hW : weightedWronskian f g 1 ≠ 0) {q : ℝ} (hq : 0 < q) :
    h q = (weightedWronskian h g 1 / weightedWronskian f g 1) * f q +
      (weightedWronskian f h 1 / weightedWronskian f g 1) * g q := by
  have hfg := weightedWronskian_eq hf hg (by norm_num : (0 : ℝ) < 1) hq
  have hhg := weightedWronskian_eq hh hg (by norm_num : (0 : ℝ) < 1) hq
  have hfh := weightedWronskian_eq hf hh (by norm_num : (0 : ℝ) < 1) hq
  field_simp [hW]
  rw [hfg, hhg, hfh]
  unfold weightedWronskian
  ring

/-- Nonzero Wronskian at one point supplies a genuine global basis on
q>0, with both coefficients selected before the varying argument. -/
theorem exists_unique_basis_coefficients {ν : ℂ} {f g h : ℝ → ℂ}
    (hf : PositiveBesselSolution ν f) (hg : PositiveBesselSolution ν g)
    (hh : PositiveBesselSolution ν h) (hW : weightedWronskian f g 1 ≠ 0) :
    ∃ A B : ℂ, (∀ q : ℝ, 0 < q → h q = A * f q + B * g q) ∧
      ∀ A' B' : ℂ, (∀ q : ℝ, 0 < q → h q = A' * f q + B' * g q) →
        A' = A ∧ B' = B := by
  let A := weightedWronskian h g 1 / weightedWronskian f g 1
  let B := weightedWronskian f h 1 / weightedWronskian f g 1
  have hab : ∀ q : ℝ, 0 < q → h q = A * f q + B * g q :=
    fun q hq => solution_eq_basis_at_one hf hg hh hW hq
  refine ⟨A, B, hab, ?_⟩
  intro A' B' hrep
  have h1 := hrep 1 (by norm_num)
  have hd : deriv h 1 = A' * deriv f 1 + B' * deriv g 1 := by
    have hcalc := (((hf 1 (by norm_num)).1.const_mul A').add
      ((hg 1 (by norm_num)).1.const_mul B'))
    have he : h =ᶠ[𝓝 (1 : ℝ)] (fun q => A' * f q + B' * g q) := by
      filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with q hq
      exact hrep q hq
    exact (hcalc.congr_of_eventuallyEq he).deriv
  constructor
  · dsimp [A]
    apply (eq_div_iff hW).mpr
    simp only [weightedWronskian, Complex.ofReal_one, one_mul]
    rw [h1, hd]
    ring
  · dsimp [B]
    apply (eq_div_iff hW).mpr
    simp only [weightedWronskian, Complex.ofReal_one, one_mul]
    rw [h1, hd]
    ring

end

end ImbalancedChen.Part3.ComplexBesselAbelBasis
