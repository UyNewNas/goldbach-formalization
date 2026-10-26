import ImbalancedChen.Part3ZeroModeLogTail
import ImbalancedChen.Part3CuspModePhysicalCoreForm

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Literal physical zero-horizontal-mode tail: dy Dirichlet energy and
dy/y^2 mass. The lower endpoint need not vanish. The quarter term has
the boundary correction -|f(Y)|^2/(2Y). No Gamma spectral claim.
-/

namespace ImbalancedChen.Part3.ZeroModePhysicalTailHardy20261026b
noncomputable section
open MeasureTheory Set
open RadialSchrodingerL2Form20261025a
open CuspModePhysicalCoreForm20261026a ZeroModeLogTail20261026b

def physicalTailMass (Y : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ y in Ioi Y, ‖f y‖ ^ 2 / y ^ 2
def physicalTailEnergy (Y : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ y in Ioi Y, ‖deriv f y‖ ^ 2

theorem heightChart_tail_range {a : ℝ} (ha : 0 < a) (R : ℝ) :
    heightChart a '' Ioi R = Ioi (heightChart a R) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (div_lt_div_iff_of_pos_right ha).mpr (Real.exp_lt_exp.mpr hr)
  · intro hy
    have hypos : 0 < y := lt_trans (heightChart_pos ha R) hy
    refine ⟨Real.log (a * y), ?_, ?_⟩
    · apply Real.exp_lt_exp.mp
      rw [Real.exp_log (mul_pos ha hypos)]
      exact (div_lt_iff₀ ha).mp hy
    · simp [heightChart, Real.exp_log (mul_pos ha hypos), ha.ne']

/-- Actual half-line Jacobian, with no integrability premise. -/
theorem physical_tail_substitution {a : ℝ} (ha : 0 < a) (R : ℝ) (g : ℝ → ℝ) :
    (∫ y in Ioi (heightChart a R), g y) =
      ∫ r in Ioi R, heightChart a r * g (heightChart a r) := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun r (_ : r ∈ Ioi R) => (heightChart_hasDerivAt ha r).hasDerivWithinAt)
    (heightChart_injective ha).injOn g
  rw [heightChart_tail_range ha R] at h
  simpa only [abs_of_pos (heightChart_pos ha _), smul_eq_mul] using h

theorem physical_tail_mass_log {a : ℝ} (ha : 0 < a) (R : ℝ) (T : RadialTest) :
    physicalTailMass (heightChart a R) (physicalLift a T.function) =
      tailMass R T.function := by
  unfold physicalTailMass tailMass
  rw [physical_tail_substitution ha]
  apply integral_congr_ae
  filter_upwards [] with r
  have hy := heightChart_pos ha r
  simp only [physicalLift, log_heightChart ha, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hy.le]
  field_simp [hy.ne']

theorem physical_tail_energy_log {a : ℝ} (ha : 0 < a) (R : ℝ) (T : RadialTest) :
    physicalTailEnergy (heightChart a R) (physicalLift a T.function) =
      tailShearEnergy R T.function := by
  unfold physicalTailEnergy tailShearEnergy
  rw [physical_tail_substitution ha]
  apply integral_congr_ae
  filter_upwards [] with r
  have hy := heightChart_pos ha r
  rw [physicalLift_deriv_chart ha]
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
    Real.sq_sqrt hy.le]
  field_simp [hy.ne']

theorem physical_tail_trace_log {a : ℝ} (ha : 0 < a) (R : ℝ) (T : RadialTest) :
    ‖physicalLift a T.function (heightChart a R)‖ ^ 2 / heightChart a R =
      ‖T.function R‖ ^ 2 := by
  have hy := heightChart_pos ha R
  simp only [physicalLift, log_heightChart ha, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hy.le]
  field_simp [hy.ne']

/-- Exact log-coordinate shear identity on the actual physical compact core. -/
theorem physical_tail_exact_shear {a : ℝ} (ha : 0 < a) (R : ℝ) (T : RadialTest) :
    physicalTailEnergy (heightChart a R) (physicalLift a T.function) =
      tailDerivativeEnergy R T.function +
        (1 / 4 : ℝ) * physicalTailMass (heightChart a R) (physicalLift a T.function) -
        ‖physicalLift a T.function (heightChart a R)‖ ^ 2 /
          (2 * heightChart a R) := by
  rw [physical_tail_energy_log ha, physical_tail_mass_log ha]
  have ht := physical_tail_trace_log ha R T
  have hs := compact_tail_shear_identity R T
  rw [show ‖physicalLift a T.function (heightChart a R)‖ ^ 2 /
      (2 * heightChart a R) = ‖T.function R‖ ^ 2 / 2 by
    rw [div_mul_eq_div_div, div_right_comm, ht]]
  exact hs

theorem physical_tail_hardy {a : ℝ} (ha : 0 < a) (R : ℝ) (T : RadialTest) :
    (1 / 4 : ℝ) * physicalTailMass (heightChart a R) (physicalLift a T.function) -
      ‖physicalLift a T.function (heightChart a R)‖ ^ 2 /
        (2 * heightChart a R) ≤
      physicalTailEnergy (heightChart a R) (physicalLift a T.function) := by
  have h := physical_tail_exact_shear ha R T
  have hn : 0 ≤ tailDerivativeEnergy R T.function :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

/-- Any specified physical height is available; the logarithmic scale is
independent of the horizontal Fourier frequency. -/
theorem physical_tail_hardy_at_height (Y : ℝ) (hY : 0 < Y) (T : RadialTest) :
    (1 / 4 : ℝ) * physicalTailMass Y (physicalLift Y⁻¹ T.function) -
      ‖physicalLift Y⁻¹ T.function Y‖ ^ 2 / (2 * Y) ≤
      physicalTailEnergy Y (physicalLift Y⁻¹ T.function) := by
  have h := physical_tail_hardy (inv_pos.mpr hY) 0 T
  simpa [heightChart] using h

end
end ImbalancedChen.Part3.ZeroModePhysicalTailHardy20261026b
