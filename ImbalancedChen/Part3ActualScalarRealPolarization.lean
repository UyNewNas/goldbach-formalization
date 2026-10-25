import ImbalancedChen.Part3ActualScalarMeasureQuadratic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Instances.RealVectorSpace

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Real polarization of the actual scalar spectral measures. Additivity is
derived from the actual parallelogram identity. Local boundedness supplies
continuity, and the pinned continuous-additive-map theorem supplies real
homogeneity. No bilinearity premise or projection law is assumed.
-/

namespace ImbalancedChen.Part3.ActualScalarRealPolarization20261025a

noncomputable section
open MeasureTheory Set
open scoped Topology
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualScalarMeasureQuadratic20261025a

def realPolar (B : Set ResolventSpectrum) (u v : HyperbolicL2) : ℝ :=
  (spectralQuadratic B (u + v) - spectralQuadratic B (u - v)) / 4

theorem quadratic_neg (B : Set ResolventSpectrum) (u : HyperbolicL2) :
    spectralQuadratic B (-u) = spectralQuadratic B u := by
  simpa using spectralQuadratic_smul B (-1 : ℂ) u

theorem quadratic_I (B : Set ResolventSpectrum) (u : HyperbolicL2) :
    spectralQuadratic B (Complex.I • u) = spectralQuadratic B u := by
  simpa using spectralQuadratic_smul B Complex.I u

theorem realPolar_symm (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    realPolar B u v = realPolar B v u := by
  have hn : spectralQuadratic B (v - u) = spectralQuadratic B (u - v) := by
    rw [← neg_sub u v, quadratic_neg]
  simp only [realPolar, add_comm u v, hn]

theorem realPolar_add_left (B : Set ResolventSpectrum) (x y z : HyperbolicL2) :
    realPolar B (x + y) z = realPolar B x z + realPolar B y z := by
  unfold realPolar
  have h1 := spectralQuadratic_parallelogram B (x + y + z) (x - z)
  have h2 := spectralQuadratic_parallelogram B (x + y - z) (x + z)
  have h3 := spectralQuadratic_parallelogram B (y + z) z
  have h4 := spectralQuadratic_parallelogram B (y - z) z
  abel_nf at h1 h2 h3 h4 ⊢
  linear_combination (-h1 + h2 + h3 - h4) / 8

theorem realPolar_add_right (B : Set ResolventSpectrum) (x y z : HyperbolicL2) :
    realPolar B x (y + z) = realPolar B x y + realPolar B x z := by
  rw [realPolar_symm B x, realPolar_add_left,
    realPolar_symm B y x, realPolar_symm B z x]

def realPolarAddHom (B : Set ResolventSpectrum) (v : HyperbolicL2) : HyperbolicL2 →+ ℝ :=
  AddMonoidHom.mk' (fun u => realPolar B u v) (realPolar_add_left B · · v)

theorem realPolar_neg_left (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    realPolar B (-u) v = -realPolar B u v :=
  (realPolarAddHom B v).map_neg u

theorem realPolar_neg_right (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    realPolar B u (-v) = -realPolar B u v := by
  rw [realPolar_symm B u, realPolar_neg_left, realPolar_symm B v]

/-- A rough bound is enough to establish continuity before any
Cauchy--Schwarz argument or real homogeneity is available. -/
theorem realPolar_abs_le (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    |realPolar B u v| ≤ (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
  have hp0 := spectralQuadratic_nonneg B (u + v)
  have hm0 := spectralQuadratic_nonneg B (u - v)
  have hp := spectralQuadratic_le_norm_sq B (u + v)
  have hm := spectralQuadratic_le_norm_sq B (u - v)
  have hn := parallelogram_law_with_norm ℂ u v
  have ha : |spectralQuadratic B (u + v) - spectralQuadratic B (u - v)| ≤
      spectralQuadratic B (u + v) + spectralQuadratic B (u - v) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  unfold realPolar
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
  nlinarith

theorem realPolar_continuous_left (B : Set ResolventSpectrum) (v : HyperbolicL2) :
    Continuous (realPolarAddHom B v) := by
  apply (realPolarAddHom B v).continuous_of_isBounded_nhds_zero
    (Metric.ball_mem_nhds (0 : HyperbolicL2) (by norm_num : (0 : ℝ) < 1))
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(1 + ‖v‖ ^ 2) / 2, ?_⟩
  rintro z ⟨u, hu, rfl⟩
  have hu' : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hb := realPolar_abs_le B u v
  change |realPolar B u v| ≤ _
  nlinarith [norm_nonneg u]

theorem realPolar_smul_left (B : Set ResolventSpectrum) (c : ℝ)
    (u v : HyperbolicL2) : realPolar B (c • u) v = c * realPolar B u v :=
  map_real_smul (realPolarAddHom B v) (realPolar_continuous_left B v) c u

theorem realPolar_smul_right (B : Set ResolventSpectrum) (c : ℝ)
    (u v : HyperbolicL2) : realPolar B u (c • v) = c * realPolar B u v := by
  rw [realPolar_symm B u, realPolar_smul_left, realPolar_symm B v]

theorem realPolar_self (B : Set ResolventSpectrum) (u : HyperbolicL2) :
    realPolar B u u = spectralQuadratic B u := by
  have h := spectralQuadratic_parallelogram B u u
  simp only [sub_self, spectralQuadratic_zero] at h
  unfold realPolar
  simp only [sub_self, spectralQuadratic_zero]
  linarith

theorem realPolar_I_I (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    realPolar B (Complex.I • u) (Complex.I • v) = realPolar B u v := by
  unfold realPolar
  rw [← smul_add, ← smul_sub, quadratic_I, quadratic_I]

theorem realPolar_I_swap (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    realPolar B (Complex.I • u) v = -realPolar B u (Complex.I • v) := by
  have h := realPolar_I_I B u (Complex.I • v)
  rw [smul_smul, Complex.I_mul_I, neg_one_smul, realPolar_neg_right] at h
  linarith

theorem realPolar_I_self (B : Set ResolventSpectrum) (u : HyperbolicL2) :
    realPolar B (Complex.I • u) u = 0 := by
  have h := realPolar_I_swap B u u
  rw [realPolar_symm B u] at h
  linarith

end
end ImbalancedChen.Part3.ActualScalarRealPolarization20261025a
