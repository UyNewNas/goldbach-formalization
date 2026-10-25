import ImbalancedChen.Part3Gamma0ActualShiftedFriedrichsResolvent
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Actual Gamma0 Yosida graph approximation for the native Friedrichs operator.
The maps B_n=(n+1)R_{n+1} converge strongly to the identity on the ACTUAL
quotient Hilbert space. On the dense range of the actual physical R the
resolvent identity bounds the error by ||g-Rg||/(n+1). A genuine uniform
contraction and the actual dense-range theorem extend this to every vector.

The bounded A_n=(n+1)(I-B_n) has graph realizations (B_n u,A_n u) in the
ACTUAL Friedrichs graph. For each u in its TRUE operator domain the inputs
and outputs converge strongly to (u,A_F u). These approximants are not
claimed to lie in the smooth core or in the minimal closed operator domain.
No desired strong convergence or graph approximation is an input premise.
-/

namespace ImbalancedChen.Part3.Gamma0ActualYosidaGraphApproximation20261025a

noncomputable section
open Filter Topology Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualShiftedFriedrichsResolvent20261025a

def yosidaParameter (n : ℕ) : ℝ := (n:ℝ)+1

theorem yosidaParameter_pos (n : ℕ) : 0<yosidaParameter n := by
  unfold yosidaParameter
  positivity

/-- Actual bounded approximate identity on the physical quotient space. -/
def actualYosidaSmoother (N : ℕ) [NeZero N] (n : ℕ) :
    QuotientL2 N →L[ℂ] QuotientL2 N :=
  ((yosidaParameter n:ℝ):ℂ) • actualGammaShiftedResolvent N (yosidaParameter n)

def actualYosidaOperator (N : ℕ) [NeZero N] (n : ℕ) :
    QuotientL2 N →L[ℂ] QuotientL2 N :=
  ((yosidaParameter n:ℝ):ℂ) • (1-actualYosidaSmoother N n)

theorem actualYosidaSmoother_norm_le_one (N : ℕ) [NeZero N] (n : ℕ) :
    ‖actualYosidaSmoother N n‖≤1 := by
  have ha := yosidaParameter_pos n
  calc
    _ = yosidaParameter n * ‖actualGammaShiftedResolvent N (yosidaParameter n)‖ := by
      rw [actualYosidaSmoother,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
    _ ≤ yosidaParameter n * (1/yosidaParameter n) :=
      mul_le_mul_of_nonneg_left (actualGammaShiftedResolvent_norm_le N ha) ha.le
    _ = 1 := mul_one_div_cancel ha.ne'

theorem actualYosidaSmoother_norm_le (N : ℕ) [NeZero N] (n : ℕ) (f : QuotientL2 N) :
    ‖actualYosidaSmoother N n f‖≤‖f‖ :=
  ((actualYosidaSmoother N n).le_opNorm f).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (actualYosidaSmoother_norm_le_one N n) (norm_nonneg f))

/-- This identity is obtained from the ACTUAL Friedrichs graph of Rg,
not from an assumed approximation theorem or a renamed whole-plane R. -/
theorem actualYosidaSmoother_range_error (N : ℕ) [NeZero N]
    (n : ℕ) (g : QuotientL2 N) :
    actualYosidaSmoother N n (actualGammaResolvent N g)-actualGammaResolvent N g=
      -actualGammaShiftedResolvent N (yosidaParameter n) (g-actualGammaResolvent N g) := by
  have h := actualGammaShiftedResolvent_on_domain N (yosidaParameter_pos n)
    (actualResolventPoint N g)
  rw [actualGammaFriedrichs_apply_resolvent] at h
  change actualGammaShiftedResolvent N (yosidaParameter n)
    (((yosidaParameter n:ℝ):ℂ) • actualGammaResolvent N g+
      (g-actualGammaResolvent N g))=actualGammaResolvent N g at h
  rw [map_add,map_smul] at h
  change ((yosidaParameter n:ℝ):ℂ) •
      actualGammaShiftedResolvent N (yosidaParameter n) (actualGammaResolvent N g)-
      actualGammaResolvent N g=_
  calc
    _ = (actualGammaResolvent N g-
      actualGammaShiftedResolvent N (yosidaParameter n) (g-actualGammaResolvent N g))-
        actualGammaResolvent N g :=
      congrArg (fun z : QuotientL2 N => z-actualGammaResolvent N g)
        (eq_sub_iff_add_eq.mpr h)
    _ = _ := by abel

theorem actualYosidaSmoother_range_error_norm_le (N : ℕ) [NeZero N]
    (n : ℕ) (g : QuotientL2 N) :
    ‖actualYosidaSmoother N n (actualGammaResolvent N g)-actualGammaResolvent N g‖≤
      (1/((n:ℝ)+1))*‖g-actualGammaResolvent N g‖ := by
  rw [actualYosidaSmoother_range_error,norm_neg]
  exact actualGammaShiftedResolvent_apply_norm_le N (yosidaParameter_pos n) _

theorem tendsto_actualYosidaSmoother_on_range (N : ℕ) [NeZero N] (g : QuotientL2 N) :
    Tendsto (fun n : ℕ => actualYosidaSmoother N n (actualGammaResolvent N g))
      atTop (𝓝 (actualGammaResolvent N g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))*‖g-actualGammaResolvent N g‖)
      atTop (𝓝 (0:ℝ)) := by
    simpa only [zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).mul tendsto_const_nhds
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => actualYosidaSmoother_range_error_norm_le N n g) hb

/-- Genuine strong convergence on ALL actual quotient L2 vectors. -/
theorem tendsto_actualYosidaSmoother (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    Tendsto (fun n : ℕ => actualYosidaSmoother N n f) atTop (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨y,hy,hnear⟩ := (actualGammaResolvent_denseRange N).exists_dist_lt f
    (show 0<epsilon/4 by positivity)
  obtain ⟨g,rfl⟩ := hy
  have hdiff : ‖f-actualGammaResolvent N g‖<epsilon/4 := by
    simpa only [dist_eq_norm] using hnear
  have hlimit : Tendsto (fun n : ℕ =>
      ‖actualYosidaSmoother N n (actualGammaResolvent N g)-actualGammaResolvent N g‖)
      atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self,norm_zero] using
      ((tendsto_actualYosidaSmoother_on_range N g).sub tendsto_const_nhds).norm
  have hrange : ∀ᶠ n : ℕ in atTop,
      ‖actualYosidaSmoother N n (actualGammaResolvent N g)-actualGammaResolvent N g‖<epsilon/2 :=
    hlimit.eventually (gt_mem_nhds (show (0:ℝ)<epsilon/2 by positivity))
  filter_upwards [hrange] with n hn
  rw [dist_eq_norm]
  have hsplit : actualYosidaSmoother N n f-f=
      (actualYosidaSmoother N n (f-actualGammaResolvent N g)-(f-actualGammaResolvent N g))+
        (actualYosidaSmoother N n (actualGammaResolvent N g)-actualGammaResolvent N g) := by
    rw [map_sub]
    abel
  calc
    _ ≤ ‖actualYosidaSmoother N n (f-actualGammaResolvent N g)-(f-actualGammaResolvent N g)‖+
        ‖actualYosidaSmoother N n (actualGammaResolvent N g)-actualGammaResolvent N g‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ ≤ (‖f-actualGammaResolvent N g‖+‖f-actualGammaResolvent N g‖)+
        ‖actualYosidaSmoother N n (actualGammaResolvent N g)-actualGammaResolvent N g‖ :=
      add_le_add_right ((norm_sub_le _ _).trans
        (add_le_add_right (actualYosidaSmoother_norm_le N n _) _)) _
    _ < epsilon := by linarith

/-- A TRUE operator-domain point, obtained by scalar closure of that
domain and the actual shifted resolvent range theorem. -/
def actualYosidaPoint (N : ℕ) [NeZero N] (n : ℕ) (u : QuotientL2 N) :
    (actualGammaFriedrichs N).domain :=
  ((yosidaParameter n:ℝ):ℂ) •
    actualShiftedResolventPoint N (yosidaParameter n) (yosidaParameter_pos n) u

theorem actualYosidaPoint_coe (N : ℕ) [NeZero N] (n : ℕ) (u : QuotientL2 N) :
    (actualYosidaPoint N n u:QuotientL2 N)=actualYosidaSmoother N n u := rfl

theorem actualGammaFriedrichs_actualYosidaPoint (N : ℕ) [NeZero N]
    (n : ℕ) (u : QuotientL2 N) :
    actualGammaFriedrichs N (actualYosidaPoint N n u)=actualYosidaOperator N n u := by
  change actualGammaFriedrichs N
    (((yosidaParameter n:ℝ):ℂ) • actualShiftedResolventPoint N (yosidaParameter n)
      (yosidaParameter_pos n) u)=_
  rw [map_smul,actualGammaFriedrichs_apply_shiftedResolvent]
  rfl

theorem actualYosida_mem_friedrichsGraph (N : ℕ) [NeZero N]
    (n : ℕ) (u : QuotientL2 N) :
    (actualYosidaSmoother N n u,actualYosidaOperator N n u)∈(actualGammaFriedrichs N).graph := by
  rw [← actualYosidaPoint_coe,← actualGammaFriedrichs_actualYosidaPoint]
  exact (actualGammaFriedrichs N).mem_graph (actualYosidaPoint N n u)

/-- On the genuine operator domain the bounded Yosida output equals
the same strongly convergent smoother applied to the ACTUAL output A_Fu. -/
theorem actualYosidaOperator_on_domain (N : ℕ) [NeZero N]
    (n : ℕ) (u : (actualGammaFriedrichs N).domain) :
    actualYosidaOperator N n (u:QuotientL2 N)=
      actualYosidaSmoother N n (actualGammaFriedrichs N u) := by
  have h := actualGammaShiftedResolvent_on_domain N (yosidaParameter_pos n) u
  rw [map_add,map_smul] at h
  have hs : (u:QuotientL2 N)-((yosidaParameter n:ℝ):ℂ) •
      actualGammaShiftedResolvent N (yosidaParameter n) (u:QuotientL2 N)=
        actualGammaShiftedResolvent N (yosidaParameter n) (actualGammaFriedrichs N u) := by
    apply sub_eq_iff_eq_add.mpr
    exact h.symm.trans (add_comm _ _)
  exact congrArg (fun z : QuotientL2 N => ((yosidaParameter n:ℝ):ℂ) • z) hs

theorem tendsto_actualYosidaOperator_on_domain (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    Tendsto (fun n : ℕ => actualYosidaOperator N n (u:QuotientL2 N))
      atTop (𝓝 (actualGammaFriedrichs N u)) := by
  simp_rw [actualYosidaOperator_on_domain]
  exact tendsto_actualYosidaSmoother N (actualGammaFriedrichs N u)

/-- Both coordinates converge in the ACTUAL physical graph topology. -/
theorem tendsto_actualYosida_graph_pair (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    Tendsto (fun n : ℕ =>
      (actualYosidaSmoother N n (u:QuotientL2 N),actualYosidaOperator N n (u:QuotientL2 N)))
      atTop (𝓝 ((u:QuotientL2 N),actualGammaFriedrichs N u)) :=
  (tendsto_actualYosidaSmoother N (u:QuotientL2 N)).prodMk_nhds
    (tendsto_actualYosidaOperator_on_domain N u)

end
end ImbalancedChen.Part3.Gamma0ActualYosidaGraphApproximation20261025a
