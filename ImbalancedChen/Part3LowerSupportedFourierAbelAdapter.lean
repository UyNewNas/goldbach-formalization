import ImbalancedChen.Part3LowerSupportedDampingL2Limit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecificLimits.Basic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The angular Fourier unitary of a lower-supported raw L2 function is
identified with ANY pointwise Abel limit of its literal exp(-epsilon*u)
Fourier integrals. A native L2-convergent subsequence is constructed via
convergence in measure. No measurability, L2 membership, bound, unitary
identity or exchange of pointwise and L2 limits is assumed for the limit.
The convention is exp(-I*omega*u) and the measure is d omega/(2*pi).
-/

namespace ImbalancedChen.Part3.LowerSupportedFourierAbelAdapter20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open AngularFourierUnitary20261026b
open HeightMellinUnitary20261026b
open LowerSupportedExponentialDamping20261026b
open LowerSupportedDampingL2Limit20261026b

def abelSequence (n : ℕ) : ℝ := 1/((n : ℝ)+1)

theorem abelSequence_pos (n : ℕ) : 0<abelSequence n := by
  unfold abelSequence
  positivity

theorem abelSequence_tendsto : Tendsto abelSequence atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall (fun n => abelSequence_pos n)⟩

/-- The literal L1 Fourier integrals have an ACTUAL almost-everywhere
convergent subsequence, derived from native angular-unitary L2
convergence. The countable family of representative equalities is paid. -/
theorem exists_literal_fourier_abel_subsequence {G : ℝ → ℂ} {u0 : ℝ}
    (hG : MemLp G 2 volume) (hs : LowerSupported G u0) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂angularMeasure,
      Tendsto (fun n => angularTransform (damped (abelSequence (ns n)) G) ω) atTop
        (𝓝 (angularFourierUnitary (hG.toLp G) ω)) := by
  let F : ℕ → AngularL2 := fun n => angularFourierUnitary (dampedL2 hG hs (abelSequence n))
  have hconv : Tendsto F atTop (𝓝 (angularFourierUnitary (hG.toLp G))) :=
    (angularFourier_dampedL2_tendsto hG hs).comp abelSequence_tendsto
  obtain ⟨ns,hns,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have hf : ∀ n, F n =ᵐ[angularMeasure] angularTransform (damped (abelSequence n) G) :=
    fun n => angularFourier_dampedL2_ae hG hs (abelSequence_pos n)
  have hall : ∀ᵐ ω ∂angularMeasure,
      ∀ n, F n ω=angularTransform (damped (abelSequence n) G) ω := ae_all_iff.mpr hf
  refine ⟨ns,hns,?_⟩
  filter_upwards [hlim,hall] with ω hω hrep
  have he : (fun n => F (ns n) ω) =
      (fun n => angularTransform (damped (abelSequence (ns n)) G) ω) :=
    funext fun n => hrep (ns n)
  rwa [he] at hω

/-- Generic lower-supported Fourier/Abel identification. The limit k
is an arbitrary function; its measurability and L2 membership are NOT
premises. Actual pointwise Abel convergence is the only limit input. -/
theorem angularFourierUnitary_eq_ae_of_pointwise_abel_limit
    {G k : ℝ → ℂ} {u0 : ℝ} (hG : MemLp G 2 volume) (hs : LowerSupported G u0)
    (hk : ∀ ω : ℝ, Tendsto (fun ε : ℝ => angularTransform (damped ε G) ω)
      (𝓝[>] (0 : ℝ)) (𝓝 (k ω))) :
    angularFourierUnitary (hG.toLp G) =ᵐ[angularMeasure] k := by
  obtain ⟨ns,hns,hlim⟩ := exists_literal_fourier_abel_subsequence hG hs
  filter_upwards [hlim] with ω hω
  have hkseq := (hk ω).comp (abelSequence_tendsto.comp hns.tendsto_atTop)
  exact tendsto_nhds_unique hω hkseq

/-- The actual Abel limit is therefore an L2 representative of the
native angular unitary; these are proved conclusions, not assumptions. -/
theorem pointwise_abel_limit_memLp_and_unitary
    {G k : ℝ → ℂ} {u0 : ℝ} (hG : MemLp G 2 volume) (hs : LowerSupported G u0)
    (hk : ∀ ω : ℝ, Tendsto (fun ε : ℝ => angularTransform (damped ε G) ω)
      (𝓝[>] (0 : ℝ)) (𝓝 (k ω))) :
    ∃ hkm : MemLp k 2 angularMeasure,
      hkm.toLp k=angularFourierUnitary (hG.toLp G) ∧ ‖hkm.toLp k‖=‖hG.toLp G‖ := by
  have he := angularFourierUnitary_eq_ae_of_pointwise_abel_limit hG hs hk
  have hkm : MemLp k 2 angularMeasure :=
    (memLp_congr_ae he).mp (Lp.memLp (angularFourierUnitary (hG.toLp G)))
  have hclass : hkm.toLp k=angularFourierUnitary (hG.toLp G) :=
    Lp.ext (hkm.coeFn_toLp.trans he.symm)
  exact ⟨hkm,hclass,by rw [hclass,angularFourierUnitary.norm_map]⟩

end
end ImbalancedChen.Part3.LowerSupportedFourierAbelAdapter20261026b
