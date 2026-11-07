import ImbalancedChen.P4AOriginalSaving19BankExhaustion
import ImbalancedChen.P2OriginalSaving19SourceMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The existing rational bank's omitted ORIGINAL saving19 density tends to
zero. This is a real-integral theorem on the actual13 domains, not an
arithmetic prime mean, old-policy gain preservation or beta compiler
estimate. Both historical global reserves remain separate and unpaid.
-/

namespace ImbalancedChen.P2OriginalSaving19BankIntegral

noncomputable section
open Filter Set MeasureTheory
open scoped Classical BigOperators Topology
open P2OriginalThirdMinorantLogDictionarySourceOnly
open OriginalAscendingThirteenCellOwnership
open P4AOriginalSaving19BankExhaustion P2OriginalSaving19SourceMeasure
open P4AOriginalCell0HalfOpenPrimeCarrier P4AOriginalLive171819PrimeBank

theorem bankRegion_measurable (i : Fin 13) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) :
    MeasurableSet (bankRegion i e chi m omega) := by
  have heq : bankRegion i e chi m omega =
      ⋃ j ∈ bank (.ascending19 i) e chi m omega,
        logPrimeMeshCell 0 (19 / 96) m j := by
    ext t
    simp only [bankRegion, mem_setOf_eq, mem_iUnion, exists_prop]
  rw [heq]
  exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion
    (fun _ => measurableSet_logPrimeMeshCell 0 (19 / 96) m j))

/-- Applies to signed integrable tests as well as positive savings.
Integrability is explicit for a general test and discharged below for
the actual original density. No convergence assumption is accepted. -/
theorem tendsto_bankIntegral (i : Fin 13) (e : ℚ) (he : e ≤ 1 / 1536)
    (chi : ℝ) (hchi : 0 < chi) (omega : ℝ) (homega : omega ≤ 1 / 100)
    (f : Point → ℝ) (hf : IntegrableOn f (cell i)) :
    Tendsto (fun m : ℕ => ∫ t in bankRegion i e chi m omega, f t) atTop
      (𝓝 (∫ t in cell i, f t)) := by
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (cell i))
    (F := fun m => (bankRegion i e chi m omega).indicator f) (f := f)
    (fun t => ‖f t‖)
    (fun m => (hf.indicator (bankRegion_measurable i e chi m omega)).aestronglyMeasurable)
    hf.norm
    (fun m => Eventually.of_forall
      (fun t => norm_indicator_le_norm_self (s := bankRegion i e chi m omega) f t))
    (show ∀ᵐ t ∂volume.restrict (cell i),
        Tendsto (fun m => (bankRegion i e chi m omega).indicator f t) atTop (𝓝 (f t)) from by
      filter_upwards [ae_restrict_mem (cell_measurable i)] with t ht
      apply tendsto_const_nhds.congr'
      filter_upwards [original_eventually_bankRegion i e he chi hchi omega homega t ht] with m hm
      simp only [indicator_of_mem hm])
  have hinter (m : ℕ) : cell i ∩ bankRegion i e chi m omega = bankRegion i e chi m omega :=
    Set.inter_eq_right.mpr (bankRegion_subset_original i e chi m omega)
  simpa only [setIntegral_indicator (bankRegion_measurable i e chi _ omega), hinter] using hlim

/-- Genuine source-specific omitted-density convergence. Neither the
28918 floor endpoint nor a bank approximation estimate is a premise. -/
theorem tendsto_original_density_bank (i : Fin 13) (e : ℚ) (he : e ≤ 1 / 1536)
    (chi : ℝ) (hchi : 0 < chi) (omega : ℝ) (homega : omega ≤ 1 / 100) :
    Tendsto (fun m : ℕ => ∫ t in bankRegion i e chi m omega, conservativeDensity t) atTop
      (𝓝 (∫ t in cell i, conservativeDensity t)) :=
  tendsto_bankIntegral i e he chi hchi omega homega conservativeDensity (cell_density_integrable i)

/-- All thirteen original indices occur once. This is a sum of actual
source integrals, never the sum of two complete numerical enclosures. -/
def bankSaving (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) : ℝ :=
  ∑ i : Fin 13, ∫ t in bankRegion i e chi m omega, conservativeDensity t

theorem tendsto_bankSaving (e : ℚ) (he : e ≤ 1 / 1536)
    (chi : ℝ) (hchi : 0 < chi) (omega : ℝ) (homega : omega ≤ 1 / 100) :
    Tendsto (fun m => bankSaving e chi m omega) atTop (𝓝 selectedSaving) := by
  rw [selectedSaving_eq_sum_cells]
  exact tendsto_finset_sum Finset.univ
    (fun i _ => tendsto_original_density_bank i e he chi hchi omega homega)

/-- A single mesh threshold pays any prescribed positive REAL saving19
omission allowance. The threshold follows e,chi,omega and precedes N.
This theorem spends neither of the two manuscript global reserves. -/
theorem exists_common_density_mesh (e : ℚ) (he : e ≤ 1 / 1536)
    (chi : ℝ) (hchi : 0 < chi) (omega : ℝ) (homega : omega ≤ 1 / 100)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, |selectedSaving - bankSaving e chi m omega| < ε := by
  have hzero : Tendsto (fun m => |selectedSaving - bankSaving e chi m omega|) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds.sub (tendsto_bankSaving e he chi hchi omega homega)).abs
    simpa only [sub_self, abs_zero] using h
  exact eventually_atTop.mp (hzero.eventually (gt_mem_nhds hε))

end
end ImbalancedChen.P2OriginalSaving19BankIntegral
