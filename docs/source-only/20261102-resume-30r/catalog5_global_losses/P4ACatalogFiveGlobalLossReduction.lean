import ImbalancedChen.P4ACatalogFiveHistoricalPairBoundaryPayment
import ImbalancedChen.P4ACatalogFiveOmittedOrderPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

All supplied payments concern the same OriginalData and the original
candidate occurrences. The complete coarseRow, compact omittedRow and
untrimmed historical-pair complement are now paid at arbitrary precision.
The ONLY term left in the resulting catalog-five identity is the explicit
small-third omittedRow sum. No theorem in this file assumes it vanishes.
Consequently this is not yet a full catalog-five or all-22 density supply.
-/

namespace ImbalancedChen.P4ACatalogFiveGlobalLossReduction
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P4AOriginalCausalHistory
open P4AOriginalRankThreeRestorationSource P4ACatalogFiveActualPairDecomposition
open P4ACatalogFiveCoarseWeightedPayment P4ACatalogFiveOmittedOrderPayment
open P4ACatalogFiveHistoricalPairBoundaryPayment P4AOriginalSecondPhysicalIntegral

def normalizedActualSaving (d : OriginalData) (N : ℕ) : ℝ :=
  -secondChange d (N:ℝ) weight (fun _ _ => 1) (carrier N) *
    Real.log (N:ℝ) / singularSeries N

def normalizedCoarseSum (d : OriginalData) (N : ℕ) : ℝ :=
  ((candidates d (N:ℝ) weight (carrier N)).map (fun s =>
    coarseRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N)).sum

def normalizedOmittedSum (d : OriginalData) (N : ℕ) : ℝ :=
  ((candidates d (N:ℝ) weight (carrier N)).map (fun s =>
    omittedRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N)).sum

private theorem normalize_sum (L : List (FirstExitDepthState ℕ))
    (f : FirstExitDepthState ℕ → ℝ) (a b : ℝ) :
    (L.map (fun s => f s*a/b)).sum = (L.map f).sum*a/b := by
  induction L with
  | nil => simp
  | cons s L ih => simp only [List.map_cons,List.sum_cons,ih]; ring

/-- Q's exact finite decomposition, with the manuscript normalization
distributed through the original occurrence sums. -/
theorem normalized_actual_identity (d : OriginalData) (N : ℕ) :
    normalizedActualSaving d N = normalizedHistoricalEndpoint d N +
      normalizedCoarseSum d N-normalizedOmittedSum d N := by
  rw [normalizedActualSaving,
    second_saving_eq_endpoint_add_actual_discrepancies d (N:ℝ) weight (fun _ _ => 1) (carrier N)]
  unfold normalizedCoarseSum normalizedOmittedSum normalizedHistoricalEndpoint
  rw [normalize_sum,normalize_sum]
  change (_+_-_)*Real.log (N:ℝ)/singularSeries N =
    _*Real.log (N:ℝ)/singularSeries N+_*Real.log (N:ℝ)/singularSeries N-
      _*Real.log (N:ℝ)/singularSeries N
  ring

theorem abs_normalizedCoarseSum_le (d : OriginalData) (N : ℕ) :
    |normalizedCoarseSum d N| ≤ coarseAbsoluteSum d N := by
  unfold normalizedCoarseSum coarseAbsoluteSum
  generalize candidates d (N:ℝ) weight (carrier N) = L
  induction L with
  | nil => simp
  | cons s L ih =>
      simp only [List.map_cons,List.sum_cons]
      exact (abs_add _ _).trans (add_le_add le_rfl ih)

/-- Three fully identified losses, plus one explicit unpaid tail.
No finite residual difference is assumed positive. -/
theorem actual_saving_plus_small_omission_error_le (d : OriginalData) (h : ℝ) (N : ℕ) :
    |normalizedActualSaving d N+smallOmittedSum d h N-physicalSaving| ≤
      |normalizedHistoricalEndpoint d N-physicalSaving|+
        coarseAbsoluteSum d N+compactOmittedAbsoluteSum d h N := by
  rw [normalized_actual_identity]
  have hcoarse := abs_normalizedCoarseSum_le d N
  have homit := omitted_sum_sub_small_abs_le d h N
  change |normalizedOmittedSum d N-smallOmittedSum d h N| ≤ _ at homit
  calc
    _ = |(normalizedHistoricalEndpoint d N-physicalSaving)+normalizedCoarseSum d N-
        (normalizedOmittedSum d N-smallOmittedSum d h N)| := by congr 1 <;> ring
    _ ≤ |(normalizedHistoricalEndpoint d N-physicalSaving)+normalizedCoarseSum d N|+
        |normalizedOmittedSum d N-smallOmittedSum d h N| := abs_sub _ _
    _ ≤ |normalizedHistoricalEndpoint d N-physicalSaving|+
        |normalizedCoarseSum d N|+|normalizedOmittedSum d N-smallOmittedSum d h N| :=
      add_le_add_right (abs_add _ _) _
    _ ≤ _ := add_le_add (add_le_add_left hcoarse _) homit

/-- Fixed h, then ONE positive common tolerance and ONE N0; afterwards
all original histories satisfying the displayed geometric widths and
omega=h. All analytic error conclusions are supplied by the preceding
proofs. This does not use the complete small-third tail as a premise. -/
theorem exists_actual_saving_approx_with_small_omission (h epsilon : ℝ)
    (hh : 0 < h) (hhrho : h < (19/96:ℝ)) (heps : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ d : OriginalData, d.omega = h →
        0 < (d.e:ℝ) → (d.e:ℝ) < (3/256:ℝ)/100 → d.chi < (d.e:ℝ)/10 →
        P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ d.chi →
        4*(d.e:ℝ)+P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta →
        (3/2:ℝ)*d.chi+2*(d.e:ℝ) ≤ delta →
        2*P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta →
      ∀ N : ℕ, N0 ≤ N → Even N →
        |normalizedActualSaving d N+smallOmittedSum d h N-physicalSaving| < epsilon := by
  have he3 : 0 < epsilon/3 := by positivity
  obtain ⟨dp,hdp,Np,hNp,hpair⟩ := exists_historical_endpoint_approx_integral (epsilon/3) he3
  obtain ⟨dc,hdc,Nc,hNc,hcoarse⟩ := exists_complete_coarseRow_payment h (epsilon/3) hh hhrho he3
  obtain ⟨do_,hdo,No,hNo,homit⟩ := exists_compact_omittedRow_payment h (epsilon/3) hh hhrho he3
  let delta := min dp (min dc do_)
  have hd : 0 < delta := lt_min hdp (lt_min hdc hdo)
  refine ⟨delta,hd,max Np (max Nc No),hNp.trans (le_max_left _ _),?_⟩
  intro d homega he hesmall hchi hmesh hp hc ho N hN hEven
  have hp' := hp.trans (min_le_left dp (min dc do_))
  have hc' := hc.trans ((min_le_right dp (min dc do_)).trans (min_le_left dc do_))
  have ho' := ho.trans ((min_le_right dp (min dc do_)).trans (min_le_right dc do_))
  have hpn := hpair d he.le hp' N ((le_max_left _ _).trans hN) hEven
  have hcn := hcoarse d (by rw [homega]) he hesmall hchi hc' N
    ((le_max_left Nc No).trans ((le_max_right _ _).trans hN)) hEven
  have hon := homit d (by rw [homega]) hmesh ho' N
    ((le_max_right Nc No).trans ((le_max_right _ _).trans hN)) hEven
  exact (actual_saving_plus_small_omission_error_le d h N).trans_lt (by linarith)

end
end ImbalancedChen.P4ACatalogFiveGlobalLossReduction
