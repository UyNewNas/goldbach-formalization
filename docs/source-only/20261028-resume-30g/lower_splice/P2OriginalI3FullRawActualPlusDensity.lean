import ImbalancedChen.P2OriginalMixedI3AllFrontierRosser
import ImbalancedChen.P2OriginalI3ProjectionAttachmentDefects
import ImbalancedChen.ActualFrozenFrontierDensity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
At a FULL (zero-lower-cutoff) actually reached mixed frontier, the real remaining
carrier is all target-deleted primes strictly below p3. Thus the established
old/new upper quotient polynomials are literally the original actual upper
Rosser densities. No equality of a y-separated carrier with this one is used.
-/
namespace ImbalancedChen.P2OriginalI3FullRawActualPlusDensity
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3ActualSmallRosserAttachment
open P2OriginalI3ReachedTraceRosserIff
open P2OriginalMixedI3AllFrontierRosser
open P2OriginalI3ProjectionAttachmentDefects

theorem reached_full_actual_plus_density {mesh : ℕ} (D : ThirdStage mesh)
    (N cap p1 p2 p3 : ℕ) (z : ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 3 (D.oldPolicy N)
      (fun p => 1 / ((p : ℝ)-1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (hpre : state.selectedPrefix = [p3,p2,p1]) (hN : 1 < (N : ℝ)) :
    let Qold := (N : ℝ)^(baselineCap D.rho)
    let Qnew := (N : ℝ)^(integerTrace D.thirdPlan (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho) N [p3,p2,p1]).cap
    firstExitRetainedPolynomial (D.newPolicy N) (fun p => 1 / ((p : ℝ)-1))
        [p3,p2,p1] state.positive state.mass state.remaining -
      firstExitRetainedPolynomial (D.oldPolicy N) (fun p => 1 / ((p : ℝ)-1))
        [p3,p2,p1] state.positive state.mass state.remaining =
      state.mass *
        (actualSmallRosserPlusDensity N cap (p3 : ℝ) (Qold / ([p3,p2,p1].prod : ℝ)) -
          actualSmallRosserPlusDensity N cap (p3 : ℝ) (Qnew / ([p3,p2,p1].prod : ℝ))) := by
  obtain ⟨hlen,hsort,hP,hcut,hrem,hsg,hmass⟩ := actualPrimeFrontier_geometry
    3 (by norm_num) (D.oldPolicy N) N cap z state hs
  have hrem' : state.remaining = roughPrimeUniverse N cap 0 (p3 : ℝ) := by
    simpa [hpre] using hrem
  have hc := reached_actual_I3_upper_continuations D N cap p1 p2 p3 0 z
    (fun p => 1 / ((p : ℝ)-1)) state hs hpre hN
  have hi0 := reached_actual_trace_admissible_iff D N cap p1 p2 p3 0 z
    (fun p => 1 / ((p : ℝ)-1)) state hs hpre hN [] (by simp)
  have hseed := reached_three_seed_retained D N cap p1 p2 p3 0 z
    (fun p => 1 / ((p : ℝ)-1)) state hs hpre
  have hnewret := new_trace_three_retained_of_seed D N p1 p2 p3 hseed
  have hnewadm := hi0.2.mp (by simpa using hnewret)
  have hP' : (0 : ℝ) < [p3,p2,p1].prod := by simpa only [hpre] using hP
  have hRold := ordinaryRosser_residual_level_gt_one true _ [p3,p2,p1] hi0.1 hP'
  have hRnew := ordinaryRosser_residual_level_gt_one true _ [p3,p2,p1] hnewadm hP'
  dsimp only at hc ⊢
  rw [hrem'] at hc
  rw [hrem']
  rw [firstExitRetainedPolynomial_eq_actualSmallRosserDensity false N cap (p3 : ℝ)
      _ hRold,
    firstExitRetainedPolynomial_eq_actualSmallRosserDensity false N cap (p3 : ℝ)
      _ hRnew] at hc
  simpa only [Bool.false_eq_true,if_false] using hc

/-- The computed source tag stays attached to every actual frontier term.
The residual levels are the frozen total levels divided by ALL three primes. -/
def actualFullI3PlusTerm {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ)
    (tag : FirstExitDepthState ℕ × Option P2OriginalLowerWholeBoxBranchSelect.SelectedBranchData) : ℝ :=
  let pre := tag.1.selectedPrefix
  let Qold := (N : ℝ)^(baselineCap D.rho)
  let Qnew := (N : ℝ)^(integerTrace D.thirdPlan (D.start.epsilon : ℝ)
    (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre).cap
  tag.1.mass *
    (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ) (Qold / (pre.prod : ℝ)) -
      actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ) (Qnew / (pre.prod : ℝ)))

/-- COMPLETE actual raw I3, including selected W, tent, failed-gate and
inherited cases. There is no all-W or adopted-policy coverage assumption. -/
theorem complete_raw_I3_eq_actual_plus_frontier {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (hN : 1 < (N : ℝ)) :
    rawDensity (thirdRetain D N) N cap 0 z -
      rawDensity (seedRetain D N) N cap 0 z =
      ((D.taggedFrontier N cap z (fun p => 1 / ((p : ℝ)-1))).map
        (actualFullI3PlusTerm D N cap)).sum := by
  rw [full_raw_I3_eq_actual_tagged_frontier]
  apply congrArg List.sum
  apply List.map_congr_left
  intro tag htag
  obtain ⟨state,hs,rfl⟩ := List.mem_map.mp htag
  have hlen : state.selectedPrefix.length = 3 :=
    firstExitDepthFrontier_selected_length 3 (D.oldPolicy N)
      (fun p => 1 / ((p : ℝ)-1)) [] (roughPrimeUniverse N cap 0 z)
      true 1 (by simp) state hs
  obtain ⟨p3,ps,h3,hl2⟩ := List.length_eq_succ_iff.mp hlen
  obtain ⟨p2,qs,h2,hl1⟩ := List.length_eq_succ_iff.mp hl2
  obtain ⟨p1,rs,h1,hl0⟩ := List.length_eq_succ_iff.mp hl1
  have hr : rs = [] := List.length_eq_zero_iff.mp hl0
  have hpre : state.selectedPrefix = [p3,p2,p1] := by rw [← h3,← h2,← h1,hr]
  have he := reached_full_actual_plus_density D N cap p1 p2 p3 z state hs hpre hN
  simpa [ThirdStage.frontierTerm,actualFullI3PlusTerm,hpre] using he

end
end ImbalancedChen.P2OriginalI3FullRawActualPlusDensity
