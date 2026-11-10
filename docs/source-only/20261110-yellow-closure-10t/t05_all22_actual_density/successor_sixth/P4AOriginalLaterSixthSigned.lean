import ImbalancedChen.P4AOriginalLaterSixthStages
import ImbalancedChen.P4AOriginalSavedSixthSigned

/-! Signed same-node sixth residuals in each later stage, evaluated
on precisely the admitted prefixes of the common fifth tree. -/
namespace ImbalancedChen.P4AOriginalLaterSixthSigned
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFull87DataPolicy (fifthPolicy)
open P4AOriginalFull87OrdinarySignedGain (weight)
open P4AOriginalSavedSixthSigned (pre admitted rank_six_density)
open P4AOriginalLaterSixthStages (policy level gain even level_zero level_mono)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalVariableFifthPhysicalLedger (raw)

def value (k n : ℕ) (d : OriginalData) (N cap : ℕ) (p : Fin 6 → ℕ) :=
  actualPrimeTupleInitialSaving N cap (level n d N (pre p) k) (level n d N (pre p) (k+1)) p

theorem fifth_le_stage (k n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    P4AOriginalFull87DataPolicy.level5Exponent n d N (rosserAncestor 5 h)≤level n d N h k := by
  have hle := level_mono n d N h (Nat.zero_le k)
  rw [level_zero] at hle
  exact (P4AOriginalSavedSixthStage.fifth_le_level n d N h).trans
    ((P4AOriginalElevenSixthStage.saved_le_level n d N h).trans hle)

theorem stage_admissible (k n : ℕ) (d : OriginalData) (N cap : ℕ) (z : ℝ) (hN : 1≤(N:ℝ))
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 6 (fifthPolicy n d N) weight [] true 1 (roughPrimeUniverse N cap 0 z)) :
    ordinaryRosserPrefixAdmissible false ((N:ℝ)^level n d N s.selectedPrefix k) s.selectedPrefix :=
  ordinaryRosserPrefixAdmissible_mono false _ (Real.rpow_le_rpow_of_exponent_le hN
    (fifth_le_stage k n d N _)) (P4AOriginalSavedSixthFrontier.actual_fifth_at_six n d N cap 0 z weight s hs)

theorem signed_at_stage (k n : ℕ) (d : OriginalData) (N cap : ℕ) (z : ℝ) (hN : 1≤(N:ℝ)) :
    normalize N (raw (policy k n d N) N cap 0 z-raw (policy (k+1) n d N) N cap 0 z) =
      ∑ p∈admitted n d N cap z,(∏ i,weight (p i))*value k n d N cap p := by
  let S := fifthPolicy n d (N:ℝ)
  let Q := fun h => (N:ℝ)^level n d N h k
  let M := fun h => (N:ℝ)^level n d N h (k+1)
  let carrier := roughPrimeUniverse N cap 0 z
  have hx := firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum
    false 6 (by decide) S M Q N cap z (stage_admissible (k+1) n d N cap z hN)
      (stage_admissible k n d N cap z hN)
  change firstExitRetainedPolynomial (policy k n d N) _ _ _ _ _ -
    firstExitRetainedPolynomial (policy (k+1) n d N) _ _ _ _ _ = _ at hx
  rw [UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
       (even k n d N) N cap 0 z,
     UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
       (even (k+1) n d N) N cap 0 z] at hx
  change raw _ N cap 0 z - raw _ N cap 0 z = _ at hx
  unfold normalize
  rw [hx]
  let states := firstExitDepthFrontier 6 S weight [] true 1 carrier
  let term := fun s : FirstExitDepthState ℕ =>
    actualFrozenFrontierDensityTerm false N cap Q s.selectedPrefix -
    actualFrozenFrontierDensityTerm false N cap M s.selectedPrefix
  have hscale (l : List (FirstExitDepthState ℕ)) :
      (l.map term).sum * Real.log (N:ℝ)/singularSeries N =
      (l.map (fun s => term s*Real.log (N:ℝ)/singularSeries N)).sum := by
    induction l with
    | nil => simp
    | cons s l ih => simp only [List.map_cons,List.sum_cons,add_mul,add_div,ih]
  change (states.map term).sum * _ / _ = _
  rw [hscale,←firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 6 S weight carrier
    (roughPrimeUniverse_nodup N cap 0 z) (value k n d N cap)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  have hl := firstExitDepthFrontier_selected_length 6 S weight [] carrier true 1 (by simp) s hs
  have hp : pre (primeHistoryTuple 6 s.selectedPrefix)=s.selectedPrefix := primeHistoryTuple_reverse_ofFn hl
  dsimp only [term]
  rw [rank_six_density N cap Q _ hl,rank_six_density N cap M _ hl]
  simp only [value,actualPrimeTupleInitialSaving,hp,primeHistoryTuple_last (k:=5) hl,
    primeHistoryTuple_prod hl,Q,M,weight]
  ring

theorem original_gain (k n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) (hN : 1≤N) :
    let d := P4AOriginalNewFifthUnion.data e q a
    normalize N (gain k n d N) =
      ∑ p∈admitted n d N N (P4AOriginalFull87RawChronology.cutoff N),
        (∏ i,weight (p i))*value k n d N N p := by
  exact signed_at_stage k n _ N N _ (by exact_mod_cast hN)

end
end ImbalancedChen.P4AOriginalLaterSixthSigned
