import ImbalancedChen.P5ZU1011OriginalSixteenTightRationalIntegralCertificates
import ImbalancedChen.P5ZU1011OriginalSixteenEligibilityGridCompleteness

/-!
# Actual grid-owner limits and eventual source/eligibility decisions

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The owner is selected from the proved generated Ico cover and is unique.
Both rational corners converge to the point. Fixed signed affine endpoint
values therefore converge to their actual affine value. At every point
off the SAME actual source and eligibility walls, the concrete generated
source tests and ALL16 correlated eligibility tests eventually decide the
actual point correctly. The eligibility non-wall condition is proved AE
from the actual proper finite wall family, never supplied as hBoundary.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenTightGridLocalGeometry

noncomputable section

open Set MeasureTheory Filter Topology U11Integral
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSourceGeometryMesh
open P2OriginalFourthCapProducerInterface
open scoped BigOperators
open Classical

def owner (n : ℕ) (v : LogFour) : Index n :=
  if hv : v ∈ cube then
    Classical.choose (exists_logPrimeMeshCell (a : ℝ) (b : ℝ) n hv)
  else fun _ => 0

theorem owner_mem (n : ℕ) {v : LogFour} (hv : v ∈ cube) : v ∈ cell n (owner n v) := by
  rw [cell_eq_generic]
  simp only [owner, dif_pos hv]
  exact Classical.choose_spec (exists_logPrimeMeshCell (a : ℝ) (b : ℝ) n hv)

theorem owner_unique (n : ℕ) {v : LogFour} (hv : v ∈ cube) {j : Index n}
    (hj : v ∈ cell n j) : j = owner n v := cell_unique hj (owner_mem n hv)

theorem owner_width (n : ℕ) (v : LogFour) : WidthLe (gridBox n (owner n v)) (step n : ℝ) := by
  intro i
  have h : ((gridBox n (owner n v)).hi i : ℝ) - ((gridBox n (owner n v)).lo i : ℝ) =
      (step n : ℝ) := by exact_mod_cast corner_difference n (owner n v) i
  exact h.le

theorem tendsto_step : Tendsto (fun n : ℕ => (step n : ℝ)) atTop (𝓝 0) := by
  simpa only [step, logPrimeMeshStep, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast] using
    tendsto_logPrimeMeshStep (a : ℝ) (b : ℝ)

theorem owner_lo_tendsto {v : LogFour} (hv : v ∈ cube) (i : Fin 4) :
    Tendsto (fun n => ((gridBox n (owner n v)).lo i : ℝ)) atTop (𝓝 (v i)) := by
  have hm (n : ℕ) : v ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) n (owner n v) := by
    simpa only [cell_eq_generic] using owner_mem n hv
  simpa only [gridBox, point_cast, logPrimeMeshLo] using
    tendsto_logPrimeMeshLo_apply (a : ℝ) (b : ℝ) (fun n => owner n v) hm i

theorem owner_hi_tendsto {v : LogFour} (hv : v ∈ cube) (i : Fin 4) :
    Tendsto (fun n => ((gridBox n (owner n v)).hi i : ℝ)) atTop (𝓝 (v i)) := by
  have hm (n : ℕ) : v ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) n (owner n v) := by
    simpa only [cell_eq_generic] using owner_mem n hv
  simpa only [gridBox, point_cast, logPrimeMeshHi] using
    tendsto_logPrimeMeshHi_apply (a : ℝ) (b : ℝ) (fun n => owner n v) hm i

/-- A true endpoint-limit lemma for a fixed rational affine expression;
it follows from finite sums, not from an assumed cell-bound conclusion. -/
theorem affine_lower_tendsto (A : Affine) {v : LogFour} (hv : v ∈ cube) :
    Tendsto (fun n => (A.lower (gridBox n (owner n v)).lo
      (gridBox n (owner n v)).hi : ℝ)) atTop (𝓝 (A.eval v)) := by
  have ht (i : Fin 4) : Tendsto (fun n =>
      ((if 0 ≤ A.coefficient i then A.coefficient i * (gridBox n (owner n v)).lo i
        else A.coefficient i * (gridBox n (owner n v)).hi i : ℚ) : ℝ))
      atTop (𝓝 ((A.coefficient i : ℝ) * v i)) := by
    by_cases hc : 0 ≤ A.coefficient i
    · simpa only [if_pos hc, Rat.cast_mul] using
        (owner_lo_tendsto hv i).const_mul (A.coefficient i : ℝ)
    · simpa only [if_neg hc, Rat.cast_mul] using
        (owner_hi_tendsto hv i).const_mul (A.coefficient i : ℝ)
  have hs := tendsto_finsetSum (Finset.univ : Finset (Fin 4)) (fun i _ => ht i)
  have h := (tendsto_const_nhds (x := (A.constant : ℝ))).add hs
  simpa only [Affine.lower, Affine.eval, Rat.cast_add, Rat.cast_sum] using h

theorem affine_upper_tendsto (A : Affine) {v : LogFour} (hv : v ∈ cube) :
    Tendsto (fun n => (A.upper (gridBox n (owner n v)).lo
      (gridBox n (owner n v)).hi : ℝ)) atTop (𝓝 (A.eval v)) := by
  have h := (affine_lower_tendsto A.neg hv).neg
  simpa only [Affine.upper, Rat.cast_neg, Affine.eval_neg, neg_neg] using h

theorem eventually_all_eligibility_tests {v : LogFour} (hv : v ∈ cube)
    (hno : ∀ p : Policy, ∀ g : Gate, Required p g → ∀ left : Bool,
      wall p left g v ≠ wallOffset p left g) :
    ∀ᶠ n : ℕ in atTop, ∀ p : Policy,
      (correlatedEligibleTest p (gridBox n (owner n v)) = true ↔ TypedEligible p v) ∧
      (correlatedIneligibleTest p (gridBox n (owner n v)) = true ↔ ¬TypedEligible p v) := by
  apply eventually_all.mpr
  intro p
  obtain ⟨delta, hd, hlocal⟩ := exists_local_complete_radius p v (hno p)
  filter_upwards [tendsto_step.eventually (gt_mem_nhds hd)] with n hn
  exact hlocal _ (cell_subset_closedBox n (owner n v) (owner_mem n hv))
    (fun i => (owner_width n v i).trans hn.le)

theorem eventually_owner_inner {v : LogFour} (hv : v ∈ sourceDomain)
    (hc : v ∈ cube) (hno : ∀ i : Fin 6, sourceForms i v ≠ sourceBounds i) :
    ∀ᶠ n : ℕ in atTop, owner n v ∈ inner n := by
  have hgap (i : Fin 6) : sourceGap i v < 0 := by
    have h := (mem_sourceDomain_iff v).mp hv i
    have hne : sourceGap i v ≠ 0 := sub_ne_zero.mpr (hno i)
    split_ifs at h
    · rcases lt_or_eq_of_le h with hh | hh
      · exact hh
      · exact (hne hh).elim
    · exact h
  have hall : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 6,
      (((sourcePiece i).upper (gridBox n (owner n v)).lo
        (gridBox n (owner n v)).hi : ℚ) : ℝ) < 0 := by
    apply eventually_all.mpr
    intro i
    have h := affine_upper_tendsto (sourcePiece i) hc
    rw [sourcePiece_eval] at h
    exact h.eventually (gt_mem_nhds (hgap i))
  filter_upwards [hall] with n hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i
  exact_mod_cast hn i

theorem eventually_owner_not_outer {v : LogFour} (hv : v ∉ sourceDomain)
    (hc : v ∈ cube) (hno : ∀ i : Fin 6, sourceForms i v ≠ sourceBounds i) :
    ∀ᶠ n : ℕ in atTop, owner n v ∉ outer n := by
  have hex : ∃ i : Fin 6, 0 < sourceGap i v := by
    by_contra hn
    have hall : ∀ i : Fin 6, sourceGap i v ≤ 0 := by
      intro i
      exact le_of_not_gt ((not_exists.mp hn) i)
    apply hv
    apply (mem_sourceDomain_iff v).mpr
    intro i
    have hne : sourceGap i v ≠ 0 := sub_ne_zero.mpr (hno i)
    have hs : sourceGap i v < 0 := by
      rcases lt_or_eq_of_le (hall i) with h | h
      · exact h
      · exact (hne h).elim
    split_ifs
    · exact hs.le
    · exact hs
  obtain ⟨i, hi⟩ := hex
  have ht := affine_lower_tendsto (sourcePiece i) hc
  rw [sourcePiece_eval] at ht
  filter_upwards [ht.eventually (lt_mem_nhds hi)] with n hn
  intro houter
  have hQ := (Finset.mem_filter.mp houter).2 i
  have hR : (((sourcePiece i).lower (gridBox n (owner n v)).lo
      (gridBox n (owner n v)).hi : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hQ
  exact (not_lt_of_ge hR) hn

abbrev RequiredIndex := {t : Policy × Gate × Bool // Required t.1 t.2.1}

def eligibilityForms (t : RequiredIndex) : LogFour →L[ℝ] ℝ := wall t.val.1 t.val.2.2 t.val.2.1
def eligibilityBounds (t : RequiredIndex) : ℝ := wallOffset t.val.1 t.val.2.2 t.val.2.1

theorem eligibilityForms_ne_zero (t : RequiredIndex) : eligibilityForms t ≠ 0 :=
  actual_wall_ne_zero t.val.1 t.val.2.2 t.val.2.1 t.property

theorem ae_no_actual_eligibility_walls :
    ∀ᵐ v : LogFour ∂volume, ∀ p : Policy, ∀ g : Gate, Required p g → ∀ left : Bool,
      wall p left g v ≠ wallOffset p left g := by
  filter_upwards [ae_primeAffineGate_no_wall eligibilityForms eligibilityBounds
    eligibilityForms_ne_zero] with v hv
  intro p g hg left
  exact hv ⟨(p, g, left), hg⟩

end

end ImbalancedChen.P5Z.U1011OriginalSixteenTightGridLocalGeometry
