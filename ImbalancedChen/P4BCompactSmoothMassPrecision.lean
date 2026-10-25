import ImbalancedChen.P4BSmoothMassParameterOrder
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact-b uniform precision for the genuine smooth physical mass

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Continuity of the exact coefficient gives small-oscillation endpoint
intervals. A finite subcover and finite minima/maxima combine the two-point
arithmetic mass estimates. Thus no uniform PNT statement is an input.
The final width and target threshold work for all b in the fixed compact
interval and every smaller positive physical width.
-/

namespace ImbalancedChen.P4B

noncomputable section
open scoped Classical BigOperators
open Filter Topology

/-- Interior endpoints with arbitrarily small exact coefficient span. -/
theorem exists_local_logCoefficient_interval
    {b eta : ℝ} (hbHalf : (1 / 2 : ℝ) < b) (hbOne : b < 1)
    (heta : 0 < eta) :
    ∃ a c : ℝ, (1 / 2 : ℝ) < a ∧ a < b ∧ b < c ∧ c < 1 ∧
      Real.log (1 / a) - Real.log (1 / c) < eta := by
  have hb : 0 < b := by linarith only [hbHalf]
  have hinv : ContinuousAt (fun x : ℝ => 1 / x) b :=
    continuousAt_const.div continuousAt_id hb.ne'
  have hcont : ContinuousAt (fun x : ℝ => Real.log (1 / x)) b :=
    (Real.continuousAt_log (one_div_pos.mpr hb).ne').comp hinv
  obtain ⟨delta, hdelta, hnear⟩ :=
    Metric.continuousAt_iff.mp hcont (eta / 2) (half_pos heta)
  have hleft : max (1 / 2 : ℝ) (b - delta) < b :=
    max_lt hbHalf (sub_lt_self b hdelta)
  have hright : b < min 1 (b + delta) :=
    lt_min hbOne (by linarith only [hdelta])
  obtain ⟨a, ha, hab⟩ := exists_between hleft
  obtain ⟨c, hbc, hc⟩ := exists_between hright
  have haHalf : (1 / 2 : ℝ) < a := (le_max_left _ _).trans_lt ha
  have haDelta : b - delta < a := (le_max_right _ _).trans_lt ha
  have hcOne : c < 1 := hc.trans_le (min_le_left _ _)
  have hcDelta : c < b + delta := hc.trans_le (min_le_right _ _)
  have hdistA : dist a b < delta := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hab)]
    linarith only [haDelta]
  have hdistC : dist c b < delta := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hbc)]
    linarith only [hcDelta]
  have hcloseA := hnear hdistA
  have hcloseC := hnear hdistC
  rw [Real.dist_eq] at hcloseA hcloseC
  have hA := (abs_lt.mp hcloseA).2
  have hC := (abs_lt.mp hcloseC).1
  exact ⟨a, c, haHalf, hab, hbc, hcOne, by linarith only [hA, hC]⟩

/-- Unconditional uniform mass precision on a compact interior b interval.
The arithmetic inputs are only the already proved fixed-endpoint estimates.
No estimate depending on the intermediate b is assumed or selected. -/
theorem exists_compact_uniform_smooth_physical_mass_precision
    {b0 b1 kappa : ℝ} (hb0 : (1 / 2 : ℝ) < b0) (hb1 : b1 < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (epsilon widthMax : ℝ) (hepsilon : 0 < epsilon) (hwidthMax : 0 < widthMax) :
    ∃ width0 : ℝ, 0 < width0 ∧ width0 ≤ widthMax ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ width : ℝ, 0 < width → width ≤ width0 →
        ∀ N : ℕ, N0 ≤ N → Even N → ∀ b : ℝ, b0 ≤ b → b ≤ b1 →
          |normalizedSmoothPhysicalMass b kappa width N - Real.log (1 / b)| < epsilon := by
  have hlocal : ∀ x : Set.Icc b0 b1,
      ∃ a c : ℝ, (1 / 2 : ℝ) < a ∧ a < (x : ℝ) ∧ (x : ℝ) < c ∧ c < 1 ∧
        Real.log (1 / a) - Real.log (1 / c) < epsilon / 2 := by
    intro x
    exact exists_local_logCoefficient_interval
      (hb0.trans_le x.property.1) (x.property.2.trans_lt hb1) (half_pos hepsilon)
  choose a c ha hax hxc hc hspan using hlocal
  have hcover : Set.Icc b0 b1 ⊆ ⋃ x : Set.Icc b0 b1, Set.Ioo (a x) (c x) := by
    intro b hb
    exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, hax ⟨b, hb⟩, hxc ⟨b, hb⟩⟩
  obtain ⟨S, hS⟩ := (isCompact_Icc : IsCompact (Set.Icc b0 b1)).elim_finite_subcover
    (fun x => Set.Ioo (a x) (c x)) (fun _ => isOpen_Ioo) hcover
  have hfinite : ∀ F : Finset (Set.Icc b0 b1),
      ∃ width0 : ℝ, 0 < width0 ∧ width0 ≤ widthMax ∧
        ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ x ∈ F,
          ∀ width : ℝ, 0 < width → width ≤ width0 →
            ∀ N : ℕ, N0 ≤ N → Even N → ∀ b : ℝ, b ∈ Set.Ioo (a x) (c x) →
              |normalizedSmoothPhysicalMass b kappa width N - Real.log (1 / b)| < epsilon := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      refine ⟨widthMax, hwidthMax, le_rfl, 2, le_rfl, ?_⟩
      intro x hx
      exact False.elim (Finset.not_mem_empty x hx)
    | @insert x F hx ih =>
      obtain ⟨widthF, hwidthF, hmaxF, NF, hNF, hF⟩ := ih
      obtain ⟨widthX, hwidthX, _hmaxX, NX, hNX, hX⟩ :=
        exists_compact_endpoint_smooth_mass_control (ha x)
          ((hax x).trans (hxc x)).le (hc x) hkappa hkappaOne
          (epsilon / 2) widthMax (half_pos hepsilon) hwidthMax
      refine ⟨min widthF widthX, lt_min hwidthF hwidthX,
        (min_le_left _ _).trans hmaxF, max NF NX, hNF.trans (le_max_left _ _), ?_⟩
      intro y hy width hwidth hwidth0 N hN hEven b hb
      rcases Finset.mem_insert.mp hy with rfl | hyF
      · have hbound := hX width hwidth (hwidth0.trans (min_le_right _ _))
          N ((le_max_right NF NX).trans hN) hEven b hb.1.le hb.2.le
        have hosc := hspan x
        linarith only [hbound, hosc]
      · exact hF y hyF width hwidth (hwidth0.trans (min_le_left _ _))
          N ((le_max_left NF NX).trans hN) hEven b hb
  obtain ⟨width0, hwidth0, hmax, N0, hN0, hcommon⟩ := hfinite S
  refine ⟨width0, hwidth0, hmax, N0, hN0, ?_⟩
  intro width hwidth hwidthLe N hN hEven b hb0b hbb1
  have hbCover := hS (show b ∈ Set.Icc b0 b1 from ⟨hb0b, hbb1⟩)
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hbCover
  obtain ⟨hxS, hbx⟩ := Set.mem_iUnion.mp hx
  exact hcommon x hxS width hwidth hwidthLe N hN hEven b hbx

end
end ImbalancedChen.P4B
