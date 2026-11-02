import ImbalancedChen.OriginalAscendingThirteenExportOwnershipJoin
import ImbalancedChen.HistoricalThirdCoarsePolicy
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The thirteen A23/s23_low domains and all 97 literal rows are imported,
not regenerated. This fills the missing *lower* historical-third port:
the actual rational HistoricalThirdCoarse.gamma, on one common finite
first-three mesh, lies within 3*chi of the physical A23 minorant. Its
literal buffered level therefore retains H1,H3,H5,H7 on any common
compact subset of the thirteen source domains at one precision.

No H7<lambda3, cap-approximation estimate, child-dependent ancestor,
moment floor, or numerical endpoint is an assumption. The uniform
theorem permits any selected mesh boxes; selection/limiting coverage
and preserving the old global approximation budgets remain separate.
-/

namespace ImbalancedChen.P2OriginalSaving19HistoricalMinorant

noncomputable section
open Set VariableEnvelope HistoricalThirdCoarse
open P2OriginalThirdMinorantLogDictionarySourceOnly
open OriginalAscendingThirteenCellOwnership

/-- All six margins are actual proper source rows (four are histories).
This is a function of the physical point, not of a chosen ancestor cap. -/
def historyMargin (t : Point) : ℝ :=
  min (mu - t 0) (min (mu - (t 1 + t 2))
    (min (thirdMinorant t - 3 * t 0)
      (min (thirdMinorant t - history3 t)
        (min (thirdMinorant t - history5 t) (thirdMinorant t - history7 t)))))

theorem historyMargin_pos {i : Fin 13} {t : Point} (h : StrictRows i t) :
    0 < historyMargin t := by
  simp only [historyMargin, lt_min_iff]
  exact ⟨sub_pos.mpr h.largest, sub_pos.mpr h.ascendingThird,
    sub_pos.mpr h.firstHistory, sub_pos.mpr h.thirdHistory,
    sub_pos.mpr h.fifthHistory, sub_pos.mpr h.seventhHistory⟩

theorem continuous_historyMargin : Continuous historyMargin := by
  unfold historyMargin thirdMinorant history3 history5 history7 A
  fun_prop

theorem historyMargin_bounds {t : Point} {δ : ℝ} (h : δ ≤ historyMargin t) :
    δ ≤ mu - t 0 ∧ δ ≤ mu - (t 1 + t 2) ∧
      δ ≤ thirdMinorant t - 3 * t 0 ∧
      δ ≤ thirdMinorant t - history3 t ∧
      δ ≤ thirdMinorant t - history5 t ∧
      δ ≤ thirdMinorant t - history7 t := by
  simpa only [historyMargin, le_min_iff] using h

/-- The source's positive 3/256 pair margin survives on the whole
closed rational ancestor box, not just at a sampled child point. -/
theorem original_yzGap_margin (b : RationalBox)
    (hx : (b.ux : ℝ) ≤ mu) (hyz : (b.uy : ℝ) + b.uz ≤ mu) :
    (3 / 256 : ℝ) ≤ yzGap b := by
  rw [yzGap, v_eq_A hyz]
  dsimp [A, mu] at *
  linarith

/-- Exact retained pair entry of the original rational maximum. -/
theorem original_pair_entry_le_gamma (b : RationalBox) {e : ℝ}
    (hdispatch : (b.ux : ℝ) ≤ mu - 4 * e) (hgate : e ≤ yzGap b) :
    (qVLo (b.ly + b.lz) (b.uy + b.uz) : ℝ) ≤ (gamma e b : ℝ) := by
  have hq : qVLo (b.ly + b.lz) (b.uy + b.uz) ≤ fullGamma e b := by
    unfold fullGamma
    rw [if_pos hgate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))))
  rw [gamma, if_pos hdispatch]
  exact_mod_cast hq

/-- The physical A23 source pays the actual Gamma approximation error.
The interval theorem is an analytic enclosure, with no finite replay. -/
theorem original_pair_minorant_error (b : RationalBox) {t : Point} {e χ : ℝ}
    (ht : b.InBox (t 0) (t 1) (t 2))
    (hwidth : (b.width : ℝ) ≤ χ)
    (hdispatch : (b.ux : ℝ) ≤ mu - 4 * e)
    (hpair : t 1 + t 2 ≤ mu) (hgate : e ≤ yzGap b) :
    thirdMinorant t - levelExponent e b ≤ 3 * χ + 2 * e := by
  have hy : (b.uy : ℝ) - b.ly ≤ χ := by
    have hq := b.coordinate_widths_le.2.1
    have hr : (b.uy : ℝ) - b.ly ≤ (b.width : ℝ) := by exact_mod_cast hq
    exact hr.trans hwidth
  have hz : (b.uz : ℝ) - b.lz ≤ χ := by
    have hq := b.coordinate_widths_le.2.2
    have hr : (b.uz : ℝ) - b.lz ≤ (b.width : ℝ) := by exact_mod_cast hq
    exact hr.trans hwidth
  have hlo : ((b.ly + b.lz : ℚ) : ℝ) ≤ t 1 + t 2 := by
    push_cast
    exact add_le_add ht.2.2.1 ht.2.2.2.2.1
  have hhi : t 1 + t 2 ≤ ((b.uy + b.uz : ℚ) : ℝ) := by
    push_cast
    exact add_le_add ht.2.2.2.1 ht.2.2.2.2.2
  have herr := rationalInterval_v_error hlo hhi
  rw [v_eq_A hpair] at herr
  push_cast at herr
  have hg := original_pair_entry_le_gamma b hdispatch hgate
  dsimp only [thirdMinorant, levelExponent]
  linarith

/-- One source margin and one common mesh precision imply all original
odd histories below the actual coarse third level. Desired history
inequalities and the pair gate are conclusions, not record fields. -/
theorem original_coarse_histories (b : RationalBox) {t : Point} {δ e χ : ℝ}
    (hδ : 0 < δ) (hm : δ ≤ historyMargin t)
    (he : 0 ≤ e) (heδ : e ≤ δ / 16) (hegate : e ≤ 3 / 256)
    (hχ : χ ≤ δ / 16)
    (ht : b.InBox (t 0) (t 1) (t 2)) (hwidth : (b.width : ℝ) ≤ χ) :
    3 * t 0 < levelExponent e b ∧ history3 t < levelExponent e b ∧
      history5 t < levelExponent e b ∧ history7 t < levelExponent e b := by
  rcases historyMargin_bounds hm with ⟨hmx, hmp, hm1, hm3, hm5, hm7⟩
  have hx : (b.ux : ℝ) - b.lx ≤ χ := by
    have hq := b.coordinate_widths_le.1
    have hr : (b.ux : ℝ) - b.lx ≤ (b.width : ℝ) := by exact_mod_cast hq
    exact hr.trans hwidth
  have hy : (b.uy : ℝ) - b.ly ≤ χ := by
    have hq := b.coordinate_widths_le.2.1
    have hr : (b.uy : ℝ) - b.ly ≤ (b.width : ℝ) := by exact_mod_cast hq
    exact hr.trans hwidth
  have hz : (b.uz : ℝ) - b.lz ≤ χ := by
    have hq := b.coordinate_widths_le.2.2
    have hr : (b.uz : ℝ) - b.lz ≤ (b.width : ℝ) := by exact_mod_cast hq
    exact hr.trans hwidth
  have hdispatch : (b.ux : ℝ) ≤ mu - 4 * e := by linarith [ht.1]
  have hux : (b.ux : ℝ) ≤ mu := by linarith
  have huyz : (b.uy : ℝ) + b.uz ≤ mu := by
    linarith [ht.2.2.1, ht.2.2.2.2.1]
  have hgate := hegate.trans (original_yzGap_margin b hux huyz)
  have hp : t 1 + t 2 ≤ mu := by linarith
  have herr := original_pair_minorant_error b ht hwidth hdispatch hp hgate
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The compact set may cross several source cells and several first-three
projection fibres. The SAME positive precision is selected first, before
e, chi, the finite mesh, all boxes, all children, and N. Empty K is allowed. -/
theorem exists_common_history_precision (K : Set Point) (hK : IsCompact K)
    (hsource : ∀ t ∈ K, ∃ i : Fin 13, StrictRows i t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (e χ : ℝ), 0 ≤ e → e ≤ ε → χ ≤ ε →
      ∀ (b : RationalBox) (t : Point), t ∈ K →
        b.InBox (t 0) (t 1) (t 2) → (b.width : ℝ) ≤ χ →
        3 * t 0 < levelExponent e b ∧ history3 t < levelExponent e b ∧
          history5 t < levelExponent e b ∧ history7 t < levelExponent e b := by
  obtain ⟨δ, hδ, hm⟩ := hK.exists_forall_le' continuous_historyMargin.continuousOn
    (by intro t ht; obtain ⟨i, hi⟩ := hsource t ht; exact historyMargin_pos hi)
  refine ⟨min (δ / 16) (3 / 256), lt_min (by positivity) (by norm_num), ?_⟩
  intro e χ he heε hχε b t ht hbt hwidth
  exact original_coarse_histories b hδ (hm t ht) he
    (heε.trans (min_le_left _ _)) (heε.trans (min_le_right _ _))
    (hχε.trans (min_le_left _ _)) hbt hwidth

/-- Literal source-row entry point. No new geometry payload is required. -/
theorem exists_common_exported_history_precision (K : Set Point) (hK : IsCompact K)
    (hsource : ∀ t ∈ K, ∃ i : Fin 13,
      OriginalAscendingThirteenLiteralAffineRows.StrictExportedRows i t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (e χ : ℝ), 0 ≤ e → e ≤ ε → χ ≤ ε →
      ∀ (b : RationalBox) (t : Point), t ∈ K →
        b.InBox (t 0) (t 1) (t 2) → (b.width : ℝ) ≤ χ →
        3 * t 0 < levelExponent e b ∧ history3 t < levelExponent e b ∧
          history5 t < levelExponent e b ∧ history7 t < levelExponent e b := by
  apply exists_common_history_precision K hK
  intro t ht
  obtain ⟨i, hi⟩ := hsource t ht
  exact ⟨i, (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp hi⟩

end
end ImbalancedChen.P2OriginalSaving19HistoricalMinorant
