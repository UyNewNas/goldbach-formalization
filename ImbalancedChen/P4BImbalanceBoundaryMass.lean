import ImbalancedChen.P4BRealBParameterMonotonicity
import ImbalancedChen.RealHalfProductMassSuppliers
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# P4B: unconditional arithmetic mass of an imbalance-wall collar

SOURCE ONLY / YELLOW / UNCOMPILED.

The fixed-exponent manuscript-cutoff mass limits are supplied by the actual
PNT/Mertens supplier module, with no analytic premise in this file.  Exact
source antitonicity identifies the difference as an arithmetic margin strip.
For each fixed target `1/2 < b < 1` and fixed positive `kappa`, a parameter
`1/2 < a < b` can be chosen before the eventual integer threshold so that
this strip costs at most any prescribed positive multiple of `N / log N`.
No currentK, distribution estimate, or final bad-count estimate is used.
-/

namespace ImbalancedChen.P4BImbalanceBoundaryMass

noncomputable section
open Filter Topology

/-- Actual ordered-source points removed between two imbalance exponents,
at the same fixed manuscript product cutoff. -/
def imbalanceBand (a b kappa : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact realHalfProductSource a N (manuscriptHalfProductCutoff kappa N) \
    realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)

/-- Exact arithmetic margin-strip dictionary.  The factor wall at `a` is
strict and the wall at `b` is inclusive; ordered prime squares are retained. -/
theorem mem_imbalanceBand_iff {a b kappa : ℝ} {N m : ℕ} :
    m ∈ imbalanceBand a b kappa N ↔
      m ≤ N ∧ manuscriptHalfProductCutoff kappa N ≤ (m : ℝ) ∧
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r ≤ q ∧
          (q : ℝ) ^ a < (r : ℝ) ∧ (r : ℝ) ≤ (q : ℝ) ^ b := by
  exact P4BRealBParameterMonotonicity.mem_source_sdiff_iff

/-- Antitonicity makes the cardinality difference exact over the reals.
The cast is taken after an additive natural-cardinality identity, so natural
subtraction is never cast without its required inequality. -/
theorem imbalanceBand_card_eq_sub {a b kappa : ℝ} {N : ℕ}
    (hab : a ≤ b) :
    ((imbalanceBand a b kappa N).card : ℝ) =
      ((realHalfProductSource a N (manuscriptHalfProductCutoff kappa N)).card : ℝ) -
        ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) := by
  classical
  have hsub := realHalfProductSource_antitone
    (N := N) (T := manuscriptHalfProductCutoff kappa N) hab
  have hnat := Finset.card_sdiff_add_card_eq_card hsub
  have hcast :
      ((imbalanceBand a b kappa N).card : ℝ) +
          ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) =
        ((realHalfProductSource a N (manuscriptHalfProductCutoff kappa N)).card : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Unconditional asymptotic mass of the exact arithmetic imbalance strip.
Both limits on the right are the proved fixed-exponent supplier limits. -/
theorem tendsto_imbalanceBand_manuscript_mass {a b kappa : ℝ}
    (ha : 0 < a) (hab : a < b) (hb1 : b < 1) (hkappa : 0 < kappa) :
    Tendsto (fun N : ℕ => ((imbalanceBand a b kappa N).card : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ))) atTop
      (nhds (Real.log (1 / a) - Real.log (1 / b))) := by
  have ha1 : a < 1 := hab.trans hb1
  have hb : 0 < b := ha.trans hab
  have hlimA :=
    tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers ha ha1 hkappa
  have hlimB :=
    tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers hb hb1 hkappa
  have hfun :
      (fun N : ℕ => ((imbalanceBand a b kappa N).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ))) =
      (fun N : ℕ =>
        ((realHalfProductSource a N (manuscriptHalfProductCutoff kappa N)).card : ℝ) /
            ((N : ℝ) / Real.log (N : ℝ)) -
          ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) /
            ((N : ℝ) / Real.log (N : ℝ))) := by
    funext N
    rw [imbalanceBand_card_eq_sub hab.le, sub_div]
  rw [hfun]
  exact hlimA.sub hlimB

/-- Choose the lower exponent only after fixing the target exponent and a
positive reserve.  Continuity is applied to the literal coefficient log(1/x).
There is no mass-limit hypothesis. -/
theorem exists_lower_parameter_log_gap {b eta : ℝ}
    (hbHalf : (1 / 2 : ℝ) < b) (heta : 0 < eta) :
    ∃ a : ℝ, (1 / 2 : ℝ) < a ∧ a < b ∧
      Real.log (1 / a) - Real.log (1 / b) < eta := by
  have hb : 0 < b := by linarith
  let f : ℝ → ℝ := fun x => Real.log (1 / x)
  have hinv : ContinuousAt (fun x : ℝ => 1 / x) b :=
    continuousAt_const.div continuousAt_id hb.ne'
  have hbinv : (1 : ℝ) / b ≠ 0 := (one_div_pos.mpr hb).ne'
  have hf : ContinuousAt f b := (Real.continuousAt_log hbinv).comp hinv
  obtain ⟨delta, hdelta, hnear⟩ :=
    Metric.continuousAt_iff.mp hf eta heta
  have hleft : max (1 / 2 : ℝ) (b - delta) < b :=
    max_lt hbHalf (sub_lt_self b hdelta)
  obtain ⟨a, hlefta, hab⟩ := exists_between hleft
  have haHalf : (1 / 2 : ℝ) < a :=
    (le_max_left _ _).trans_lt hlefta
  have hadelta : b - delta < a :=
    (le_max_right _ _).trans_lt hlefta
  have hdist : dist a b < delta := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hab)]
    linarith
  have hclose : |f a - f b| < eta := by
    simpa only [Real.dist_eq] using hnear hdist
  have hgap : Real.log (1 / a) - Real.log (1 / b) < eta := by
    exact (abs_lt.mp hclose).2
  exact ⟨a, haHalf, hab, hgap⟩

/-- A genuine arithmetic wall-collar reserve.  The lower exponent is fixed
before one threshold N0; the resulting bound holds for every N >= N0, and
hence simultaneously for every even N in that range.  kappa remains any
fixed positive manuscript-cutoff parameter. -/
theorem exists_parameter_boundary_mass_reserve {b kappa eta : ℝ}
    (hbHalf : (1 / 2 : ℝ) < b) (hb1 : b < 1)
    (hkappa : 0 < kappa) (heta : 0 < eta) :
    ∃ a : ℝ, 0 < a ∧ (1 / 2 : ℝ) < a ∧ a < b ∧ a < 1 ∧
      Real.log (1 / a) - Real.log (1 / b) < eta ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
        ((imbalanceBand a b kappa N).card : ℝ) ≤
          eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨a, haHalf, hab, hgap⟩ :=
    exists_lower_parameter_log_gap hbHalf (half_pos heta)
  have ha : 0 < a := by linarith
  have ha1 : a < 1 := hab.trans hb1
  have hgapEta : Real.log (1 / a) - Real.log (1 / b) < eta := by linarith
  have hlim := tendsto_imbalanceBand_manuscript_mass ha hab hb1 hkappa
  have hratio : ∀ᶠ N : ℕ in atTop,
      ((imbalanceBand a b kappa N).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) < eta :=
    hlim.eventually (gt_mem_nhds hgapEta)
  have hbound : ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ ((imbalanceBand a b kappa N).card : ℝ) ≤
        eta * ((N : ℝ) / Real.log (N : ℝ)) := by
    filter_upwards [hratio, eventually_ge_atTop (2 : ℕ)] with N hratioN hN
    have hN1 : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
      div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
    exact ⟨hN, ((div_lt_iff₀ hscale).mp hratioN).le⟩
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨a, ha, haHalf, hab, ha1, hgapEta, N0, (hN0 N0 le_rfl).1, ?_⟩
  intro N hN
  exact (hN0 N hN).2

end
end ImbalancedChen.P4BImbalanceBoundaryMass
