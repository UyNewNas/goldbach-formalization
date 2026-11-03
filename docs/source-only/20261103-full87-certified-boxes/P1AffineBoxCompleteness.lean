import ImbalancedChen.P1FiniteAffineDecisionProgram
import ImbalancedChen.AffinePrimeGates

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Completeness of the existing CLOSED-box sign certificate away from proper
walls. A zero coefficient vector is handled exactly, including an affine
identity. It is NEVER placed in the exceptional wall family. The quantitative
bound concerns the actual coefficient-sign extrema, not midpoint samples.
-/
namespace ImbalancedChen.P1AffineBoxCompleteness
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory P1FiniteAffineDecisionProgram

def _root_.ImbalancedChen.P1FiniteAffineDecisionProgram.Affine.slopeMass {k : ℕ} (a : Affine k) : ℝ := ∑ i, |a.coefficient i|

theorem _root_.ImbalancedChen.P1FiniteAffineDecisionProgram.Affine.slopeMass_nonneg {k : ℕ} (a : Affine k) : 0 ≤ a.slopeMass :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- This is the error of the ORIGINAL sign-extremum box evaluator. -/
theorem _root_.ImbalancedChen.P1FiniteAffineDecisionProgram.Affine.endpoint_error {k : ℕ} (a : Affine k) (r : ℝ)
    (lo hi t : Fin k → ℝ)
    (hl : ∀ i, t i - r ≤ lo i) (hu : ∀ i, hi i ≤ t i + r) :
    a.eval t - r * a.slopeMass ≤ a.lower lo hi ∧
      a.upper lo hi ≤ a.eval t + r * a.slopeMass := by
  have hlow (i : Fin k) : a.coefficient i * t i - r * |a.coefficient i| ≤
      if 0 ≤ a.coefficient i then a.coefficient i * lo i
      else a.coefficient i * hi i := by
    by_cases hc : 0 ≤ a.coefficient i
    · rw [if_pos hc, abs_of_nonneg hc]
      nlinarith [mul_le_mul_of_nonneg_left (hl i) hc]
    · rw [if_neg hc, abs_of_neg (lt_of_not_ge hc)]
      nlinarith [mul_le_mul_of_nonpos_left (hu i) (le_of_not_ge hc)]
  have hupp (i : Fin k) :
      (if 0 ≤ a.coefficient i then a.coefficient i * hi i
       else a.coefficient i * lo i) ≤ a.coefficient i * t i + r * |a.coefficient i| := by
    by_cases hc : 0 ≤ a.coefficient i
    · rw [if_pos hc, abs_of_nonneg hc]
      nlinarith [mul_le_mul_of_nonneg_left (hu i) hc]
    · rw [if_neg hc, abs_of_neg (lt_of_not_ge hc)]
      nlinarith [mul_le_mul_of_nonpos_left (hl i) (le_of_not_ge hc)]
  have hL := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hlow i)
  have hU := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hupp i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hL hU
  dsimp [Affine.eval, Affine.lower, Affine.upper, Affine.slopeMass]
  constructor <;> linarith

/-- Constant comparisons are EXACT on every box, even on an equality stratum. -/
theorem _root_.ImbalancedChen.P1FiniteAffineDecisionProgram.Affine.constant_endpoints {k : ℕ} (a : Affine k)
    (hc : a.coefficient = 0) (lo hi t : Fin k → ℝ) :
    a.lower lo hi = a.eval t ∧ a.upper lo hi = a.eval t := by
  simp [Affine.lower, Affine.upper, Affine.eval, hc]

def Separated {k : ℕ} (p : Program k) (eta : ℝ) (t : Fin k → ℝ) : Prop :=
  ∀ ab : p.Label × p.Label,
    let a := ab.1.val.sub ab.2.val
    a.coefficient ≠ 0 → eta * (a.slopeMass + 1) ≤ |a.eval t|

def Regular {k : ℕ} (p : Program k) (t : Fin k → ℝ) : Prop :=
  ∀ ab : p.Label × p.Label,
    let a := ab.1.val.sub ab.2.val
    a.coefficient ≠ 0 → a.eval t ≠ 0

theorem separated_mono {k : ℕ} (p : Program k) {r eta : ℝ}
    (hr : r ≤ eta) {t : Fin k → ℝ} (ht : Separated p eta t) : Separated p r t := by
  intro ab ha
  exact (mul_le_mul_of_nonneg_right hr
    (by linarith [(ab.1.val.sub ab.2.val).slopeMass_nonneg])).trans (ht ab ha)

private theorem sign_certificate {k : ℕ} (a : Affine k) (eta : ℝ) (heta : 0 < eta)
    (lo hi t : Fin k → ℝ)
    (hl : ∀ i, t i - eta ≤ lo i) (hu : ∀ i, hi i ≤ t i + eta)
    (hsep : a.coefficient ≠ 0 → eta * (a.slopeMass + 1) ≤ |a.eval t|) :
    (if a.eval t < 0 then a.upper lo hi < 0 else 0 ≤ a.lower lo hi) ∧
    (if a.eval t ≤ 0 then a.upper lo hi ≤ 0 else 0 < a.lower lo hi) := by
  by_cases hc : a.coefficient = 0
  · obtain ⟨hL, hU⟩ := a.constant_endpoints hc lo hi t
    rw [hL, hU]
    constructor
    · split_ifs with h
      · exact h
      · exact le_of_not_gt h
    · split_ifs with h
      · exact h
      · exact lt_of_not_ge h
  · have hs := hsep hc
    have hp : 0 < eta * (a.slopeMass + 1) :=
      mul_pos heta (by linarith [a.slopeMass_nonneg])
    have hn : a.eval t ≠ 0 := abs_pos.mp (hp.trans_le hs)
    obtain ⟨hL, hU⟩ := a.endpoint_error eta lo hi t hl hu
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · rw [if_pos hneg, if_pos hneg.le]
      rw [abs_of_neg hneg] at hs
      constructor <;> nlinarith
    · rw [if_neg (not_lt_of_ge hpos.le), if_neg (not_le_of_gt hpos)]
      rw [abs_of_pos hpos] at hs
      constructor <;> nlinarith

/-- A point with explicit normalized margins certifies every sufficiently
small surrounding CLOSED rectangle, not just the selected sample. -/
theorem boxCertificate_of_separated {k : ℕ} (p : Program k)
    (eta : ℝ) (heta : 0 < eta) (lo hi t : Fin k → ℝ)
    (hl : ∀ i, t i - eta ≤ lo i) (hu : ∀ i, hi i ≤ t i + eta)
    (ht : Separated p eta t) : p.BoxCertificate (p.signature t) lo hi := by
  intro ab
  have h := sign_certificate (ab.1.val.sub ab.2.val) eta heta lo hi t hl hu (ht ab)
  simpa only [Program.signature, decide_eq_true_eq, Affine.eval_sub,
    sub_lt_zero, sub_le_zero] using h

/-- The existing null-wall theorem receives an actual nonzero linear map. -/
def _root_.ImbalancedChen.P1FiniteAffineDecisionProgram.Affine.linearPart {k : ℕ} (a : Affine k) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin k, a.coefficient i • ContinuousLinearMap.proj i

@[simp] theorem _root_.ImbalancedChen.P1FiniteAffineDecisionProgram.Affine.linearPart_apply {k : ℕ} (a : Affine k) (t : Fin k → ℝ) :
    a.linearPart t = ∑ i, a.coefficient i * t i := by
  simp [Affine.linearPart]

theorem _root_.ImbalancedChen.P1FiniteAffineDecisionProgram.Affine.linearPart_ne_zero {k : ℕ} (a : Affine k)
    (hc : a.coefficient ≠ 0) : a.linearPart ≠ 0 := by
  intro h
  apply hc
  funext i
  have he := congrArg (fun L : (Fin k → ℝ) →L[ℝ] ℝ =>
    L (fun j => if j = i then (1 : ℝ) else 0)) h
  simpa [Affine.linearPart_apply, mul_ite] using he

theorem _root_.ImbalancedChen.P1FiniteAffineDecisionProgram.Affine.proper_wall_null {k : ℕ} (a : Affine k) (hc : a.coefficient ≠ 0) :
    volume {t | a.eval t = 0} = 0 := by
  have hs : {t | a.eval t = 0} = {t | a.linearPart t = -a.constant} := by
    ext t
    simp only [mem_setOf_eq, Affine.eval, Affine.linearPart_apply]
    constructor <;> intro h <;> linarith
  rw [hs]
  exact affinePrimeWall_volume_zero a.linearPart (a.linearPart_ne_zero hc) (-a.constant)

/-- An earlier-rank proper wall is still proper when embedded in a later
coordinate space. We do not project a child wall into an ancestor domain. -/
theorem _root_.ImbalancedChen.P1FiniteAffineDecisionProgram.Affine.pull_coefficient_ne_zero {k d : ℕ} (a : Affine k)
    (f : Fin k ↪ Fin d) (hc : a.coefficient ≠ 0) :
    (a.pull f).coefficient ≠ 0 := by
  intro h
  apply hc
  funext i
  have he := congrFun h (f i)
  simpa [Affine.pull, f.injective.eq_iff] using he

theorem ae_regular_projection {k d : ℕ} (p : Program k) (f : Fin k ↪ Fin d) :
    ∀ᵐ t : Fin d → ℝ ∂volume, Regular p (fun i => t (f i)) := by
  apply ae_all_iff.mpr
  intro ab
  let a := ab.1.val.sub ab.2.val
  by_cases hc : a.coefficient = 0
  · exact Filter.Eventually.of_forall (fun _ h => (h hc).elim)
  · have hnull := (a.pull f).proper_wall_null (a.pull_coefficient_ne_zero f hc)
    have hn : ∀ᵐ t : Fin d → ℝ ∂volume, (a.pull f).eval t ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using hnull
    filter_upwards [hn] with t ht
    intro _
    simpa only [Affine.eval_pull] using ht

theorem eventually_separated {k : ℕ} (p : Program k) (t : Fin k → ℝ)
    (ht : Regular p t) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) :
    ∀ᶠ m : ℕ in atTop, Separated p (r m) t := by
  apply eventually_all.mpr
  intro ab
  let a := ab.1.val.sub ab.2.val
  by_cases hc : a.coefficient = 0
  · exact Filter.Eventually.of_forall (fun _ h => (h hc).elim)
  · have hp : 0 < |a.eval t| := abs_pos.mpr (ht ab hc)
    have hlim : Tendsto (fun m => r m * (a.slopeMass + 1)) atTop (𝓝 0) := by
      simpa only [zero_mul] using hr.mul_const (a.slopeMass + 1)
    filter_upwards [hlim.eventually (gt_mem_nhds hp)] with m hm
    exact fun _ => hm.le

end
end ImbalancedChen.P1AffineBoxCompleteness
