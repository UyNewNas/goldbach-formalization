import ImbalancedChen.AffinePrimeGates
import ImbalancedChen.RealHalfProductMass

/-!
# P4B: explicit continuous positive outer ramps for actual log gates

YELLOW / SOURCE ONLY / UNCOMPILED.

The scalar ramp is exactly `min 1 (max 0 (1 + x / delta))`.
The actual prime imbalance gate is derived from the rpow/log equivalence;
it is not an independent hypothesis.  Finite products supply actual tuple
weights for finite intersections of strict affine gates.  These are
continuous geometric envelopes only: no derivative bound, P3 packet licence,
Siegel--Walfisz estimate or boundary lattice-point estimate is asserted.
-/

namespace ImbalancedChen
namespace P4B

noncomputable section
open scoped Classical BigOperators

/-- Explicit upper ramp, equal to one on the closed positive half-line. -/
def logGateOuterRamp (delta x : ℝ) : ℝ :=
  min 1 (max 0 (1 + x / delta))

/-- Continuity is unconditional because division is by a fixed constant. -/
theorem continuous_logGateOuterRamp (delta : ℝ) :
    Continuous (logGateOuterRamp delta) := by
  unfold logGateOuterRamp
  exact continuous_const.min
    (continuous_const.max (continuous_const.add (continuous_id.div_const delta)))

theorem logGateOuterRamp_bounds (delta x : ℝ) :
    0 ≤ logGateOuterRamp delta x ∧ logGateOuterRamp delta x ≤ 1 := by
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem logGateOuterRamp_eq_one {delta x : ℝ}
    (hdelta : 0 < delta) (hx : 0 ≤ x) :
    logGateOuterRamp delta x = 1 := by
  have hterm : 1 ≤ 1 + x / delta := by
    linarith [div_nonneg hx hdelta.le]
  exact min_eq_left (hterm.trans (le_max_right _ _))

theorem logGateOuterRamp_eq_zero {delta x : ℝ}
    (hdelta : 0 < delta) (hx : x ≤ -delta) :
    logGateOuterRamp delta x = 0 := by
  have hdiv : x / delta ≤ -1 := (div_le_iff₀ hdelta).mpr (by linarith)
  have hterm : 1 + x / delta ≤ 0 := by linarith
  simp only [logGateOuterRamp, max_eq_left hterm, min_eq_right zero_le_one]

/-- The literal strict indicator is dominated, including the zero wall. -/
theorem logGateOuterRamp_indicator_le {delta : ℝ}
    (hdelta : 0 < delta) (x : ℝ) :
    (if 0 < x then (1 : ℝ) else 0) ≤ logGateOuterRamp delta x := by
  by_cases hx : 0 < x
  · simpa only [if_pos hx, logGateOuterRamp_eq_one hdelta hx.le] using (le_refl (1 : ℝ))
  · rw [if_neg hx]
    exact (logGateOuterRamp_bounds delta x).1

/-- Nonzero weight lies inside the strict expanded gate. -/
theorem logGateOuterRamp_nonzero_support {delta x : ℝ}
    (hdelta : 0 < delta) (hnonzero : logGateOuterRamp delta x ≠ 0) :
    -delta < x := by
  by_contra h
  exact hnonzero (logGateOuterRamp_eq_zero hdelta (le_of_not_gt h))

/-- The actual surplus is nonnegative and can only occur in `-delta < x ≤ 0`.
In particular, the strict indicator wall at zero remains in the surplus. -/
theorem logGateOuterRamp_surplus_support {delta x : ℝ}
    (hdelta : 0 < delta)
    (hsurplus : logGateOuterRamp delta x - (if 0 < x then (1 : ℝ) else 0) ≠ 0) :
    -delta < x ∧ x ≤ 0 := by
  constructor
  · by_contra h
    have hx : x ≤ -delta := le_of_not_gt h
    have hxnonpos : x ≤ 0 := by linarith
    apply hsurplus
    rw [logGateOuterRamp_eq_zero hdelta hx, if_neg (not_lt.mpr hxnonpos)]
    ring
  · by_contra h
    have hx : 0 < x := lt_of_not_ge h
    apply hsurplus
    rw [logGateOuterRamp_eq_one hdelta hx.le, if_pos hx]
    ring

theorem logGateOuterRamp_surplus_nonneg {delta : ℝ}
    (hdelta : 0 < delta) (x : ℝ) :
    0 ≤ logGateOuterRamp delta x - (if 0 < x then (1 : ℝ) else 0) := by
  exact sub_nonneg.mpr (logGateOuterRamp_indicator_le hdelta x)

/-- The exact rpow/log dictionary for positive real prime variables.
No sign assumption on `b` is needed for this identity. -/
theorem rpow_lt_iff_positive_logGate {q r b : ℝ}
    (hq : 0 < q) (hr : 0 < r) :
    q ^ b < r ↔ 0 < Real.log r - b * Real.log q := by
  have hpow : 0 < q ^ b := Real.rpow_pos_of_pos hq b
  constructor
  · intro hbad
    have hlog := (Real.log_lt_log_iff hpow hr).mpr hbad
    rw [Real.log_rpow hq] at hlog
    exact sub_pos.mpr hlog
  · intro hgate
    apply (Real.log_lt_log_iff hpow hr).mp
    rw [Real.log_rpow hq]
    exact sub_pos.mp hgate

/-- The literal smaller/larger prime imbalance gate on integer prime pairs. -/
def primeImbalanceLogGate (b : ℝ) (q r : ℕ) : ℝ :=
  Real.log (r : ℝ) - b * Real.log (q : ℝ)

theorem prime_badness_iff_positive_logGate (b : ℝ) {q r : ℕ}
    (hq : Nat.Prime q) (hr : Nat.Prime r) :
    (q : ℝ) ^ b < (r : ℝ) ↔ 0 < primeImbalanceLogGate b q r := by
  exact rpow_lt_iff_positive_logGate
    (Nat.cast_pos.mpr hq.pos) (Nat.cast_pos.mpr hr.pos)

/-- Actual prime badness is dominated after deriving its log gate. -/
theorem prime_badness_indicator_le_logGateOuterRamp
    {delta : ℝ} (hdelta : 0 < delta) (b : ℝ) {q r : ℕ}
    (hq : Nat.Prime q) (hr : Nat.Prime r) :
    (if (q : ℝ) ^ b < (r : ℝ) then (1 : ℝ) else 0) ≤
      logGateOuterRamp delta (primeImbalanceLogGate b q r) := by
  rw [prime_badness_iff_positive_logGate b hq hr]
  exact logGateOuterRamp_indicator_le hdelta _

/-- The surplus for the actual prime imbalance is confined to its explicit
logarithmic boundary strip, retaining the weak upper edge. -/
theorem prime_badness_outerRamp_surplus_support
    {delta : ℝ} (hdelta : 0 < delta) (b : ℝ) {q r : ℕ}
    (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hsurplus : logGateOuterRamp delta (primeImbalanceLogGate b q r) -
      (if (q : ℝ) ^ b < (r : ℝ) then (1 : ℝ) else 0) ≠ 0) :
    -delta < Real.log (r : ℝ) - b * Real.log (q : ℝ) ∧
      Real.log (r : ℝ) ≤ b * Real.log (q : ℝ) := by
  rw [prime_badness_iff_positive_logGate b hq hr] at hsurplus
  obtain ⟨hleft, hright⟩ := logGateOuterRamp_surplus_support hdelta hsurplus
  refine ⟨hleft, ?_⟩
  exact sub_nonpos.mp hright

/-- Actual tuple weight for a finite conjunction `L i x < c i`.
Each gate is the explicit affine margin `c i - L i x`. -/
def affineTupleOuterRamp {d : ℕ} {ι : Type*}
    (I : Finset ι) (L : ι → (Fin d → ℝ) →L[ℝ] ℝ)
    (c : ι → ℝ) (delta : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ i ∈ I, logGateOuterRamp delta (c i - L i x)

theorem continuous_affineTupleOuterRamp {d : ℕ} {ι : Type*}
    (I : Finset ι) (L : ι → (Fin d → ℝ) →L[ℝ] ℝ)
    (c : ι → ℝ) (delta : ℝ) :
    Continuous (affineTupleOuterRamp I L c delta) := by
  unfold affineTupleOuterRamp
  exact continuous_finsetProd _ (fun i _ =>
    (continuous_logGateOuterRamp delta).comp
      (continuous_const.sub (L i).continuous))

theorem affineTupleOuterRamp_bounds {d : ℕ} {ι : Type*}
    (I : Finset ι) (L : ι → (Fin d → ℝ) →L[ℝ] ℝ)
    (c : ι → ℝ) (delta : ℝ) (x : Fin d → ℝ) :
    0 ≤ affineTupleOuterRamp I L c delta x ∧
      affineTupleOuterRamp I L c delta x ≤ 1 := by
  refine ⟨Finset.prod_nonneg (fun i _ => (logGateOuterRamp_bounds _ _).1), ?_⟩
  exact Finset.prod_le_one (fun i _ => (logGateOuterRamp_bounds _ _).1)
    (fun i _ => (logGateOuterRamp_bounds _ _).2)

theorem affineTupleOuterRamp_eq_one_of_nonneg {d : ℕ} {ι : Type*}
    (I : Finset ι) (L : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) {x : Fin d → ℝ}
    (hx : ∀ i ∈ I, 0 ≤ c i - L i x) :
    affineTupleOuterRamp I L c delta x = 1 := by
  unfold affineTupleOuterRamp
  exact Finset.prod_eq_one (fun i hi => logGateOuterRamp_eq_one hdelta (hx i hi))

/-- The product dominates the strict conjunction, including empty families. -/
theorem affineTuple_strict_indicator_le_outerRamp {d : ℕ} {ι : Type*}
    (I : Finset ι) (L : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) (x : Fin d → ℝ) :
    (if ∀ i ∈ I, L i x < c i then (1 : ℝ) else 0) ≤
      affineTupleOuterRamp I L c delta x := by
  classical
  by_cases hx : ∀ i ∈ I, L i x < c i
  · simpa only [if_pos hx, affineTupleOuterRamp_eq_one_of_nonneg I L c hdelta
      (fun i hi => sub_nonneg.mpr (hx i hi).le)] using (le_refl (1 : ℝ))
  · rw [if_neg hx]
    exact (affineTupleOuterRamp_bounds I L c delta x).1

/-- A nonzero product forces every original affine margin above `-delta`. -/
theorem affineTupleOuterRamp_nonzero_support {d : ℕ} {ι : Type*}
    (I : Finset ι) (L : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) {x : Fin d → ℝ}
    (hnonzero : affineTupleOuterRamp I L c delta x ≠ 0) :
    ∀ i ∈ I, -delta < c i - L i x := by
  classical
  intro i hi
  apply logGateOuterRamp_nonzero_support hdelta
  intro hzero
  apply hnonzero
  exact Finset.prod_eq_zero hi hzero

/-- Nonzero surplus lies in the expanded conjunction and meets at least
one weakly failed original gate.  No boundary-measure estimate is assumed. -/
theorem affineTupleOuterRamp_surplus_support {d : ℕ} {ι : Type*}
    (I : Finset ι) (L : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) {x : Fin d → ℝ}
    (hsurplus : affineTupleOuterRamp I L c delta x -
      (if ∀ i ∈ I, L i x < c i then (1 : ℝ) else 0) ≠ 0) :
    (∀ i ∈ I, -delta < c i - L i x) ∧
      ∃ i ∈ I, c i - L i x ≤ 0 := by
  classical
  have hfailed : ¬ ∀ i ∈ I, L i x < c i := by
    intro hx
    apply hsurplus
    rw [affineTupleOuterRamp_eq_one_of_nonneg I L c hdelta
      (fun i hi => sub_nonneg.mpr (hx i hi).le), if_pos hx]
    ring
  have hnonzero : affineTupleOuterRamp I L c delta x ≠ 0 := by
    intro hzero
    apply hsurplus
    rw [hzero, if_neg hfailed]
    ring
  refine ⟨affineTupleOuterRamp_nonzero_support I L c hdelta hnonzero, ?_⟩
  push_neg at hfailed
  obtain ⟨i, hi, hgate⟩ := hfailed
  exact ⟨i, hi, sub_nonpos.mpr hgate⟩

end
end P4B
end ImbalancedChen