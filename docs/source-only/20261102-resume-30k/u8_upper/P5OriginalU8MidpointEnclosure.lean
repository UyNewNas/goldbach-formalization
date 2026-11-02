import ImbalancedChen.P5OriginalU8ScalarProducer
import ImbalancedChen.P5OriginalSignedMidpoint
import ImbalancedChen.P2GuardedReciprocalRounding
import ImbalancedChen.P2ContinuousSieveRational

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Actual original U8, signed midpoint enclosure. The logarithm nodes and
the full closed-cell second derivative are enclosed by proved rational
Taylor bounds and signed four-corner interval operations. The 1/24
Peano identity is imported from the shared K/u7_sharp module. There is
no assumed derivative enclosure, integral endpoint, or numerical result.

The functions below are exact rational refinements of the archived
producer's real expression and partition. They are NOT asserted to be
the saved Q80 execution. Authentication of that execution or an exact
comparison of these sums to the unchanged saved endpoint remains OPEN.
-/

namespace ImbalancedChen.P5OriginalU8MidpointEnclosure

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open P5OriginalU8ScalarProducer P2U8UniformRationalCover
open Certificates.P2DirectedLogRounding P2ContinuousSieveRational

def inverseBounds (l r : ℚ) : Enclosure := (⟨l, r⟩ : Enclosure).reciprocalBounds

theorem inverseBounds_contains {l r : ℚ} {t : ℝ}
    (hl : 0 < l) (ht : (l : ℝ) ≤ t ∧ t ≤ (r : ℝ)) :
    (inverseBounds l r).Contains (1 / t) := by
  have hlr : l ≤ r := by exact_mod_cast ht.1.trans ht.2
  have hc : (⟨l, r⟩ : Enclosure).reciprocalCheck = true := by
    apply decide_eq_true_iff.mpr
    exact ⟨hlr, Or.inl hl⟩
  exact Enclosure.reciprocalBounds_contains ht hc

/-- log(q-1) at q=3-3t is exactly the original log(2-3t). -/
def logarithmBounds (n : ℕ) (l r : ℚ) : Enclosure :=
  ⟨logLower n (3 - 3 * r), logUpper n (3 - 3 * l)⟩

theorem logarithmBounds_contains (n : ℕ) {l r : ℚ} {t : ℝ}
    (hr : r ≤ 1 / 3) (ht : (l : ℝ) ≤ t ∧ t ≤ (r : ℝ)) :
    (logarithmBounds n l r).Contains (producerLog t) := by
  have hlr : l ≤ r := by exact_mod_cast ht.1.trans ht.2
  have hql : 2 ≤ 3 - 3 * r := by linarith only [hr]
  have hqu : 2 ≤ 3 - 3 * l := by linarith only [hr, hlr]
  have hlo := (log_bounds n (3 - 3 * r) hql).1
  have hhi := (log_bounds n (3 - 3 * l) hqu).2
  have hrl : (r : ℝ) ≤ 1 / 3 := by exact_mod_cast hr
  have harg : 0 < 2 - 3 * (r : ℝ) := by linarith only [hrl]
  have hargt : 0 < 2 - 3 * t := by linarith only [hrl, ht.2]
  have harglo : 2 - 3 * (r : ℝ) ≤ 2 - 3 * t := by linarith only [ht.2]
  have harghi : 2 - 3 * t ≤ 2 - 3 * (l : ℝ) := by linarith only [ht.1]
  have hlcast : ((3 - 3 * r : ℚ) : ℝ) - 1 = 2 - 3 * (r : ℝ) := by push_cast; ring
  have hucast : ((3 - 3 * l : ℚ) : ℝ) - 1 = 2 - 3 * (l : ℝ) := by push_cast; ring
  rw [hlcast] at hlo
  rw [hucast] at hhi
  exact ⟨hlo.trans (Real.log_le_log harg harglo),
    (Real.log_le_log hargt harghi).trans hhi⟩

def valueBounds (n : ℕ) (q : ℚ) : Enclosure :=
  (logarithmBounds n q q).mul
    ((inverseBounds q q).add (inverseBounds (1 - q) (1 - q)))

/-- Node enclosure of the producer's true scalar, not a saved-value port. -/
theorem valueBounds_contains (n : ℕ) (q : ℚ)
    (hql : 417 / 5000 ≤ q) (hqu : q ≤ 1 / 3) :
    (valueBounds n q).Contains (producerValue (q : ℝ)) := by
  have hq0 : 0 < q := by linarith only [hql]
  have hq1 : 0 < 1 - q := by linarith only [hqu]
  have hL := logarithmBounds_contains n hqu (show (q : ℝ) ≤ q ∧ (q : ℝ) ≤ q from ⟨le_rfl, le_rfl⟩)
  have hT := inverseBounds_contains hq0 (show (q : ℝ) ≤ q ∧ (q : ℝ) ≤ q from ⟨le_rfl, le_rfl⟩)
  have hW : (inverseBounds (1 - q) (1 - q)).Contains (1 / (1 - (q : ℝ))) := by
    apply inverseBounds_contains hq1
    simp
  exact Enclosure.mul_contains hL (Enclosure.add_contains hT hW)

/-- The archived main_second expression, evaluated by signed exact
rational interval operations. Every repeated occurrence is retained. -/
def secondBounds (n : ℕ) (l r : ℚ) : Enclosure :=
  let T := inverseBounds l r
  let W := inverseBounds (1 - r) (1 - l)
  let A := inverseBounds (2 - 3 * r) (2 - 3 * l)
  let L := logarithmBounds n l r
  let L1 := (Enclosure.point (-3)).mul A
  let L2 := (Enclosure.point (-9)).mul (A.mul A)
  let R := T.add W
  let R1 := ((Enclosure.point (-1)).mul (T.mul T)).add (W.mul W)
  let R2 := ((Enclosure.point 2).mul ((T.mul T).mul T)).add
    ((Enclosure.point 2).mul ((W.mul W).mul W))
  ((L2.mul R).add (((Enclosure.point 2).mul L1).mul R1)).add (L.mul R2)

/-- A genuine full-cell bound for the actual second derivative. The
input conditions are only original rational endpoints and point membership. -/
theorem secondBounds_contains (n : ℕ) {l r : ℚ} {t : ℝ}
    (hl : 417 / 5000 ≤ l) (hr : r ≤ 1 / 3)
    (ht : (l : ℝ) ≤ t ∧ t ≤ (r : ℝ)) :
    (secondBounds n l r).Contains (producerSecond t) := by
  have hl0 : 0 < l := by linarith only [hl]
  have hw0 : 0 < 1 - r := by linarith only [hr]
  have ha0 : 0 < 2 - 3 * r := by linarith only [hr]
  have hT := inverseBounds_contains hl0 ht
  have hW : (inverseBounds (1 - r) (1 - l)).Contains (1 / (1 - t)) := by
    apply inverseBounds_contains hw0
    push_cast
    constructor <;> linarith only [ht.1, ht.2]
  have hA : (inverseBounds (2 - 3 * r) (2 - 3 * l)).Contains (1 / (2 - 3 * t)) := by
    apply inverseBounds_contains ha0
    push_cast
    constructor <;> linarith only [ht.1, ht.2]
  have hL := logarithmBounds_contains n hr ht
  have hL1 := Enclosure.mul_contains (Enclosure.point_contains (-3)) hA
  have hL2 := Enclosure.mul_contains (Enclosure.point_contains (-9))
    (Enclosure.mul_contains hA hA)
  have hR := Enclosure.add_contains hT hW
  have hR1 := Enclosure.add_contains
    (Enclosure.mul_contains (Enclosure.point_contains (-1)) (Enclosure.mul_contains hT hT))
    (Enclosure.mul_contains hW hW)
  have hR2 := Enclosure.add_contains
    (Enclosure.mul_contains (Enclosure.point_contains 2)
      (Enclosure.mul_contains (Enclosure.mul_contains hT hT) hT))
    (Enclosure.mul_contains (Enclosure.point_contains 2)
      (Enclosure.mul_contains (Enclosure.mul_contains hW hW) hW))
  have hsum := Enclosure.add_contains
    (Enclosure.add_contains (Enclosure.mul_contains hL2 hR)
      (Enclosure.mul_contains (Enclosure.mul_contains (Enclosure.point_contains 2) hL1) hR1))
    (Enclosure.mul_contains hL hR2)
  change (secondBounds n l r).Contains _ at hsum
  convert hsum using 1 <;>
    simp only [producerSecond, producerLogFirst, producerLogSecond, reciprocal,
      reciprocalFirst, reciprocalSecond, div_eq_mul_inv, inv_pow, Rat.cast_neg,
      Rat.cast_ofNat, Rat.cast_one, one_mul] <;> ring

def panelLower (n : ℕ) (l r : ℚ) : ℚ :=
  (r - l) * ((valueBounds n ((l + r) / 2)).lower +
    (secondBounds n l r).lower * (r - l) ^ 2 / 24)
def panelUpper (n : ℕ) (l r : ℚ) : ℚ :=
  (r - l) * ((valueBounds n ((l + r) / 2)).upper +
    (secondBounds n l r).upper * (r - l) ^ 2 / 24)

/-- Signed 1/24 integration of the real original U8 scalar. Neither
curvature positivity nor an analytic bound is an input. -/
theorem panel_enclosure (n : ℕ) (l r : ℚ)
    (hl : 417 / 5000 ≤ l) (hr : r ≤ 1 / 3) (hlr : l ≤ r) :
    (panelLower n l r : ℝ) ≤ (∫ t in (l : ℝ)..(r : ℝ), logDensity t) ∧
      (∫ t in (l : ℝ)..(r : ℝ), logDensity t) ≤ (panelUpper n l r : ℝ) := by
  have hlR : (417 / 5000 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hrR : (r : ℝ) ≤ 1 / 3 := by exact_mod_cast hr
  have hlrR : (l : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlr
  have hsub : Icc (l : ℝ) (r : ℝ) ⊆ Icc (417 / 5000 : ℝ) (1 / 3 : ℝ) :=
    fun t ht => ⟨hlR.trans ht.1, ht.2.trans hrR⟩
  have hf : ∀ t ∈ Icc (l : ℝ) (r : ℝ), HasDerivAt producerValue (producerFirst t) t := by
    intro t ht
    obtain ⟨ht0, ht1, harg⟩ := original_interval_guards (hsub ht)
    exact producerValue_hasDerivAt ht0 (by linarith only [ht1]) (zero_lt_one.trans_le harg)
  have hf' : ∀ t ∈ Icc (l : ℝ) (r : ℝ), HasDerivAt producerFirst (producerSecond t) t := by
    intro t ht
    obtain ⟨ht0, ht1, harg⟩ := original_interval_guards (hsub ht)
    exact producerFirst_hasDerivAt ht0 (by linarith only [ht1]) (zero_lt_one.trans_le harg)
  have hM := P5OriginalSignedMidpoint.midpoint_bounds hlrR hf hf'
    (continuousOn_producerSecond.mono hsub)
    (fun t ht => secondBounds_contains n hl hr ht)
  have hIntegral : (∫ t in (l : ℝ)..(r : ℝ), producerValue t) =
      ∫ t in (l : ℝ)..(r : ℝ), logDensity t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hlrR] at ht
    obtain ⟨ht0, ht1, _⟩ := original_interval_guards (hsub ht)
    exact producerValue_eq_logDensity ht0 (by linarith only [ht1])
  rw [hIntegral] at hM
  have hmid : (((l + r) / 2 : ℚ) : ℝ) = ((l : ℝ) + (r : ℝ)) / 2 := by push_cast; rfl
  rw [← hmid] at hM
  have hnode := valueBounds_contains n ((l + r) / 2)
    (by linarith only [hl, hlr]) (by linarith only [hr, hlr])
  have hw : 0 ≤ (r : ℝ) - (l : ℝ) := sub_nonneg.mpr hlrR
  constructor
  · have h := (mul_le_mul_of_nonneg_left (add_le_add_right hnode.1
      ((secondBounds n l r).lower * ((r : ℝ) - (l : ℝ)) ^ 2 / 24)) hw).trans hM.1
    simpa only [panelLower, Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_sub,
      Rat.cast_pow, Rat.cast_ofNat] using h
  · have h := hM.2.trans (mul_le_mul_of_nonneg_left (add_le_add_right hnode.2
      ((secondBounds n l r).upper * ((r : ℝ) - (l : ℝ)) ^ 2 / 24)) hw)
    simpa only [panelUpper, Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_sub,
      Rat.cast_pow, Rat.cast_ofNat] using h

def rationalLower (n m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m, panelLower n (mesh m k) (mesh m (k + 1))
def rationalUpper (n m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m, panelUpper n (mesh m k) (mesh m (k + 1))

/-- Complete actual-domain midpoint enclosure. All finite rational terms
remain unevaluated; the theorem itself has no numerical-check premise. -/
theorem original_integral_midpoint_enclosure (n m : ℕ) (hm : 0 < m) :
    (rationalLower n m : ℝ) ≤ currentChenUpsilon8HarmonicIntegral ∧
      currentChenUpsilon8HarmonicIntegral ≤ (rationalUpper n m : ℝ) := by
  rw [original_integral_eq_cell_sum m hm]
  have hcell (k : ℕ) (hk : k ∈ Finset.range m) := panel_enclosure n
    (mesh m k) (mesh m (k + 1))
    ((mesh_bounds m hm k (Finset.mem_range.mp hk).le).1)
    ((mesh_bounds m hm (k + 1) (by have := Finset.mem_range.mp hk; omega)).2)
    (mesh_monotone m hm (Nat.le_succ k))
  constructor
  · simpa only [rationalLower, Rat.cast_sum] using Finset.sum_le_sum (fun k hk => (hcell k hk).1)
  · simpa only [rationalUpper, Rat.cast_sum] using Finset.sum_le_sum (fun k hk => (hcell k hk).2)

theorem original_1024_midpoint_enclosure :
    (rationalLower 32 1024 : ℝ) ≤ currentChenUpsilon8HarmonicIntegral ∧
      currentChenUpsilon8HarmonicIntegral ≤ (rationalUpper 32 1024 : ℝ) :=
  original_integral_midpoint_enclosure 32 1024 (by norm_num)

end

end ImbalancedChen.P5OriginalU8MidpointEnclosure
