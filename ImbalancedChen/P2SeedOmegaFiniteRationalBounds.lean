import ImbalancedChen.P2SeedOmegaSampledKappaEnclosure

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual finite-sum lower/upper enclosures with EXACT rational cell weights,
and actual original bad-cost rational enclosures after the paid mesh error.
All floor-query membership, positivity, sample admissibility and analytic
error are produced by this chain. Inputs are causal recurrence data and
finite array length, not a desired coefficient, integral bound or PASS.
No concrete array, sample value or numerical passing gain was evaluated.
-/

namespace ImbalancedChen.P2SeedOmegaFiniteRationalBounds
noncomputable section
open Set
open scoped BigOperators
open P2SeedOmegaBadGlobalCost (actualBadCost)
open P2SeedOmegaFiniteMesh
open P2SeedOmegaFiniteMeshLimit
open P2SeedOmegaRationalCellArea
open P2SeedOmegaFiniteCellSum (weight)
open P2SeedOmegaRationalRangeEnclosure
open P2SeedOmegaSampledKappaEnclosure
open Certificates.P2BuchstabRationalSemantics

theorem rationalArea_nonnegative (n : ℕ) (i j : Fin (n+1)) : 0≤rationalArea n i j := by
  have h : (0:ℝ)≤weight n (some i) (some j) := ENNReal.toReal_nonneg
  rw [actual_weight_eq_rationalArea] at h
  exact_mod_cast h

def lowerSum (m : ℕ) (cs : List NodeEnclosure) (A B : ℚ) (n : ℕ) : ℚ :=
  ∑ i : Fin (n+1),∑ j : Fin (n+1),lowerKappa m cs A B n i j*rationalArea n i j
def upperSum (m : ℕ) (cs : List NodeEnclosure) (A B : ℚ) (n : ℕ) : ℚ :=
  ∑ i : Fin (n+1),∑ j : Fin (n+1),upperKappa m cs A B n i j*rationalArea n i j
def geometricError (n : ℕ) : ℚ := 8192*((10/29-19/58)/(n+1:ℚ))
def actualCostLower (m : ℕ) (cs : List NodeEnclosure) (A B : ℚ) (n : ℕ) : ℚ :=
  lowerSum m cs A B n-geometricError n
def actualCostUpper (m : ℕ) (cs : List NodeEnclosure) (A B : ℚ) (n : ℕ) : ℚ :=
  upperSum m cs A B n+geometricError n

/-- Exact rational finite sums enclose the actual sampled kappa sum
uniformly on the inherited alpha box. The weights are actual areas. -/
theorem actual_mesh_rational_bounds {m : ℕ} {cs : List NodeEnclosure}
    (hc : check m cs=true) {A B : ℚ} (hA : 2≤A) (hAB : A≤B)
    (hcover : queryIndex m (boxTop B)+1<cs.length)
    (n : ℕ) {alpha : ℝ} (ha : alpha ∈ Icc (A:ℝ) (B:ℝ)) :
    (lowerSum m cs A B n:ℝ)≤meshCost n alpha ∧
      meshCost n alpha≤(upperSum m cs A B n:ℝ) := by
  rw [meshCost_eq_rational_weight_sum]
  have hpoint (i j : Fin (n+1)) := actual_sampled_kappa_enclosure hc hA hAB hcover n i j ha
  constructor
  · have h : (∑ i : Fin (n+1),∑ j : Fin (n+1),
        (lowerKappa m cs A B n i j:ℝ)*(rationalArea n i j:ℝ))≤
        (∑ i : Fin (n+1),∑ j : Fin (n+1),
          P2SeedOmegaBadCellSemantics.actualBadKernel alpha (node n i) (node n j)*(rationalArea n i j:ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hw : (0:ℝ)≤(rationalArea n i j:ℝ) := by exact_mod_cast rationalArea_nonnegative n i j
      exact mul_le_mul_of_nonneg_right (hpoint i j).1 hw
    simpa only [lowerSum,Rat.cast_sum,Rat.cast_mul] using h
  · have h : (∑ i : Fin (n+1),∑ j : Fin (n+1),
        P2SeedOmegaBadCellSemantics.actualBadKernel alpha (node n i) (node n j)*(rationalArea n i j:ℝ))≤
        (∑ i : Fin (n+1),∑ j : Fin (n+1),
          (upperKappa m cs A B n i j:ℝ)*(rationalArea n i j:ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hw : (0:ℝ)≤(rationalArea n i j:ℝ) := by exact_mod_cast rationalArea_nonnegative n i j
      exact mul_le_mul_of_nonneg_right (hpoint i j).2 hw
    simpa only [upperSum,Rat.cast_sum,Rat.cast_mul] using h

theorem geometricError_cast (n : ℕ) : (geometricError n:ℝ)=8192*step n := by
  simp only [geometricError,step,logPrimeMeshStep,P2SeedOmegaLiteralFibre.a2,
    P2SeedOmegaLiteralFibre.corner,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,
    Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one,Nat.cast_add,Nat.cast_one]

/-- RATIONAL lower and upper bounds for the actual original double
integral. The geometric error is derived, retained and rounded nowhere. -/
theorem actual_bad_cost_rational_bounds {m : ℕ} {cs : List NodeEnclosure}
    (hc : check m cs=true) {A B : ℚ} (hA : 2≤A) (hAB : A≤B)
    (hcover : queryIndex m (boxTop B)+1<cs.length)
    (n : ℕ) {alpha : ℝ} (ha : alpha ∈ Icc (A:ℝ) (B:ℝ)) :
    (actualCostLower m cs A B n:ℝ)≤actualBadCost alpha ∧
      actualBadCost alpha≤(actualCostUpper m cs A B n:ℝ) := by
  have hm := actual_mesh_rational_bounds hc hA hAB hcover n ha
  have ha2 : (2:ℝ)≤alpha := by
    have h : (2:ℝ)≤(A:ℝ) := by exact_mod_cast hA
    exact h.trans ha.1
  have he := abs_le.mp (actual_finite_mesh_error n ha2)
  have hg := geometricError_cast n
  simp only [actualCostLower,actualCostUpper,Rat.cast_sub,Rat.cast_add]
  constructor <;> linarith only [hm.1,hm.2,he.1,he.2,hg]

/-- The original saving's negative sign and 1/5 normalization reverse
the endpoints, with every genuine analytic error already included. -/
theorem original_negative_bad_contribution_bounds {m : ℕ} {cs : List NodeEnclosure}
    (hc : check m cs=true) {A B : ℚ} (hA : 2≤A) (hAB : A≤B)
    (hcover : queryIndex m (boxTop B)+1<cs.length)
    (n : ℕ) {alpha : ℝ} (ha : alpha ∈ Icc (A:ℝ) (B:ℝ)) :
    ((-actualCostUpper m cs A B n/5:ℚ):ℝ)≤-actualBadCost alpha/5 ∧
      -actualBadCost alpha/5≤((-actualCostLower m cs A B n/5:ℚ):ℝ) := by
  have h := actual_bad_cost_rational_bounds hc hA hAB hcover n ha
  simp only [Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat]
  constructor <;> linarith only [h.1,h.2]

end
end ImbalancedChen.P2SeedOmegaFiniteRationalBounds
