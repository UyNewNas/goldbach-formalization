import ImbalancedChen.P5OriginalKFeedbackBudget
import ImbalancedChen.P5OriginalElevenEventualAssembly
import ImbalancedChen.CurrentP5CausalCellEventualAssembly

/-!
# Fixed original numerical instance of the eventual supplier assembly

SOURCE ONLY; UNCOMPILED. All imports with P5 names are staged draft names.

The original records only certify the combined ordinary-start change and
the combined U3/U4 table gains. They do not give a separate original endpoint
for each changed row. We retain those two genuine groups. The same-mask
floor is charged to L6 and the removed negative gross to joint U10+U11.
Analytic suppliers use the raw joint endpoint. The reserve/surplus charge
is applied only in a subsequent proved weakening; it is not attributed to
the original joint analytic route or either original last occurrence.

The last theorem also adapts the common-causal-cell consumer, keeping the
local actual cell suppliers and an explicit original total-mass identity.
No whole paired-weight mean, hLower, or numerical hCoefficient inequality
is an input to either final export.
-/

namespace ImbalancedChen.P5OriginalCoefficientArithmetic

noncomputable section

open Filter
open scoped BigOperators

def fixedProductDensityCoefficient : ℝ := currentK + allowedDensityDelta

/-- The two starts are kept jointly because their original ordinary delta
is joint. `own-chen-table-insertion-chain`, sections 4-5, locates the
empty-prefix/start change and displaced H248 here; `lower-start-joint-
finite-approximation` identifies I3/I4/I5 as one starting-tree telescope.
`lower-fourth-own-cube-restoration`, eq. own-cube-gain, assigns its
restoration specifically to L2. None of these quantities is a U1011 gain. -/
def originalGroupedStarts : ℝ := 3 * savedL1 + savedL2 +
  ordinaryStartChange - removedH248 + weightedSixIntegrals + slantedRestoration

/-- Only the original two upper costs share the selected later table gains. -/
def originalGroupedU34 : ℝ := savedU3 + savedU4 - 4 * table248to312 - 4 * table312to430
def originalRetainedL6 : ℝ := savedL6 - 4 * replacementSavedFloorPayment

/-- Original raw owner: priority replacements belong to the complete
U10/U11 cover (`global-theorem-completion`, obligation L3). The E0, E1,
and v2 extra gross are all restrictions of the U11 positive parent
majorant, on the same mask, disjoint from priority parents; see
`paired-y6-y11-improvement`, section 3, `positive-pair-deletion-selected-
parent-cover`, and `corpus-renewal-paired-certificate-v2`, section 3.
There is no starting-tree or U34 correction in this analytic endpoint. -/
def originalJointRawCost (k : ℝ) : ℝ :=
  U1011Envelope k - 4 * priorityParentReplacement - 4 * variableRemovedGross k

/-- Numerical phase only: the original two reserves and conservative surplus
weaken the already supplied raw upper bound. They are not required as part
of the original analytic U10/U11 certificate. -/
def originalJointFinalCost (k : ℝ) : ℝ := originalJointRawCost k +
  4 * retainedRoundingSurplus + 8 * eachReserve

theorem originalJointFinalCost_is_weakening (k : ℝ) :
    originalJointRawCost k ≤ originalJointFinalCost k := by
  have hreserve : 0 < eachReserve := by
    rw [eachReserve_value]
    norm_num
  dsimp [originalJointFinalCost]
  linarith [retainedRoundingSurplus_pos]

/-- Explicit analytic-to-numerical phase transition. No start/table gain is
transferred: only a nonnegative reserve/surplus inflation is applied. -/
theorem eventual_joint_final_supplier_of_original_raw
    (E : ℕ → ℕ × ℕ → Prop)
    (hraw : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon10 N + currentChenUpsilon11 N (E N) ≤
        (originalJointRawCost fixedProductDensityCoefficient + 2 * delta) *
          singularNormalization N) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon10 N + currentChenUpsilon11 N (E N) ≤
        (originalJointFinalCost fixedProductDensityCoefficient + 2 * delta) *
          singularNormalization N := by
  intro delta hdelta
  filter_upwards [hraw delta hdelta] with N hN
  intro hEven
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (hN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add_right (originalJointFinalCost_is_weakening fixedProductDensityCoefficient)
      (2 * delta)) hH)

def originalGroupedCoefficient (k : ℝ) : ℝ :=
  originalGroupedStarts - originalGroupedU34 + savedL5 + originalRetainedL6 -
    2 * U7Envelope k - U8Envelope k - U9Envelope k - originalJointFinalCost k

/-- All original gains and losses occur once. No aggregate gain is assigned
to an arbitrary individual row merely to force the coefficient identity. -/
theorem originalGroupedCoefficient_exact (k : ℝ) :
    originalGroupedCoefficient k =
      4 * (adoptedRawWithDensityCoefficient k - 2 * eachReserve) := by
  have hbase := directAtK0_eq_adopted_add_surplus
  dsimp [directAtK0] at hbase
  dsimp [originalGroupedCoefficient, originalGroupedStarts, originalGroupedU34,
    originalRetainedL6, originalJointFinalCost, originalJointRawCost,
    adoptedRawWithDensityCoefficient,
    originalVariableRoot, root] at ⊢
  dsimp [savedRoot, root] at hbase ⊢
  linear_combination 4 * hbase

theorem fixed_originalGroupedCoefficient_gt_currentC :
    4 * currentC < originalGroupedCoefficient fixedProductDensityCoefficient := by
  have h := (currentC_of_density_coefficient_delta
    allowedDensityDelta_pos.le (le_refl allowedDensityDelta)).2.2
  rw [originalGroupedCoefficient_exact]
  change currentC < adoptedRawWithDensityCoefficient fixedProductDensityCoefficient -
    2 * eachReserve at h
  linarith

/-- Actual per-group suppliers, with every ungrouped occurrence visible.
The two joint groups are forced by the original selected data, not by an
assumed whole-mean bound. The exact accumulated error is ten local units. -/
theorem eventual_mean_of_fixed_original_grouped_suppliers
    (E : ℕ → ℕ × ℕ → Prop)
    (hstarts : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (originalGroupedStarts - delta) * singularNormalization N ≤
        3 * currentChenUpsilon1 N + currentChenUpsilon2 N)
    (h34 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon3 N + currentChenUpsilon4 N ≤
        (originalGroupedU34 + delta) * singularNormalization N)
    (h5 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (savedL5 - delta) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h6 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (originalRetainedL6 - delta) * singularNormalization N ≤ currentChenUpsilon6 N (E N))
    (h7 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon7 N ≤ (U7Envelope fixedProductDensityCoefficient + delta) *
        singularNormalization N)
    (h8 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon8 N ≤ (U8Envelope fixedProductDensityCoefficient + delta) *
        singularNormalization N)
    (h9 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤ (U9Envelope fixedProductDensityCoefficient + delta) *
        singularNormalization N)
    (h1011 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon10 N + currentChenUpsilon11 N (E N) ≤
        (originalJointRawCost fixedProductDensityCoefficient + 2 * delta) *
          singularNormalization N) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      (originalGroupedCoefficient fixedProductDensityCoefficient - epsilon) *
        singularNormalization N ≤ currentChenPairedPrimeSum N (E N) := by
  intro epsilon hepsilon
  have hd : 0 < epsilon / 10 := by linarith
  filter_upwards [hstarts (epsilon / 10) hd, h34 (epsilon / 10) hd,
    h5 (epsilon / 10) hd, h6 (epsilon / 10) hd, h7 (epsilon / 10) hd,
    h8 (epsilon / 10) hd, h9 (epsilon / 10) hd,
    eventual_joint_final_supplier_of_original_raw E h1011 (epsilon / 10) hd]
    with N hNstarts hN34 hN5 hN6 hN7 hN8 hN9 hN1011
  intro hEven
  have hs := hNstarts hEven
  have h34' := hN34 hEven
  have h5' := hN5 hEven
  have h6' := hN6 hEven
  have h7' := hN7 hEven
  have h8' := hN8 hEven
  have h9' := hN9 hEven
  have h1011' := hN1011 hEven
  rw [currentChenPairedPrimeSum_eq_upsilon]
  dsimp [originalGroupedCoefficient]
  nlinarith only [hs, h34', h5', h6', h7', h8', h9', h1011']

/-- The original numerical coefficient condition is discharged inside this
adapter. All actual analytic suppliers remain explicit and unproved here. -/
theorem eventual_D12_of_fixed_original_grouped_suppliers
    (E : ℕ → ℕ × ℕ → Prop)
    (hstarts : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (originalGroupedStarts - delta) * singularNormalization N ≤
        3 * currentChenUpsilon1 N + currentChenUpsilon2 N)
    (h34 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon3 N + currentChenUpsilon4 N ≤
        (originalGroupedU34 + delta) * singularNormalization N)
    (h5 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (savedL5 - delta) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h6 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (originalRetainedL6 - delta) * singularNormalization N ≤ currentChenUpsilon6 N (E N))
    (h7 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon7 N ≤ (U7Envelope fixedProductDensityCoefficient + delta) *
        singularNormalization N)
    (h8 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon8 N ≤ (U8Envelope fixedProductDensityCoefficient + delta) *
        singularNormalization N)
    (h9 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤ (U9Envelope fixedProductDensityCoefficient + delta) *
        singularNormalization N)
    (h1011 : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon10 N + currentChenUpsilon11 N (E N) ≤
        (originalJointRawCost fixedProductDensityCoefficient + 2 * delta) *
          singularNormalization N) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ) := by
  apply P5OriginalElevenEventualAssembly.eventual_D12_of_coefficient E
    (originalGroupedCoefficient fixedProductDensityCoefficient)
    fixed_originalGroupedCoefficient_gt_currentC.le
  exact eventual_mean_of_fixed_original_grouped_suppliers E
    hstarts h34 h5 h6 h7 h8 h9 h1011

/-- A genuine common-causal-cell certificate may compute this same explicit
mass sum instead of splitting joint original gains among occurrences.
The equality is a finite data-binding obligation, not a whole-weight mean.
It must be proved from the actual selected cell masses; no cell map is
fabricated from the scalar numerical endpoint in this adapter. -/
theorem eventual_D12_of_fixed_original_causal_masses
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ℕ → ℕ × ℕ → Prop) (label : ℕ → ℕ → ι)
    (mass amplification priority : ι → ℝ) (hpriority : ∀ a, 0 < priority a)
    (hlocal : ∀ a, ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (mass a - |amplification a| * delta) * singularNormalization N ≤
        p5CausalCellSignedLedger N (E N) (label N) a)
    (hmass : (∑ a, mass a) = originalGroupedCoefficient fixedProductDensityCoefficient) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ) := by
  intro epsilon hepsilon
  apply p5CausalClassifiedCellAssembly_eventual_D12 E label mass amplification priority
    hpriority hlocal ?_ epsilon hepsilon
  rw [hmass]
  exact fixed_originalGroupedCoefficient_gt_currentC.le

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
