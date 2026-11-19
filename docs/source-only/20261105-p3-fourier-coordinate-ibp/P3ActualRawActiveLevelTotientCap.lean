import ImbalancedChen.P3ActualRawPhysicalRhoTotientCap
import ImbalancedChen.ActualSmallRoughAttachment
import Mathlib.Tactic

/-!
P3.6, manuscript pin 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §3(T), §4(F).

The displayed small Rosser divisor support contains ALL divisors of the
presieving prime product, even when both literal Rosser weights vanish.
Its size cannot reasonably be bounded by the small Rosser level L.

This file removes those inactive divisors from the physical positive
reciprocal-totient mass using the actual PRODUCTION nonzero-fibre
theorem, before applying a true two-factor totient bound. Thus A only
has to dominate L, not every displayed small divisor. The rough
retained factor bound B is still explicit, and still needs producer
verification. The coefficient remains exactly the raw REAL
actualSmallRoughRho at the original full INTEGER modulus. No analytic
PP estimate, compiler rho_N identification or target conclusion is an
assumption.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualRawActiveLevelTotientCap
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualRawPhysicalRhoTotientCap
open ImbalancedChen.P3ActualSignedPairTotientCap
open ImbalancedChen.P3ActualPhysicalTotientConvolution

/-- The *effective* small support at the literal strict Rosser level.
The original displayed support and coefficients are not redefined. -/
def activeSmallRosserByLevel (N cap : ℕ) (w L : ℝ) : Finset ℕ :=
  (actualSmallRosserSupport N cap w).filter (fun a => (a : ℝ) < L)

/-- Retain exactly the physically nonzero raw moduli. In particular,
this is not a replacement for the final integer compiler rho_N. -/
def activeRawPhysicalModuli
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : Finset ℕ :=
  (actualSmallRoughModuli retainOdd N cap w z).filter
    (fun q => actualSmallRoughRho retainOdd N cap w z L q ≠ 0)

/-- Every occupied raw physical modulus is represented with a genuine
small factor *strictly below L*. The entire original rough first-exit
support and the exact physical integer product are retained. -/
theorem active_raw_physical_moduli_subset
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    activeRawPhysicalModuli retainOdd N cap w z L ⊆
      smallRoughModuli (activeSmallRosserByLevel N cap w L)
        (fixedRoughSupport retainOdd N cap w z) := by
  classical
  intro q hq
  have hnonzero :
      actualSmallRoughRho retainOdd N cap w z L q ≠ 0 :=
    (Finset.mem_filter.mp hq).2
  obtain ⟨a, ha, b, hb, hprod, haL, _⟩ :=
    actualSmallRoughRho_ne_zero_factors retainOdd N cap w z L hnonzero
  unfold smallRoughModuli
  refine Finset.mem_image.mpr ⟨(a, b), ?_, hprod.symm⟩
  change (a, b) ∈
    (activeSmallRosserByLevel N cap w L).product
      (fixedRoughSupport retainOdd N cap w z)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨ha, haL⟩, hb⟩

/-- Physical reciprocal-totient cap for the genuine nonzero RAW
attachment. Unlike the earlier displayed-support theorem, this has
NO premise bounding every divisor of the full small presieving product.
Only the strict Rosser level L needs to fit in A. The true rough
first-exit support still needs its own cap B. -/
theorem actual_raw_physical_mass_le_active_level_caps
    (retainOdd : List ℕ → Bool) (N cap A B : ℕ) (w z L : ℝ)
    (hLA : L ≤ (A : ℝ))
    (hB : ∀ b ∈ fixedRoughSupport retainOdd N cap w z, b ≤ B) :
    actualRawPhysicalTotientMass retainOdd N cap w z L ≤
      logTotientCap A * logTotientCap B := by
  classical
  let s := actualSmallRosserSupport N cap w
  let r := fixedRoughSupport retainOdd N cap w z
  let t := activeSmallRosserByLevel N cap w L
  let Q := actualSmallRoughModuli retainOdd N cap w z
  let Q' := smallRoughModuli t r
  let rho := actualSmallRoughRho retainOdd N cap w z L
  let F : ℕ → ℝ := fun q => |rho q| * (Nat.totient q : ℝ)⁻¹
  have hs : ∀ a ∈ t, SmallPrimeSupportedAt w a := by
    intro a ha
    exact actualSmallRosserSupport_smallPrimeSupportedAt N cap w
      (Finset.mem_filter.mp ha).1
  have hr : ∀ b ∈ r, RoughPrimeSupportedAt w b := by
    intro b hb
    exact fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hb
  have htcap : t ⊆ Finset.Icc 1 A := by
    intro a ha
    have ha0 : 0 < a :=
      Nat.pos_of_ne_zero (hs a ha).1
    have haReal : (a : ℝ) ≤ (A : ℝ) :=
      (le_of_lt (Finset.mem_filter.mp ha).2).trans hLA
    exact Finset.mem_Icc.mpr ⟨ha0, by exact_mod_cast haReal⟩
  have hrcap : r ⊆ Finset.Icc 1 B := by
    intro b hb
    have hb0 : 0 < b := Nat.pos_of_ne_zero (hr b hb).1
    exact Finset.mem_Icc.mpr ⟨hb0, hB b hb⟩
  have hqsub : Q' ⊆ Q := by
    change (smallRoughPairs t r).image (fun x => x.1 * x.2) ⊆
      (smallRoughPairs s r).image (fun x => x.1 * x.2)
    apply Finset.image_mono
    change t.product r ⊆ s.product r
    exact Finset.product_mono (Finset.filter_subset _ _) (Finset.Subset.rfl)
  have hzero : ∀ q ∈ Q, q ∉ Q' → F q = 0 := by
    intro q hq hnot
    have hrho : rho q = 0 := by
      by_contra hnz
      have hactive : q ∈ activeRawPhysicalModuli retainOdd N cap w z L :=
        Finset.mem_filter.mpr ⟨hq, hnz⟩
      exact hnot (active_raw_physical_moduli_subset
        retainOdd N cap w z L hactive)
    simp [F, hrho]
  have hdrop : (∑ q ∈ Q, F q) = ∑ q ∈ Q', F q :=
    (Finset.sum_subset hqsub hzero).symm
  have hAsum :
      (∑ a ∈ Finset.Icc 1 A, (Nat.totient a : ℝ)⁻¹) ≤
        logTotientCap A := sum_reciprocal_totient_le_log A
  have hBsum :
      (∑ b ∈ Finset.Icc 1 B, (Nat.totient b : ℝ)⁻¹) ≤
        logTotientCap B := sum_reciprocal_totient_le_log B
  change (∑ q ∈ Q, F q) ≤ _
  rw [hdrop, sum_smallRoughModuli hs hr F]
  calc
    (∑ x ∈ smallRoughPairs t r, F (x.1 * x.2)) ≤
      ∑ x ∈ smallRoughPairs t r,
        (Nat.totient x.1 : ℝ)⁻¹ *
          (Nat.totient x.2 : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hx
      have hpos : 0 < x.1 ∧ 0 < x.2 :=
        ⟨Nat.pos_of_ne_zero (hs x.1 ha).1,
          Nat.pos_of_ne_zero (hr x.2 hb).1⟩
      have hcoeff : |rho (x.1 * x.2)| ≤ 1 :=
        actualSmallRoughRho_abs_le_one retainOdd N cap w z L _
      calc
        F (x.1 * x.2) ≤
          (Nat.totient (x.1 * x.2) : ℝ)⁻¹ := by
            simpa only [F, one_mul] using
              mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ ≤ (Nat.totient x.1 : ℝ)⁻¹ *
            (Nat.totient x.2 : ℝ)⁻¹ :=
          reciprocal_totient_product_le x.1 x.2 hpos.1 hpos.2
    _ ≤ ∑ x ∈ (Finset.Icc 1 A).product (Finset.Icc 1 B),
          (Nat.totient x.1 : ℝ)⁻¹ *
            (Nat.totient x.2 : ℝ)⁻¹ := by
      change (∑ x ∈ t.product r,
        (Nat.totient x.1 : ℝ)⁻¹ *
          (Nat.totient x.2 : ℝ)⁻¹) ≤ _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.product_mono htcap hrcap)
        (fun x hx hnot => by positivity)
    _ = (∑ a ∈ Finset.Icc 1 A, (Nat.totient a : ℝ)⁻¹) *
        (∑ b ∈ Finset.Icc 1 B, (Nat.totient b : ℝ)⁻¹) := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ logTotientCap A *
        (∑ b ∈ Finset.Icc 1 B, (Nat.totient b : ℝ)⁻¹) := by
      exact mul_le_mul_of_nonneg_right hAsum
        (Finset.sum_nonneg (fun b hb => by positivity))
    _ ≤ logTotientCap A * logTotientCap B := by
      exact mul_le_mul_of_nonneg_left hBsum (logTotientCap_nonneg A)

end
end ImbalancedChen.P3ActualRawActiveLevelTotientCap
