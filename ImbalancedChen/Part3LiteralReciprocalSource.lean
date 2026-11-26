import ImbalancedChen.Part3ActualReciprocalSquarePoissonCore
import ImbalancedChen.Part3OriginalCommonPoissonKernelLanesCore
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Integration adapter for the already accepted P3.4 source at 97d5de82.
Existing declaration owners are reused; retained theorem statements and proof bodies
are unchanged. Exact transformations are recorded in
`docs/part3-distribution/p31-actual-source-lanes-20261126/SUPPLIER_ADAPTERS.json`. -/


/-! # The signed finite reciprocal source and its grouped coefficient -/

namespace ImbalancedChen.Part3

noncomputable section
open Finset

def CommonSmoothCutoff.poissonNonzeroFrequencyWindow (H : ℕ) : Finset ℤ :=
  ((Finset.Icc 1 H).image (fun n : ℕ => (n : ℤ))) ∪
    ((Finset.Icc 1 H).image (fun n : ℕ => -(n : ℤ)))

end
end ImbalancedChen.Part3

namespace ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly

noncomputable section
open Classical Finset CommonSmoothCutoff
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- An exact finite t carrier, needed for the actual quotient image. No
claim that that image equals a full dyadic factorCarrier is required. -/
def finiteInnerCarrier (T : Finset ℕ) (H : ℕ) : Finset Inner := T ×ˢ poissonNonzeroFrequencyWindow H

/-- The actual a-unit level licence follows from both retained t gates.
This is the CoprimePacket gate required after y,z grouping, including |a|=0. -/
theorem output_level_residue_coprime (A : ℕ) (a : ℤ) {u v : Inner}
    (hu : fixedUnit A a u.1) (hv : fixedUnit A a v.1) :
    a.natAbs.Coprime (level u v) := (hu.2.mul_left hv.2).symm

/-- Positive level comes from actual t>0; no fictitious positive level0. -/
theorem output_level_pos {u v : Inner} (hu : 0 < u.1) (hv : 0 < v.1) : 0 < level u v :=
  Nat.mul_pos hu hv

end
end ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly

namespace ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly

noncomputable section
open Classical Finset ActualReciprocalSquarePoissonSourceOnly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Source := ℤ × (Inner × Inner)

def rawCarrier (T : Finset ℕ) (H : ℕ) (F : Finset ℤ) : Finset Source :=
  F ×ˢ (finiteInnerCarrier T H ×ˢ finiteInnerCarrier T H)

def carrier (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : Finset ℤ) : Finset Source :=
  (rawCarrier T H F).filter (fun s => s.1 ≠ 0 ∧ fixedUnit A a s.2.1.1 ∧ fixedUnit A a s.2.2.1)

def output (s : Source) : Output := (level s.2.1 s.2.2, outputY s.1 s.2.1 s.2.2)

def weight (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (s : Source) : ℂ :=
  atomCoeff lambda omega s.2.1 * star (atomCoeff lambda omega s.2.2)

def nonzeroSource (U : Finset Source) : Finset Source := U.filter (fun s => (output s).2 ≠ 0)

def fiber (U : Finset Source) (zy : Output) : Finset Source := U.filter (fun s => output s = zy)

def beta (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (zy : Output) : ℂ :=
  ∑ s ∈ fiber U zy, weight lambda omega s

/-- Exact joint coefficient pushforward. Captured fixed lambda/omega do
not acquire a b,c or future Poisson m argument. -/
theorem weighted_pushforward (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (K : Output → ℂ) :
    (∑ s ∈ U, weight lambda omega s * K (output s)) =
      ∑ zy ∈ U.image output, beta U lambda omega zy * K zy := by
  have hf := sum_fiberwise_of_maps_to (s := U) (t := U.image output) (g := output)
    (fun s hs => mem_image_of_mem _ hs) (fun s => weight lambda omega s * K (output s))
  rw [← hf]
  apply sum_congr rfl
  intro zy hzy
  unfold beta
  rw [sum_mul]
  apply sum_congr rfl
  intro s hs
  rw [(mem_filter.mp hs).2]

/-- A grouped coefficient has no hidden support: a nonzero beta supplies
an original source witness. -/
theorem beta_ne_zero_mem_image {U : Finset Source} {lambda : ℕ → ℂ} {omega : ℤ → ℂ}
    {zy : Output} (hb : beta U lambda omega zy ≠ 0) : zy ∈ U.image output := by
  by_contra hn
  apply hb
  apply sum_eq_zero
  intro s hs
  exact False.elim (hn (mem_image.mpr ⟨s,(mem_filter.mp hs).1,(mem_filter.mp hs).2⟩))

theorem carrier_data {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {F : Finset ℤ}
    {s : Source} (hs : s ∈ carrier A a T H F) :
    s.1 ∈ F ∧ s.2.1 ∈ finiteInnerCarrier T H ∧ s.2.2 ∈ finiteInnerCarrier T H ∧
      s.1 ≠ 0 ∧ fixedUnit A a s.2.1.1 ∧ fixedUnit A a s.2.2.1 := by
  obtain ⟨hr,hg⟩ := mem_filter.mp hs
  exact ⟨(mem_product.mp hr).1,(mem_product.mp (mem_product.mp hr).2).1,
    (mem_product.mp (mem_product.mp hr).2).2,hg⟩

theorem output_residue_coprime {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {F : Finset ℤ}
    {s : Source} (hs : s ∈ carrier A a T H F) : a.natAbs.Coprime (output s).1 := by
  have hd := carrier_data hs
  exact output_level_residue_coprime A a hd.2.2.2.2.1 hd.2.2.2.2.2

theorem output_positive_level {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {F : Finset ℤ}
    (hT : ∀ t ∈ T, 0 < t) {s : Source} (hs : s ∈ carrier A a T H F) : 0 < (output s).1 := by
  have hd := carrier_data hs
  exact output_level_pos (hT _ (mem_product.mp hd.2.1).1) (hT _ (mem_product.mp hd.2.2.1).1)

end
end ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
