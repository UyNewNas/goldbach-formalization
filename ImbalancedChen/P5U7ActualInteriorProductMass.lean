import ImbalancedChen.P5U7ActualInteriorAsymptotic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The actual strict-interior U7 product weight, with every marked fibre
multiplicity, has the proved K=1 Buchstab mean. Both source families and
the ordered repeated-prime semiprime labels are literal restrictions of
the original arithmetic source. No product injectivity is asserted.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

def p5U7ActualInteriorThree (N : ℕ) (eta : ℝ) : Finset P5U7ThreeLabel :=
  (p5U7InteriorSelector N eta).sigma fun t => p5U7MassPrimeFibre N (t.1 * t.2) t.2

def p5U7ActualInteriorFour (N : ℕ) (eta : ℝ) : Finset P5U7FourLabel :=
  (p5U7InteriorSelector N eta).sigma fun t => p5U7MassSemiprimePairs N t

theorem p5U7ActualInteriorThree_eq_original_filter (N : ℕ) (eta : ℝ) :
    p5U7ActualInteriorThree N eta =
      (p5U7ArithmeticThree N).filter (fun x => x.1 ∈ p5U7InteriorSelector N eta) := by
  ext x
  constructor
  · intro hx
    obtain ⟨ht, hq⟩ := Finset.mem_sigma.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨(Finset.mem_filter.mp ht).1, hq⟩, ht⟩
  · intro hx
    obtain ⟨hx, ht⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_sigma.mpr ⟨ht, (Finset.mem_sigma.mp hx).2⟩

theorem p5U7ActualInteriorFour_eq_original_filter (N : ℕ) (eta : ℝ) :
    p5U7ActualInteriorFour N eta =
      (p5U7ArithmeticFour N).filter (fun x => x.1 ∈ p5U7InteriorSelector N eta) := by
  ext x
  constructor
  · intro hx
    obtain ⟨ht, hq⟩ := Finset.mem_sigma.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨(Finset.mem_filter.mp ht).1, hq⟩, ht⟩
  · intro hx
    obtain ⟨hx, ht⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_sigma.mpr ⟨ht, (Finset.mem_sigma.mp hx).2⟩

theorem p5U7ActualInterior_label_mass_eq_rows (N : ℕ) (eta : ℝ) :
    ((p5U7ActualInteriorThree N eta).card : ℝ) + ((p5U7ActualInteriorFour N eta).card : ℝ) =
      p5U7ActualInteriorSourceMass N eta := by
  simp only [p5U7ActualInteriorThree, p5U7ActualInteriorFour, Finset.card_sigma, Nat.cast_sum,
    p5U7ActualInteriorSourceMass, p5U7OriginalRowMass, Finset.sum_add_distrib]

def p5U7ActualInteriorProductWeight (N : ℕ) (eta : ℝ) (m : ℕ) : ℝ :=
  (((p5U7ActualInteriorThree N eta).filter (fun x => p5U7ThreeProduct x = m)).card : ℝ) +
    (((p5U7ActualInteriorFour N eta).filter (fun x => p5U7FourProduct x = m)).card : ℝ)

theorem p5U7ActualInteriorProductWeight_nonneg (N : ℕ) (eta : ℝ) (m : ℕ) :
    0 ≤ p5U7ActualInteriorProductWeight N eta m := by unfold p5U7ActualInteriorProductWeight; positivity

private theorem p5U7ActualInterior_fibre_sum {α : Type*} [DecidableEq α]
    (N : ℕ) (S : Finset α) (f : α → ℕ) (hN : ∀ x ∈ S, f x < N) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.range N, (((S.filter (fun x => f x = m)).card : ℝ) * H m)) =
      ∑ x ∈ S, H (f x) := by
  have hmap : ∀ x ∈ S, f x ∈ Finset.range N := fun x hx => Finset.mem_range.mpr (hN x hx)
  simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_fiberwise_of_maps_to' hmap H

/-- Exact signed product-test Fubini. Multiplicity survives product
collisions and repeated terminal prime factors without any correction. -/
theorem p5U7ActualInterior_product_weighted_Fubini (N : ℕ) (eta : ℝ) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.range N, p5U7ActualInteriorProductWeight N eta m * H m) =
      (∑ x ∈ p5U7ActualInteriorThree N eta, H (p5U7ThreeProduct x)) +
        ∑ x ∈ p5U7ActualInteriorFour N eta, H (p5U7FourProduct x) := by
  simp only [p5U7ActualInteriorProductWeight, add_mul, Finset.sum_add_distrib]
  rw [p5U7ActualInterior_fibre_sum N _ _ ?_ H, p5U7ActualInterior_fibre_sum N _ _ ?_ H]
  · intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2.2
  · intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2.2.2

theorem p5U7ActualInterior_product_weight_mass (N : ℕ) (eta : ℝ) :
    (∑ m ∈ Finset.range N, p5U7ActualInteriorProductWeight N eta m) = p5U7ActualInteriorSourceMass N eta := by
  have hh := p5U7ActualInterior_product_weighted_Fubini N eta (fun _ => 1)
  simpa only [mul_one, Finset.sum_const, nsmul_eq_mul, p5U7ActualInterior_label_mass_eq_rows] using hh

/-- ACTUAL original strict-interior marked arithmetic product mass,
normalized by N/log N, tends to its genuine Buchstab integral. The proof
uses source reconstruction, paid target-divisor/unit/endpoint losses,
native band3 error and the already proved double-prime PNT main. -/
theorem tendsto_p5U7ActualInteriorProductWeight_mass (eta : ℝ) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) *
      (∑ m ∈ Finset.range N, p5U7ActualInteriorProductWeight N eta m)) atTop
        (𝓝 (p5U7InteriorOmegaIntegral eta)) := by
  simpa only [p5U7ActualInterior_product_weight_mass] using
    tendsto_p5U7ActualInteriorSourceMass_normalized eta heta

end

end ImbalancedChen
