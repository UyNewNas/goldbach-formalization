import ImbalancedChen.P5U7SpatialRoughRowReconstruction
import ImbalancedChen.P5U7TerminalPrimeMixedWindow

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Actual spatial product-CDF families at cutoff M with original target N.
The original N-labelled source is filtered by product<M; it is identified
with the mixed target-N prime window and ordered-semiprime window. Exact
signed-test Fubini and rough-row CDF reconstruction precede any spatial
asymptotic. No target exclusion or factor threshold is changed to M.
-/
namespace ImbalancedChen
noncomputable section
open scoped BigOperators
open Classical

def p5U7SpatialThree (N M : ℕ) : Finset P5U7ThreeLabel :=
  (p5U7ArithmeticThree N).filter (fun x => p5U7ThreeProduct x<M)

def p5U7SpatialFour (N M : ℕ) : Finset P5U7FourLabel :=
  (p5U7ArithmeticFour N).filter (fun x => p5U7FourProduct x<M)

/-- The outer marked pair and prime-divisor exclusion are still indexed
by N, while M controls only the physical product cutoff. -/
theorem p5U7SpatialThree_eq_mixed_windows {N M : ℕ} (hMN : M ≤ N) :
    p5U7SpatialThree N M =
      (chenY7PrimeSelector N ((N : ℝ)^(59/250 : ℝ))).sigma
        (fun t => p5U7MassPrimeWindow N M (t.1*t.2) t.2) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx,hM⟩ := Finset.mem_filter.mp hx
    obtain ⟨ht,hq⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hc,hw,_⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_sigma.mpr ⟨ht,Finset.mem_filter.mpr ⟨hc,hw,hM⟩⟩
  · intro hx
    obtain ⟨ht,hq⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hc,hw,hM⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
      ⟨ht,Finset.mem_filter.mpr ⟨hc,hw,hM.trans_le hMN⟩⟩,hM⟩

theorem p5U7SpatialFour_eq_mixed_windows {N M : ℕ} (hMN : M ≤ N) :
    p5U7SpatialFour N M =
      (chenY7PrimeSelector N ((N : ℝ)^(59/250 : ℝ))).sigma (p5U7MassSemiprimeWindow N M) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx,hM⟩ := Finset.mem_filter.mp hx
    obtain ⟨ht,hu⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hc,hw,ho,_⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_sigma.mpr ⟨ht,Finset.mem_filter.mpr ⟨hc,hw,ho,hM⟩⟩
  · intro hx
    obtain ⟨ht,hu⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hc,hw,ho,hM⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
      ⟨ht,Finset.mem_filter.mpr ⟨hc,hw,ho,hM.trans_le hMN⟩⟩,hM⟩

private theorem p5U7Spatial_filter_fibre {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) {M m : ℕ} (hm : m<M) :
    (S.filter (fun x => f x<M)).filter (fun x => f x=m) = S.filter (fun x => f x=m) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hx,_⟩,heq⟩
    exact ⟨hx,heq⟩
  · rintro ⟨hx,heq⟩
    exact ⟨⟨hx,by simpa only [heq] using hm⟩,heq⟩

/-- Exact CDF-restricted signed physical-test Fubini. The range endpoint
M is strict and every marked product-fibre multiplicity is preserved. -/
theorem p5U7SpatialPrimeProductWeight_Fubini (N M : ℕ) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.range M,p5U7ActualPrimeProductWeight N m*H m) =
      ∑ x ∈ p5U7SpatialThree N M,H (p5U7ThreeProduct x) := by
  have hmap : ∀ x ∈ p5U7SpatialThree N M,p5U7ThreeProduct x ∈ Finset.range M :=
    fun x hx => Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
  calc
    _ = ∑ m ∈ Finset.range M,
        ((((p5U7SpatialThree N M).filter (fun x => p5U7ThreeProduct x=m)).card : ℝ)*H m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [p5U7SpatialThree,p5U7Spatial_filter_fibre _ _ (Finset.mem_range.mp hm)]
      rfl
    _ = _ := by
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_fiberwise_of_maps_to' hmap H

theorem p5U7SpatialSemiprimeProductWeight_Fubini (N M : ℕ) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.range M,p5U7ActualSemiprimeProductWeight N m*H m) =
      ∑ x ∈ p5U7SpatialFour N M,H (p5U7FourProduct x) := by
  have hmap : ∀ x ∈ p5U7SpatialFour N M,p5U7FourProduct x ∈ Finset.range M :=
    fun x hx => Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
  calc
    _ = ∑ m ∈ Finset.range M,
        ((((p5U7SpatialFour N M).filter (fun x => p5U7FourProduct x=m)).card : ℝ)*H m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [p5U7SpatialFour,p5U7Spatial_filter_fibre _ _ (Finset.mem_range.mp hm)]
      rfl
    _ = _ := by
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_fiberwise_of_maps_to' hmap H

theorem p5U7SpatialPrimeProductWeight_mass (N M : ℕ) :
    (∑ m ∈ Finset.range M,p5U7ActualPrimeProductWeight N m) =
      ((p5U7SpatialThree N M).card : ℝ) := by
  simpa only [mul_one,Finset.sum_const,nsmul_eq_mul] using
    p5U7SpatialPrimeProductWeight_Fubini N M (fun _ => 1)

theorem p5U7SpatialSemiprimeProductWeight_mass (N M : ℕ) :
    (∑ m ∈ Finset.range M,p5U7ActualSemiprimeProductWeight N m) =
      ((p5U7SpatialFour N M).card : ℝ) := by
  simpa only [mul_one,Finset.sum_const,nsmul_eq_mul] using
    p5U7SpatialSemiprimeProductWeight_Fubini N M (fun _ => 1)

/-- The exact prime CDF is a sum of mixed windows with original target N.
This is a finite arithmetic identification, not an assumed CDF asymptotic. -/
theorem p5U7SpatialPrimeCDF_eq_window_sum {N M : ℕ} (hMN : M ≤ N) :
    (∑ m ∈ Finset.range M,p5U7ActualPrimeProductWeight N m) =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ)^(59/250 : ℝ)),
        ((p5U7MassPrimeWindow N M (t.1*t.2) t.2).card : ℝ) := by
  rw [p5U7SpatialPrimeProductWeight_mass,p5U7SpatialThree_eq_mixed_windows hMN]
  simp only [Finset.card_sigma,Nat.cast_sum]

theorem p5U7SpatialSemiprimeCDF_eq_window_sum {N M : ℕ} (hMN : M ≤ N) :
    (∑ m ∈ Finset.range M,p5U7ActualSemiprimeProductWeight N m) =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ)^(59/250 : ℝ)),
        ((p5U7MassSemiprimeWindow N M t).card : ℝ) := by
  rw [p5U7SpatialSemiprimeProductWeight_mass,p5U7SpatialFour_eq_mixed_windows hMN]
  simp only [Finset.card_sigma,Nat.cast_sum]

/-- The full physical CDF equals the actual good rough-row count at M/a,
with original N target exclusion and no terminal multiplicity loss. -/
theorem p5U7SpatialFullCDF_eq_goodRough_sum {N M : ℕ} (hMN : M ≤ N) :
    (∑ m ∈ Finset.range M,p5U7ArithmeticProductWeight N m) =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ)^(59/250 : ℝ)),
        ((p5U7SpatialGoodRough N M t).card : ℝ) := by
  simp only [p5U7ArithmeticProductWeight_eq_components,Finset.sum_add_distrib]
  rw [p5U7SpatialPrimeCDF_eq_window_sum hMN,p5U7SpatialSemiprimeCDF_eq_window_sum hMN,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have h := p5U7SpatialGoodRough_card_eq_components hMN ht
  change ((p5U7MassPrimeWindow N M (t.1*t.2) t.2).card : ℝ) +
    ((p5U7MassSemiprimeWindow N M t).card : ℝ) = _
  exact_mod_cast h.symm

end
end ImbalancedChen
