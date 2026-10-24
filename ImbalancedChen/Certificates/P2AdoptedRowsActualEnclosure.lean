import ImbalancedChen.Certificates.PairedV2FullCertificate

/-!
SOURCE ONLY; not compiled or installed.

The existing `FullMask.integral_bounds` already encloses the sum of all
17572 actual local integrals, using the proved `all_certificates_checked`.
This module supplies the missing binding to actual grid pairs: the grid
image has exactly 17572 elements, has the original strip membership
predicate, has the same geometric union, and its sum of literal local
integrals has the certified endpoints. No stored endpoint is used to
define an integral. No target endpoint inequality is a hypothesis.

This does not identify a product-volume set integral over `region` with
the iterated integrals: that separate Fubini/endpoint-null-set theorem is
not supplied by the imported modules or asserted here.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2AdoptedRows

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-- The adopted cells indexed by their actual grid coordinates. -/
def grid : Finset (ℕ × ℕ) := Finset.univ.image indices

/-- The original cutoff, now a function of actual grid coordinates. -/
def gridCutoff (p : ℕ × ℕ) : ℚ :=
  min (uLower p.2) (3 * (1 - tUpper p.1 - uUpper p.2) / 13)

def gridSupport (p : ℕ × ℕ) : Set (Fin 4 → ℝ) :=
  openFibreSet p.1 p.2 (gridCutoff p)

/-- A genuine integral with no certificate output among its arguments. -/
def gridIntegral (p : ℕ × ℕ) : ℝ :=
  pairedLocalIntegral (K : ℝ) a (tLower p.1) (tUpper p.1)
    (uLower p.2) (uUpper p.2) (gridCutoff p)

theorem gridCutoff_indices (r : Row) : gridCutoff (indices r) = cutoff r := by
  rfl

theorem gridSupport_indices (r : Row) : gridSupport (indices r) = support r := by
  rfl

theorem grid_card : grid.card = 17572 := by
  rw [grid, Finset.card_image_of_injective _ indices_injective]
  simpa only [Finset.card_univ] using row_count

/-- Membership refers to the actual mesh, rather than to an ordinal range. -/
theorem mem_grid (p : ℕ × ℕ) :
    p ∈ grid ↔ ∃ k : Fin 186,
      p.1 = 326 + k.val ∧ firstU k ≤ p.2 ∧ p.2 < 512 := by
  rcases p with ⟨i, j⟩
  simpa only [grid, Finset.mem_image, Finset.mem_univ, true_and] using
    indices_cover i j

/-- Reindexing does not change the actual geometric region. -/
theorem region_eq_grid_union : region = ⋃ p ∈ grid, gridSupport p := by
  ext x
  simp only [region, Set.mem_iUnion, grid, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨indices r, ⟨r, rfl⟩, hr⟩
  · rintro ⟨p, ⟨r, rfl⟩, hr⟩
    exact ⟨r, hr⟩

/-- The reindexing identity works for every real observable on actual cells. -/
theorem sum_grid (f : ℕ × ℕ → ℝ) :
    (∑ p ∈ grid, f p) = ∑ r : Row, f (indices r) := by
  exact Finset.sum_image (fun _ _ _ _ he => indices_injective he)

/-- No adopted cell is dropped or counted twice in the integral sum. -/
theorem sum_gridIntegral : (∑ p ∈ grid, gridIntegral p) = integral := by
  rw [sum_grid]
  rfl

/-- Literal kernel semantics after reindexing by actual mesh coordinates. -/
theorem gridIntegral_literal (p : ℕ × ℕ) :
    gridIntegral p = ((K : ℝ) / 80) *
      ∫ t in (tLower p.1 : ℝ)..(tUpper p.1 : ℝ),
      ∫ u in (uLower p.2 : ℝ)..(uUpper p.2 : ℝ),
      ∫ z in (a : ℝ)..(gridCutoff p : ℝ), ∫ w in (a : ℝ)..z,
        1 / (t * u * z ^ 2 * w) := by
  exact pairedLocalIntegral_eq_literal _ _ _ _ _ _ _

/-- Bind the existing all-row check supplier to each actual row integral. -/
theorem row_actual_enclosure (r : Row) :
    ((makeCertificate r (approximation r)).lower : ℝ) ≤
        gridIntegral (indices r) ∧
      gridIntegral (indices r) ≤
        ((makeCertificate r (approximation r)).upper : ℝ) := by
  simpa only [makeCertificate, gridIntegral, gridCutoff, cutoff] using
    (makeCertificate r (approximation r)).check_sound (all_certificates_checked r)

/-- Any selected part of the adopted mask inherits the proved actual checks.
This permits exact finite subdivisions without rerunning the row checker. -/
theorem partial_actual_enclosure (s : Finset Row) :
    ((∑ r ∈ s, (makeCertificate r (approximation r)).lower : ℚ) : ℝ) ≤
        (∑ r ∈ s, gridIntegral (indices r)) ∧
      (∑ r ∈ s, gridIntegral (indices r)) ≤
        ((∑ r ∈ s, (makeCertificate r (approximation r)).upper : ℚ) : ℝ) := by
  simpa only [makeCertificate, gridIntegral, gridCutoff, cutoff] using
    PairedIntegralCertificate.sum_check_sound s
      (fun r => makeCertificate r (approximation r))
      (fun r _ => all_certificates_checked r)

/-- The complete actual grid sum, with the original K/80 normalization. -/
theorem grid_actual_enclosure :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤
        (∑ p ∈ grid, gridIntegral p) ∧
      (∑ p ∈ grid, gridIntegral p) ≤
        (55858409959907296 / 100000000000000000000 : ℝ) := by
  rw [sum_gridIntegral]
  exact integral_bounds

/-- The same enclosure written entirely with literal iterated integrals. -/
theorem literal_grid_actual_enclosure :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤
        ((K : ℝ) / 80) * (∑ p ∈ grid,
          ∫ t in (tLower p.1 : ℝ)..(tUpper p.1 : ℝ),
          ∫ u in (uLower p.2 : ℝ)..(uUpper p.2 : ℝ),
          ∫ z in (a : ℝ)..(gridCutoff p : ℝ), ∫ w in (a : ℝ)..z,
            1 / (t * u * z ^ 2 * w)) ∧
      ((K : ℝ) / 80) * (∑ p ∈ grid,
          ∫ t in (tLower p.1 : ℝ)..(tUpper p.1 : ℝ),
          ∫ u in (uLower p.2 : ℝ)..(uUpper p.2 : ℝ),
          ∫ z in (a : ℝ)..(gridCutoff p : ℝ), ∫ w in (a : ℝ)..z,
            1 / (t * u * z ^ 2 * w)) ≤
        (55858409959907296 / 100000000000000000000 : ℝ) := by
  simpa only [gridIntegral_literal, Finset.mul_sum] using grid_actual_enclosure

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2AdoptedRows
