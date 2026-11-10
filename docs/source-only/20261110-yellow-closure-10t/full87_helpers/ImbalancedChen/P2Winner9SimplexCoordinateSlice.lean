import ImbalancedChen.P2Winner9NestedEightSimplexMoment
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is the geometric first Fubini slice of the actual canonical simplex,
at every finite dimension. It proves the exact `Fin.cons` membership/set
identity and the corresponding monomial factorization, then establishes
closedness, compactness and polynomial integrability. No final integral
slice equality is assumed. Mathlib already supplies the volume-preserving
`piFinSuccAbove` identification of `Fin (n+1) → ℝ` with
`ℝ × (Fin n → ℝ)`. The remaining step is its set-integral transport
followed by indicator/Fubini slicing of the dependent slanted set.
No compiler, kernel, producer, checker or numerical replay ran.
-/

namespace ImbalancedChen.P2Winner9SimplexCoordinateSlice

noncomputable section

open Set MeasureTheory

def standardSimplex (n : Nat) (s : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i : Fin n, x i) ≤ s}

/-- A coordinate first slice is exactly the smaller simplex at
the remaining mass. This equality retains the true slanted endpoint. -/
theorem cons_mem_iff {n : Nat} (s t : ℝ) (y : Fin n → ℝ) :
    Fin.cons t y ∈ standardSimplex (n + 1) s ↔
      t ∈ Icc (0 : ℝ) s ∧ y ∈ standardSimplex n (s - t) := by
  constructor
  · rintro ⟨hcoord, hsum⟩
    have ht : 0 ≤ t := by simpa using hcoord 0
    have hy : ∀ i : Fin n, 0 ≤ y i := by
      intro i
      simpa using hcoord i.succ
    have hys : 0 ≤ ∑ i : Fin n, y i := Finset.sum_nonneg (fun i _ => hy i)
    have hs : t + ∑ i : Fin n, y i ≤ s := by
      simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using hsum
    exact ⟨⟨ht, by linarith⟩, ⟨hy, by linarith⟩⟩
  · rintro ⟨⟨ht, _⟩, ⟨hy, hys⟩⟩
    have hc : ∀ i : Fin (n + 1), 0 ≤ Fin.cons t y i := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simpa using ht
      · intro j
        simpa using hy j
    have hs : t + ∑ i : Fin n, y i ≤ s := by linarith
    exact ⟨hc, by
      simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using hs⟩

/-- Explicit preimage equality under the coordinate split; this is the
set equality needed before any product-measure theorem is applied. -/
theorem split_preimage {n : Nat} (s : ℝ) :
    {p : ℝ × (Fin n → ℝ) |
      Fin.cons p.1 p.2 ∈ standardSimplex (n + 1) s} =
    {p : ℝ × (Fin n → ℝ) |
      p.1 ∈ Icc (0 : ℝ) s ∧
        p.2 ∈ standardSimplex n (s - p.1)} := by
  ext p
  exact cons_mem_iff s p.1 p.2

/-- Mathlib's exact measurable coordinate equivalence, with the first
coordinate split off. Its measure preservation is a proved library input. -/
def splitEquiv (n : Nat) :
    (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) 0).symm

theorem splitEquiv_volume (n : Nat) :
    MeasurePreserving (splitEquiv n) := by
  exact (volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) 0).symm _

theorem splitEquiv_apply (n : Nat) (p : ℝ × (Fin n → ℝ)) :
    splitEquiv n p = Fin.cons p.1 p.2 := by
  ext i
  simp [splitEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero]

/-- The exact preimage set under the proved volume-preserving map. -/
theorem splitEquiv_preimage (n : Nat) (s : ℝ) :
    (splitEquiv n) ⁻¹' standardSimplex (n + 1) s =
      {p : ℝ × (Fin n → ℝ) |
        p.1 ∈ Icc (0 : ℝ) s ∧
          p.2 ∈ standardSimplex n (s - p.1)} := by
  ext p
  simpa [splitEquiv_apply] using cons_mem_iff s p.1 p.2

def monomial {n : Nat} (m0 : Nat) (ms : Fin n → Nat)
    (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  (s - ∑ i : Fin n, x i)^m0 *
    (∏ i : Fin n, (x i)^(ms i))

/-- The same slice factors the actual polynomial integrand. -/
theorem monomial_cons {n : Nat} (m0 : Nat)
    (ms : Fin (n + 1) → Nat) (s t : ℝ) (y : Fin n → ℝ) :
    monomial m0 ms s (Fin.cons t y) =
      t^(ms 0) * monomial m0 (fun i => ms i.succ) (s - t) y := by
  simp [monomial, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

theorem continuous_monomial {n : Nat} (m0 : Nat)
    (ms : Fin n → Nat) (s : ℝ) :
    Continuous (monomial m0 ms s) := by
  unfold monomial
  fun_prop

/-- The true closed simplex is a closed set of the finite product. -/
theorem isClosed_standardSimplex {n : Nat} (s : ℝ) :
    IsClosed (standardSimplex n s) := by
  have hc (i : Fin n) : IsClosed {x : Fin n → ℝ | 0 ≤ x i} :=
    isClosed_le continuous_const (continuous_apply i)
  have hcoords : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    convert isClosed_iInter hc using 1
    ext x
    simp
  have hsum : Continuous (fun x : Fin n → ℝ => ∑ i : Fin n, x i) := by
    fun_prop
  have hbound : IsClosed {x : Fin n → ℝ | (∑ i : Fin n, x i) ≤ s} :=
    isClosed_le hsum continuous_const
  simpa [standardSimplex] using hcoords.inter hbound

/-- The coordinate sum bounds each nonnegative coordinate by s. -/
theorem simplex_subset_box {n : Nat} {s : ℝ} (hs : 0 ≤ s) :
    standardSimplex n s ⊆
      {x : Fin n → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) s} := by
  intro x hx i
  have hnonneg := hx.1
  have hi : x i ≤ ∑ j : Fin n, x j := by
    classical
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  exact ⟨hnonneg i, le_trans hi hx.2⟩

theorem isCompact_standardSimplex {n : Nat} {s : ℝ} (hs : 0 ≤ s) :
    IsCompact (standardSimplex n s) := by
  have hbox : IsCompact
      {x : Fin n → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) s} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  exact hbox.of_isClosed_subset (isClosed_standardSimplex s)
    (simplex_subset_box hs)

theorem integrableOn_monomial {n : Nat} {s : ℝ} (hs : 0 ≤ s)
    (m0 : Nat) (ms : Fin n → Nat) :
    IntegrableOn (monomial m0 ms s) (standardSimplex n s) := by
  exact (continuous_monomial m0 ms s).continuousOn.integrableOn_compact
    (isCompact_standardSimplex hs)

/-- Identifies the generic eight-coordinate set with the Phase15 target. -/
theorem standardSimplex_eight (s : ℝ) :
    standardSimplex 8 s =
      ImbalancedChen.P2Winner9NestedEightSimplexMoment.standardSimplex s := rfl

end

end ImbalancedChen.P2Winner9SimplexCoordinateSlice
