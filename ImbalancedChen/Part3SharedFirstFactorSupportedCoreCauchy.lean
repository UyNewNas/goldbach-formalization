import ImbalancedChen.Part3SharedFirstFactorSmallCoreSquaredFinite

/-!
# Cauchy on the literal nonzero outer coefficient support

The outer carrier is filtered by the original complex coefficient being
nonzero. Both the coefficient energy and the positive sum of complete row
squares retain that same support. In particular the paired-gcd and
supported-part gates remain available after Cauchy.

All inner labels, signed frequencies, real projections, divisor masks and
CRT conditions are those of SmallCoreSquaredFinite. Only the total row
square is used: no positivity or comparison of its signed nonresonant
part is asserted. This is a finite entry point, not a spectral estimate.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

/-- Literal support of the existing outer coefficient; no gate is replaced. -/
def MediumAtom.smallCoreSquaredSupportedOuterCarrier (d : MediumAtom)
    (Ybeta Ysupport : ℝ) :
    Finset ((ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) :=
  d.smallCoreSquaredOuterCarrier.filter
    (fun o => d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o ≠ 0)

/-- The actual complex coefficient energy, on its literal nonzero support. -/
def MediumAtom.smallCoreSquaredSupportedFirstEnergy (d : MediumAtom)
    (Ybeta Ysupport : ℝ) : ℝ :=
  ∑ o ∈ d.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport,
    ‖d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o‖ ^ 2

/-- A positive sum of complete original row squares, on the same support. -/
def MediumAtom.smallCoreSquaredSupportedRowSquareMass (d : MediumAtom)
    (Ybeta Ysupport Z : ℝ) : ℝ :=
  ∑ o ∈ d.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport,
    ‖∑ u ∈ d.smallCoreSquaredInnerCarrier Z o,
      d.smallCoreSquaredRowTerm Z o u‖ ^ 2

theorem MediumAtom.mem_smallCoreSquaredSupportedOuterCarrier
    (d : MediumAtom) (Ybeta Ysupport : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) :
    o ∈ d.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport ↔
      o ∈ d.smallCoreSquaredOuterCarrier ∧
        d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o ≠ 0 := by
  exact Finset.mem_filter

/-- These are precisely the two arithmetic gates already present in `Co`. -/
theorem MediumAtom.smallCoreSquaredOuterCoefficient_nonzero_gates
    (d : MediumAtom) (Ybeta Ysupport : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ))
    (hC : d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o ≠ 0) :
    (o.1.2.1.gcd o.1.2.2 : ℝ) ≤ Ybeta ∧
      (CanonicalReciprocalData.supportedPart
        (o.1.2.1 / o.1.2.1.gcd o.1.2.2) (o.1.2.1.gcd o.1.2.2) : ℝ) ≤
        Ysupport := by
  unfold MediumAtom.smallCoreSquaredOuterCoefficient at hC
  dsimp only at hC
  by_contra hgate
  exact hC (if_neg hgate)

theorem MediumAtom.smallCoreSquaredSupportedOuterCarrier_gates
    (d : MediumAtom) (Ybeta Ysupport : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ))
    (ho : o ∈ d.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport) :
    (o.1.2.1.gcd o.1.2.2 : ℝ) ≤ Ybeta ∧
      (CanonicalReciprocalData.supportedPart
        (o.1.2.1 / o.1.2.1.gcd o.1.2.2) (o.1.2.1.gcd o.1.2.2) : ℝ) ≤
        Ysupport := by
  exact d.smallCoreSquaredOuterCoefficient_nonzero_gates Ybeta Ysupport o
    ((d.mem_smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport o).mp ho).2

/-- The small modulus product is controlled on this support without an
additional smallness assumption or a replacement coefficient. -/
theorem MediumAtom.smallCoreSquaredSupportedOuterCarrier_product_le
    (d : MediumAtom) (Ybeta Ysupport : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ))
    (ho : o ∈ d.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport) :
    (o.1.2.1.gcd o.1.2.2 : ℝ) *
      (CanonicalReciprocalData.supportedPart
        (o.1.2.1 / o.1.2.1.gcd o.1.2.2) (o.1.2.1.gcd o.1.2.2) : ℝ) ≤
        Ybeta * Ysupport := by
  obtain ⟨hg, hs⟩ := d.smallCoreSquaredSupportedOuterCarrier_gates Ybeta Ysupport o ho
  exact mul_le_mul_of_nonneg' hg hs (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hg)

/-- Removing zero coefficients is an exact identity, for any original row. -/
theorem MediumAtom.smallCoreSquared_sum_eq_supported
    (d : MediumAtom) (Ybeta Ysupport : ℝ)
    (F : ((ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) → ℂ) :
    (∑ o ∈ d.smallCoreSquaredOuterCarrier,
      d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o * F o) =
      ∑ o ∈ d.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport,
        d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o * F o := by
  unfold MediumAtom.smallCoreSquaredSupportedOuterCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o _
  by_cases hC : d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o = 0 <;> simp [hC]

theorem MediumAtom.smallCoreSquaredSupportedFirstEnergy_nonneg
    (d : MediumAtom) (Ybeta Ysupport : ℝ) :
    0 ≤ d.smallCoreSquaredSupportedFirstEnergy Ybeta Ysupport := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem MediumAtom.smallCoreSquaredSupportedRowSquareMass_nonneg
    (d : MediumAtom) (Ybeta Ysupport Z : ℝ) :
    0 ≤ d.smallCoreSquaredSupportedRowSquareMass Ybeta Ysupport Z := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Exact total Gram expansion. It is the complete row square, with both
signed frequencies and every inner label still present. -/
theorem MediumAtom.smallCoreSquaredSupportedRowSquareMass_eq_totalGram
    (d : MediumAtom) (Ybeta Ysupport Z : ℝ) :
    d.smallCoreSquaredSupportedRowSquareMass Ybeta Ysupport Z =
      ∑ o ∈ d.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport,
        (∑ u ∈ d.smallCoreSquaredInnerCarrier Z o,
          ∑ v ∈ d.smallCoreSquaredInnerCarrier Z o,
            d.smallCoreSquaredRowTerm Z o u *
              star (d.smallCoreSquaredRowTerm Z o v)).re := by
  unfold MediumAtom.smallCoreSquaredSupportedRowSquareMass
  apply Finset.sum_congr rfl
  intro o _
  simpa only [Complex.ofReal_re] using
    congrArg Complex.re (complex_norm_sq_sum_eq_double_star
      (d.smallCoreSquaredInnerCarrier Z o) (d.smallCoreSquaredRowTerm Z o))

/-- Cauchy keeps both energies on `O_C`; the first energy is not replaced by
the cardinality of the unfiltered carrier. -/
theorem MediumAtom.smallCoreSquared_supported_Cauchy
    (d : MediumAtom) (Ybeta Ysupport Z : ℝ) :
    ‖∑ o ∈ d.smallCoreSquaredOuterCarrier,
      d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o *
        (∑ u ∈ d.smallCoreSquaredInnerCarrier Z o,
          d.smallCoreSquaredRowTerm Z o u)‖ ^ 2 ≤
      d.smallCoreSquaredSupportedFirstEnergy Ybeta Ysupport *
        d.smallCoreSquaredSupportedRowSquareMass Ybeta Ysupport Z := by
  rw [d.smallCoreSquared_sum_eq_supported Ybeta Ysupport
    (fun o => ∑ u ∈ d.smallCoreSquaredInnerCarrier Z o,
      d.smallCoreSquaredRowTerm Z o u)]
  exact complex_finset_cauchy_norm_sq
    (d.smallCoreSquaredSupportedOuterCarrier Ybeta Ysupport)
    (d.smallCoreSquaredOuterCoefficient Ybeta Ysupport)
    (fun o => ∑ u ∈ d.smallCoreSquaredInnerCarrier Z o,
      d.smallCoreSquaredRowTerm Z o u)

/-- Consumer for the actual cleaned small core. The only source identity
used is the first component of the existing public finite decomposition. -/
theorem actual_smallSupported_supportedCore_Cauchy
    (B : ℕ) (sigma kappa c0 : ℝ) (hsigma : 0 < sigma)
    (d : MediumAtom) (hd : MediumAdmissible B sigma kappa c0 d) :
    ∀ Z : ℝ, 0 < Z →
      let e := d.cleanedAlphaAtom
      let Y := d.scale ^ (sigma / 4)
      (e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z =
        ∑ o ∈ e.smallCoreSquaredSupportedOuterCarrier Y Y,
          e.smallCoreSquaredOuterCoefficient Y Y o *
            (∑ u ∈ e.smallCoreSquaredInnerCarrier Z o,
              e.smallCoreSquaredRowTerm Z o u)) ∧
      (‖e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z‖ ^ 2 ≤
        e.smallCoreSquaredSupportedFirstEnergy Y Y *
          e.smallCoreSquaredSupportedRowSquareMass Y Y Z) := by
  intro Z hZ
  dsimp only
  let e := d.cleanedAlphaAtom
  let Y := d.scale ^ (sigma / 4)
  have heqFull : e.sharedSmallPairedSmallSupportedNonzeroSmooth Y Y Z =
      ∑ o ∈ e.smallCoreSquaredOuterCarrier,
        e.smallCoreSquaredOuterCoefficient Y Y o *
          (∑ u ∈ e.smallCoreSquaredInnerCarrier Z o,
            e.smallCoreSquaredRowTerm Z o u) :=
    (actual_smallSupported_squared_resonance_Cauchy
      B sigma kappa c0 hsigma d hd Z hZ).1
  refine ⟨heqFull.trans (e.smallCoreSquared_sum_eq_supported Y Y _), ?_⟩
  rw [heqFull]
  exact e.smallCoreSquared_supported_Cauchy Y Y Z

end

end ImbalancedChen.Part3
