import ImbalancedChen.P2Winner9HomogeneousRecurrence
import ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly

/-! Exact evaluation of the original T10 and all 70 signed mixed terms. -/

namespace ImbalancedChen.P2Winner9FastExactAssembly

open scoped BigOperators
open P2Winner9CurvatureFullExactAssembly
open P2Winner9CurvatureExactMomentFloor (gapTotal)
open P2Winner9HomogeneousRecurrence (homogeneousFast homogeneousFast_eq_source)

private theorem homogeneous_eq (y : Fin 9 → ℕ) (k : ℕ) :
    homogeneousFast y k = homogeneous y k :=
  homogeneousFast_eq_source y k

def weightedMomentFast (d : SimplexData) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1),
    homogeneousFast d.y (k - j) * powerMoment d j

private theorem weightedMoment_eq (d : SimplexData) (k : ℕ) :
    weightedMomentFast d k = weightedMoment d k := by
  simp only [weightedMomentFast, weightedMoment, homogeneous_eq]

def zFast (d : SimplexData) (k : ℕ) : ℤ :=
  (weightedMomentFast d k : ℤ) * (H d : ℤ)^k -
    (gapTotal d.gaps : ℤ) * ((9 + k).choose k : ℤ) *
      (meanNumerator d : ℤ)^k

private theorem z_eq (d : SimplexData) (k : ℕ) : zFast d k = z d k := by
  simp only [zFast, z, weightedMoment_eq]

def t10NumeratorFast (d : SimplexData) : ℤ :=
  (∑ k ∈ Finset.Icc 2 10, zFast d k * (D d : ℤ)^(10 - k)) * (d.L : ℤ)^10

private theorem t10Numerator_eq (d : SimplexData) :
    t10NumeratorFast d = t10Numerator d := by
  simp only [t10NumeratorFast, t10Numerator, z_eq]

def t10Fast (d : SimplexData) : ExactFraction :=
  ⟨t10NumeratorFast d, t10Denominator d, t10_denominator_pos d⟩

theorem t10_eq (d : SimplexData) : t10Fast d = t10 d := by
  simp only [t10Fast, t10, t10Numerator_eq]

open P2Winner9MixedDegreeSixExactAssembly
  (conv doubled mixedNumerator mixedTerm mixedTermNumerator mixedTermDenominator
    mixed_term_denominator_pos mixedTerms q6)

/-- Replace the homogeneous input to the original signed convolution. -/
def mixedNumeratorFast (d : SimplexData) (j : Fin 10) (k : ℕ) : ℤ :=
  conv (fun n => (homogeneousFast d.y n : ℤ)) (doubled d j) k

theorem mixedNumerator_eq (d : SimplexData) (j : Fin 10) (k : ℕ) :
    mixedNumeratorFast d j k = mixedNumerator d j k := by
  simp only [mixedNumeratorFast, mixedNumerator, homogeneous_eq]

def mixedTermFast (d : SimplexData) (j : Fin 10) (k : Fin 7) : ExactFraction :=
  ⟨(d.L : ℤ)^10 * mixedNumeratorFast d j k.val, mixedTermDenominator d j k.val,
    mixed_term_denominator_pos d j k.val⟩

private theorem mixedTerm_eq (d : SimplexData) (j : Fin 10) (k : Fin 7) :
    mixedTermFast d j k = mixedTerm d j k := by
  simp only [mixedTermFast, mixedTerm, mixedTermNumerator, mixedNumerator_eq]

def q6Fast (d : SimplexData) : ExactFraction :=
  sumFractions ((List.ofFn (fun j : Fin 10 =>
    List.ofFn (fun k : Fin 7 => mixedTermFast d j k))).flatten)

theorem q6_eq (d : SimplexData) : q6Fast d = q6 d := by
  simp only [q6Fast, q6, mixedTerms, mixedTerm_eq]

def totalFast (d : SimplexData) : ExactFraction := add (t10Fast d) (q6Fast d)

theorem total_eq (d : SimplexData) :
    totalFast d = P2Winner9MixedDegreeSixExactAssembly.total d := by
  simp only [totalFast, P2Winner9MixedDegreeSixExactAssembly.total, t10_eq, q6_eq]

end ImbalancedChen.P2Winner9FastExactAssembly
