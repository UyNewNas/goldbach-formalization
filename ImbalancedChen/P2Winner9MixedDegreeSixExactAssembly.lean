import ImbalancedChen.P2Winner9CurvatureFullExactAssembly
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Typed exact degree-six mixed correction from the pinned mixed-moment note and
producer. The signed generating-function coefficient N_{j,k} is constructed
for every one of ten factors and k=0..6, then all seventy exact rational
terms are assembled with positive denominators. This is a distinct Q6,
not an additional copy of the older curvature Q0. The exact old T10 is
reused, and the total is rounded once to Q80 before the Jensen product is
rounded once to Q96. No producer, checker, kernel or numerical replay ran.

The coefficient formula's analytic Dirichlet interpretation, equivalence
with the fast producer's common-denominator optimization, k=0 agreement
with the previous curvature stream, physical cap, actual row data and the
full 11,026-row certificate remain separate obligations.
-/

namespace ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly

open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor

/-- Finite coefficient convolution at degree k. -/
def conv (a b : Nat → ℤ) (k : Nat) : ℤ :=
  ∑ r ∈ Finset.range (k + 1), a r * b (k - r)

def B1 (d : SimplexData) (j : Fin 10) (k : Nat) : ℤ :=
  ∑ i : Fin 9, d.deviations j i * (d.y i : ℤ)^k

def B2 (d : SimplexData) (j : Fin 10) (k : Nat) : ℤ :=
  (k + 1 : ℤ) *
    (∑ i : Fin 9, (d.deviations j i)^2 * (d.y i : ℤ)^k)

def W0 (d : SimplexData) (k : Nat) : ℤ :=
  ∑ i : Fin 9, (d.gaps i : ℤ) * (d.y i : ℤ)^k

def W1 (d : SimplexData) (j : Fin 10) (k : Nat) : ℤ :=
  (k + 1 : ℤ) *
    (∑ i : Fin 9, (d.gaps i : ℤ) * d.deviations j i *
      (d.y i : ℤ)^k)

def W2 (d : SimplexData) (j : Fin 10) (k : Nat) : ℤ :=
  ((k + 2).choose 2 : ℤ) *
    (∑ i : Fin 9, (d.gaps i : ℤ) * (d.deviations j i)^2 *
      (d.y i : ℤ)^k)

/-- Twice the weighted u² coefficient in the pinned source formula (M). -/
def doubled (d : SimplexData) (j : Fin 10) (k : Nat) : ℤ :=
  2 * W2 d j k +
  2 * conv (B1 d j) (W1 d j) k +
  conv (fun n => conv (B1 d j) (B1 d j) n + B2 d j n)
    (W0 d) k

/-- The signed exact integer numerator of the mixed k-th moment.
Intermediate convolution coefficients are not assumed nonnegative. -/
def mixedNumerator (d : SimplexData) (j : Fin 10) (k : Nat) : ℤ :=
  conv (fun n => (homogeneous d.y n : ℤ)) (doubled d j) k

/-- The source's simplified contribution after
`choose(9+k,k)*k!/(10)_(k+2)=1/((k+10)(k+11))`, represented with
the unreduced `Y_i=y_i/U` and `U_phys=U/L` denominators. -/
def mixedTermNumerator (d : SimplexData) (j : Fin 10) (k : Nat) : ℤ :=
  (d.L : ℤ)^10 * mixedNumerator d j k

def mixedTermDenominator (d : SimplexData) (j : Fin 10) (k : Nat) : Nat :=
  2 * gapTotal d.gaps * d.U^k * (k + 10) * (k + 11) *
    (d.maxima j)^2 * d.U^10

theorem mixed_term_denominator_pos
    (d : SimplexData) (j : Fin 10) (k : Nat) :
    0 < mixedTermDenominator d j k := by
  unfold mixedTermDenominator
  have hg := d.gapsPos
  have hu := d.UPos
  have hv := d.maximaPos j
  positivity

def mixedTerm (d : SimplexData) (j : Fin 10) (k : Fin 7) :
    ExactFraction :=
  ⟨mixedTermNumerator d j k.val,
    mixedTermDenominator d j k.val,
    mixed_term_denominator_pos d j k.val⟩

/-- All 10 × 7 exact source terms, with neither filtering nor term floors. -/
def mixedTerms (d : SimplexData) : List ExactFraction :=
  (List.ofFn (fun j : Fin 10 =>
    List.ofFn (fun k : Fin 7 => mixedTerm d j k))).flatten

def q6 (d : SimplexData) : ExactFraction := sumFractions (mixedTerms d)

/-- Full exact `T10 + Q6`. The curvature Q0 is not added separately. -/
def total (d : SimplexData) : ExactFraction := add (t10 d) (q6 d)

theorem q6_value (d : SimplexData) :
    value (q6 d) = ((mixedTerms d).map value).sum := by
  exact sumFractions_value (mixedTerms d)

theorem total_value (d : SimplexData) :
    value (total d) = value (t10 d) +
      ((mixedTerms d).map value).sum := by
  simp [total, q6, add_value, sumFractions_value]

/-- Exact factor-degree fraction, before summing and rounding. -/
theorem mixed_term_fraction (d : SimplexData)
    (j : Fin 10) (k : Fin 7) :
    value (mixedTerm d j k) =
      (mixedTermNumerator d j k.val : ℚ) /
        mixedTermDenominator d j k.val := rfl

/-- One Q80 floor of T10+Q6, then one Q96 floor of positive Jensen,
gives the mixed raw bound. The former curvature maximum is a predecessor
for the later maximum, not another summand in this expression. -/
theorem mixed_directed_floor_semantics
    (d : SimplexData) (tFloor raw : Nat)
    (hT : curvatureFloorQ80 (total d).num (total d).den tFloor)
    (hRaw : jensenProductFloorQ96 d.jensenNum d.jensenDen
      tFloor raw) :
    (raw : ℚ) / q96 ≤
      ((d.jensenNum : ℚ) / d.jensenDen) * (1 + value (total d)) := by
  have ht : (tFloor : ℚ) / q80 ≤ value (total d) := by
    simpa [value] using (curvature_floor_Q80_semantics hT).1
  have hr : (raw : ℚ) / q96 ≤
      ((d.jensenNum : ℚ) / d.jensenDen) *
        (1 + (tFloor : ℚ) / q80) := by
    simpa [jensen_product_fraction d.jensenNum d.jensenDen
      tFloor d.jensenDenPos] using
      (jensen_product_floor_Q96_semantics hRaw).1
  calc
    (raw : ℚ) / q96 ≤
        ((d.jensenNum : ℚ) / d.jensenDen) *
          (1 + (tFloor : ℚ) / q80) := hr
    _ ≤ ((d.jensenNum : ℚ) / d.jensenDen) *
        (1 + value (total d)) := by
      apply mul_le_mul_of_nonneg_left (by linarith [ht])
      positivity

/-- The mixed stage can only replace the already selected curvature floor.
The ledger increment is this difference, never the full new raw floor. -/
theorem selected_replacement (previous raw : Nat) :
    previous ≤ max previous raw ∧
    ((max previous raw : ℤ) - previous) + previous = max previous raw := by
  constructor
  · exact le_max_left _ _
  · omega

end ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly
