import ImbalancedChen.Part3OriginalSameInfinityHolomorphicTrace
import ImbalancedChen.Part3OriginalSameInfinityScalarGeometry
import ImbalancedChen.Part3OriginalHolomorphicWeightSum

/-! Sum the positive-weight Petersson sector at the two identity frames.
The level-one comparison evaluates only the classical Bessel summand. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityWeightedHol20261113
noncomputable section
open Complex
open scoped BigOperators MatrixGroups ComplexConjugate
open OriginalSameInfinityHolomorphicTrace20261113 OriginalSameInfinityScalarGeometry20261113 (term term_filter)
open OriginalHolomorphicCuspFrames20261110 (frameR) OriginalHolomorphicPeterssonSpace20261112 (BasisIndex formsBasis)
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalHolomorphicProjectionPrices20261112 (joint joint_absolute)
open OriginalHolomorphicWeightSum20261112 (multiplier diagonalTerm diagonal_sum projectedRow_eq physical_modulus oddProjection gamma_step)
open OriginalPositivePeterssonTrace20261112 (geometry coincidence)
open OriginalPeterssonNormalizedOrbits20261112 (modulus)
open OriginalPeterssonLipschitz20261112 (argument)
open ActualPositiveHolomorphicWeights20261112 (holWeight)
open ActualPositiveHolomorphicDiagonal20261112 (diagonalMoment)
open OriginalSmoothPoissonTail (kloosterman) ActualGeneralJBesselSourceOnly (generalJ)
open P3NativePeriod64SamplingSourceOnly (D4) P3Period64NativeReconstructionSourceOnly (spectralTest)
open private one_sum from ImbalancedChen.Part3OriginalSameInfinityScalarGeometry

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def basisTerm (q m n : ℕ+) (Φ : ℝ→ℂ) (j : ℕ) (i : BasisIndex q.val (j+1)) : ℂ :=
  (Real.Gamma (2*((j+1:ℕ):ℝ)):ℂ)*holWeight j Φ*
    (conj (frameR q.val (NeZero.pos q.val) (j+1) (formsBasis q.val (j+1) i) 1 m.val)*
      frameR q.val (NeZero.pos q.val) (j+1) (formsBasis q.val (j+1) i) 1 n.val)

def holSum (q m n : ℕ+) (Φ : ℝ→ℂ) := ∑' j : ℕ,∑ i,basisTerm q m n Φ j i

def diagonal (m n : ℕ+) (Φ : ℝ→ℂ) : ℂ :=
  if (m.val:ℤ)=(n.val:ℤ) then diagonalMoment 0 Φ/(2*(Real.pi:ℂ)) else 0

private def F (q m n : ℕ+) (Φ : ℝ→ℂ) (p : ℕ+×ℕ) :=
  if q.val∣p.1.val then joint 1 m.val n.val Φ p else 0

private theorem basis_weight (q m n : ℕ+) (Φ : ℝ→ℂ) (j : ℕ) :
    multiplier Φ j*(((4*Real.pi*Real.Gamma (2*(j:ℝ)+1):ℝ):ℂ)*
      ∑ i,conj (frameR q.val (NeZero.pos q.val) (j+1) (formsBasis q.val (j+1) i) 1 m.val)*
        frameR q.val (NeZero.pos q.val) (j+1) (formsBasis q.val (j+1) i) 1 n.val)=
      ∑ i,basisTerm q m n Φ j i := by
  simp only [basisTerm,←Finset.mul_sum,gamma_step]
  simp only [multiplier]
  rw [show 2*((j+1:ℕ):ℝ)-1=2*(j:ℝ)+1 by push_cast;ring]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

private theorem one_geometry (m n k : ℕ+) (j : ℕ) :
    geometry 1 (j+1) m.val n.val k=
      ((2*Real.pi/(k:ℝ):ℝ):ℂ)*(-I)^(2*(j+1))*kloosterman k.val (m.val:ℤ) (n.val:ℤ)*
      generalJ ((2*j+1:ℕ):ℂ) (argument (Real.sqrt m.val) (Real.sqrt n.val) (k:ℝ)) := by
  simp [geometry,modulus,one_sum m n k,show 2*(j+1)-1=2*j+1 by omega]

private theorem weighted_row (q m n : ℕ+) (Φ : ℝ→ℂ) (j : ℕ) :
    (∑ i,basisTerm q m n Φ j i)=multiplier Φ j*coincidence 1 m.val n.val+
      ∑' k : ℕ+,F q m n Φ (k,j) := by
  have T := (same_infinity_petersson q.val j m.val n.val m.property n.property).2
  have C : coincidence 1 m.val n.val=(if m.val=n.val then (1:ℂ) else 0) := by simp [coincidence]
  rw [←basis_weight,T,mul_add,C,←tsum_mul_left]
  apply congrArg (_+·)
  apply tsum_congr
  intro k
  by_cases good : q.val∣k.val
  · simp only [F,if_pos good,←one_geometry]
    exact OriginalHolomorphicWeightSum20261112.weighted_geometry 1 m.val n.val Φ k j
  · simp [F,good]

theorem weighted_hol (q m n : ℕ+) (ell : D4→ℤ) {Y : ℝ} (yp : 0<Y) :
    let Φ := spectralTest ell Y
    Summable (fun k : ℕ+ => ‖term (oddProjection ell Y) q m n k‖) ∧
    Summable (fun j : ℕ => ‖∑ i,basisTerm q m n Φ j i‖) ∧
      (∑' k : ℕ+,term (oddProjection ell Y) q m n k)=holSum q m n Φ+diagonal m n Φ := by
  let Φ := spectralTest ell Y
  have SF : Summable (fun p => ‖F q m n Φ p‖) := by
    apply (joint_absolute 1 m.val n.val m.property ell yp).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro p
    by_cases good : q.val∣p.1.val <;> simp [F,good]
  have S : Summable (F q m n Φ) := SF.of_norm
  have proj (k : ℕ+) : term (oddProjection ell Y) q m n k=∑' j,F q m n Φ (k,j) := by
    rw [term_filter]
    by_cases good : q.val∣k.val
    · simpa only [F,if_pos good,physical_modulus] using projectedRow_eq 1 m.val n.val ell Y k
    · simp [F,good]
  have A := diagonal_sum 1 m.val n.val ell yp
  have T := (A.add S.prod_symm.prod.hasSum).congr_fun
    (fun j => weighted_row q m n Φ j)
  have P := S.prod.hasSum.congr_fun proj
  have diag : diagonalTerm 1 m.val n.val Φ=diagonal m n Φ := by
    by_cases same : m.val=n.val <;> simp [diagonalTerm,coincidence,diagonal,same]
  refine ⟨summable_norm_iff.mpr P.summable,summable_norm_iff.mpr T.summable,?_⟩
  change _=(∑' j,∑ i,basisTerm q m n Φ j i)+diagonal m n Φ
  rw [P.tsum_eq,T.tsum_eq,diag]
  change (∑' k,∑' j,F q m n Φ (k,j))= -diagonal m n Φ+
    (∑' j,∑' k,F q m n Φ (k,j))+diagonal m n Φ
  rw [S.tsum_comm]
  ring

end
end ImbalancedChen.Part3.OriginalSameInfinityWeightedHol20261113
