import ImbalancedChen.Part3OriginalHolomorphicProjectionPrices
import ImbalancedChen.Part3OriginalPositiveProjection

/-! Sum the Petersson identities with the transform of the prescribed test at every even
weight. The geometric side uses the same residual as the positive cosine projection. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicWeightSum20261112
open Complex
open scoped BigOperators MatrixGroups InnerProductSpace ComplexConjugate
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalHolomorphicCuspFrames20261110 (frameR)
open Gamma0ActualCuspsSourceOnly (cuspOneMatrix)
open OriginalHolomorphicPeterssonSpace20261112 (formsBasis BasisIndex)
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalPeterssonNormalizedOrbits20261112 (modulus)
open ActualPositiveHolomorphicWeights20261112 ActualPositiveHolomorphicDiagonal20261112
open OriginalPositivePeterssonTrace20261112 (geometry spectrum coincidence petersson)
open OriginalHolomorphicProjectionPrices20261112
open OriginalPositiveStrip20261112 (residual)

def multiplier (Φ : ℝ→ℂ) (j : ℕ) : ℂ := ((2*j+1:ℕ):ℂ)*holWeight j Φ/(4*(Real.pi:ℂ))

def basisTerm (N m h : ℕ) [NeZero N] (Φ : ℝ→ℂ) (j : ℕ) (i : BasisIndex N (j+1)) : ℂ :=
  (Real.Gamma (2*((j+1:ℕ):ℝ)):ℂ)*holWeight j Φ*
    (conj (frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) 1 m)*
      frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) cuspOneMatrix h)

def diagonalTerm (N m h : ℕ) (Φ : ℝ→ℂ) : ℂ :=
  coincidence N m h*diagonalMoment 0 Φ/(2*(Real.pi:ℂ))

def projectedRow (N m h : ℕ) (ell : D4→ℤ) (Y : ℝ) (d : ℕ+) : ℂ :=
  arithmetic N m h d*(spectralTest ell Y (qMark N m h d)-residual ell Y (qMark N m h d))

theorem gamma_step (j : ℕ) :
    Real.Gamma (2*((j+1:ℕ):ℝ))=((2*j+1:ℕ):ℝ)*Real.Gamma (2*((j+1:ℕ):ℝ)-1) := by
  let n : ℝ := ((2*j+1:ℕ):ℝ)
  have hn : n≠0 := by dsimp [n];positivity
  have hw : 2*((j+1:ℕ):ℝ)=n+1 := by dsimp [n];push_cast;ring
  rw [hw,add_sub_cancel_right,Real.Gamma_add_one hn]

theorem weighted_basis (N m h : ℕ) [NeZero N] (Φ : ℝ→ℂ) (j : ℕ) :
    multiplier Φ j*spectrum N (j+1) m h=∑ i,basisTerm N m h Φ j i := by
  unfold multiplier spectrum basisTerm
  rw [←Finset.mul_sum,gamma_step]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;>ring

theorem weighted_geometry (N m h : ℕ) [NeZero N] (Φ : ℝ→ℂ) (d : ℕ+) (j : ℕ) :
    multiplier Φ j*geometry N (j+1) m h d=joint N m h Φ (d,j) := by
  have hp : I^(2*(j+1))*(-I)^(2*(j+1))=1 := by
    rw [←mul_pow,show I*(-I)=1 by rw [mul_neg,Complex.I_mul_I,neg_neg],one_pow]
  unfold multiplier holWeight geometry joint arithmetic oddTerm
  split_ifs with good
  · rw [show 2*(j+1)-1=2*j+1 by omega]
    calc
      _ = (I^(2*(j+1))*(-I)^(2*(j+1)))*
          (OriginalNonzeroCuspOneSource20261102.cuspOneMatrixSum N d good m h/(modulus N d:ℂ)*
            (2*((2*j+1:ℕ):ℂ)*moment (2*j+1) Φ*intJ (2*j+1) (qMark N m h d))) := by
        unfold qMark intJ
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
          Complex.ofReal_ne_zero.mpr (OriginalPeterssonNormalizedOrbits20261112.modulus_pos N d).ne']
        <;>ring
      _ = _ := by rw [hp,one_mul]
  · simp

theorem diagonal_sum (N m h : ℕ) (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    HasSum (fun j => multiplier (spectralTest ell Y) j*coincidence N m h)
      (-diagonalTerm N m h (spectralTest ell Y)) := by
  have H := ((positive_holomorphic_diagonal ell hY).div_const (4*(Real.pi:ℂ))).mul_right
    (coincidence N m h)
  convert H using 1 <;> first | rfl | (unfold diagonalTerm;ring)

theorem projectedRow_eq (N m h : ℕ) (ell : D4→ℤ) (Y : ℝ) (d : ℕ+) :
    projectedRow N m h ell Y d=∑' j,joint N m h (spectralTest ell Y) (d,j) := by
  unfold projectedRow residual
  rw [sub_sub_cancel,←tsum_mul_left]
  rfl

/-- The genuine grouped spectral (4.15) is absolutely summable over the weights. The
geometric row is absolutely summable in both orders before summing either index. -/
theorem weighted_petersson (N m h : ℕ) [NeZero N] (hm : 0<m) (hh : 0<h)
    (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    let Φ := spectralTest ell Y
    Summable (fun p : ℕ+ × ℕ => ‖joint N m h Φ p‖) ∧
    Summable (fun d : ℕ+ => ‖projectedRow N m h ell Y d‖) ∧
    Summable (fun j : ℕ => ‖∑ i,basisTerm N m h Φ j i‖) ∧
    (∑' d,projectedRow N m h ell Y d)=
      (∑' j : ℕ,∑ i,basisTerm N m h Φ j i)+diagonalTerm N m h Φ := by
  let Φ := spectralTest ell Y
  let F := joint N m h Φ
  let b := fun j : ℕ => ∑ i,basisTerm N m h Φ j i
  let a := fun j : ℕ => multiplier Φ j*coincidence N m h
  have normF := joint_absolute N m h hm ell hY
  have sF : Summable F := normF.of_norm
  have diag := diagonal_sum N m h ell hY
  have row (j : ℕ) : b j=a j+∑' d : ℕ+,F (d,j) := by
    rw [show b j=multiplier Φ j*spectrum N (j+1) m h from (weighted_basis N m h Φ j).symm,
      (petersson N (j+1) m h (by omega) hm hh).2,mul_add,←tsum_mul_left]
    congr 1
    exact tsum_congr fun d => weighted_geometry N m h Φ d j
  have sb : Summable b := (diag.summable.add sF.prod_symm.prod).congr (fun j => (row j).symm)
  have sP : Summable (projectedRow N m h ell Y) := sF.prod.congr
    (fun d => (projectedRow_eq N m h ell Y d).symm)
  refine ⟨normF,summable_norm_iff.mpr sP,summable_norm_iff.mpr sb,?_⟩
  change _=(∑' j,b j)+diagonalTerm N m h Φ
  simp_rw [projectedRow_eq]
  rw [show (∑' j,b j)=(∑' j,a j)+(∑' j,∑' d,F (d,j)) by
    simp_rw [row];exact diag.summable.tsum_add sF.prod_symm.prod,
    show (∑' j,a j) = -diagonalTerm N m h Φ from diag.tsum_eq]
  change (∑' d,∑' j,F (d,j))=_
  rw [sF.tsum_comm]
  ring

end ImbalancedChen.Part3.OriginalHolomorphicWeightSum20261112
end
