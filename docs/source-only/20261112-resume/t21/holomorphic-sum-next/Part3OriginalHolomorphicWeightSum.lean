import ImbalancedChen.Part3OriginalHolomorphicProjectionMarks
import ImbalancedChen.Part3OriginalHolomorphicBasisMass

/-! The positive holomorphic contribution of the prescribed test on the two original
cusps, absolutely over the dependent full basis and jointly over all physical moduli
and odd Bessel orders. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicWeightSum20261112
open Complex Matrix
open scoped MatrixGroups BigOperators InnerProductSpace ComplexConjugate
open OriginalHolomorphicCuspFrames20261110 (frameR)
open OriginalHolomorphicPeterssonSpace20261112 (BasisIndex formsBasis)
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalHolomorphicBasisMass20261112 (basisCost basis_mass)
open Gamma0ActualCuspsSourceOnly (cuspOneMatrix)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPositiveHolomorphicWeights20261112 (moment holWeight)
open ActualPositiveHolomorphicDiagonal20261112 (diagonalMoment)
open OriginalHolomorphicProjectionPrices20261112 (joint joint_absolute weighted_moments)
open OriginalOppositeMarkedKuznetsov20261112 (modulusTerm)
open OriginalCompletedReciprocalSource20261102 OriginalPrimaryPacketRows20261102
open OriginalSignedTraceInput20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalCommonPoissonLanes20261102

private theorem weight_cost (N p b j : ℕ) [NeZero N] (hp : 0<p) (hb : 0<b) (Φ : ℝ→ℂ) :
    (∑ i,‖basisTerm N p b Φ j i‖) ≤
      ((basisCost N p 1+basisCost N b cuspOneMatrix)/Real.pi)*
        (((2*j+1:ℕ):ℝ)*‖moment (2*j+1) Φ‖) := by
  let L := fun i : BasisIndex N (j+1) => ‖frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) 1 p‖
  let R := fun i : BasisIndex N (j+1) => ‖frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) cuspOneMatrix b‖
  let τ := 4*Real.pi*Real.Gamma (2*(j:ℝ)+1)
  have hΓ : 0<Real.Gamma (2*(j:ℝ)+1) := Real.Gamma_pos_of_pos (by positivity)
  have hτ : 0≤τ := by dsimp [τ];positivity
  have M : τ*(∑ i,L i*R i)≤basisCost N p 1+basisCost N b cuspOneMatrix := by
    calc
      _ ≤ τ*(∑ i,(L i^2+R i^2)) := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (L i-R i),sq_nonneg (L i),sq_nonneg (R i)]) hτ
      _ = τ*(∑ i,L i^2)+τ*(∑ i,R i^2) := by rw [Finset.sum_add_distrib,mul_add]
      _ ≤ _ := add_le_add (basis_mass N j hp 1) (basis_mass N j hb cuspOneMatrix)
  let n : ℝ := ((2*j+1:ℕ):ℝ)
  let v := ‖moment (2*j+1) Φ‖
  have normTerm (i : BasisIndex N (j+1)) :
      ‖basisTerm N p b Φ j i‖=(n*v/Real.pi)*(τ*(L i*R i)) := by
    have hk : 2*((j+1:ℕ):ℝ)-1=2*(j:ℝ)+1 := by push_cast;ring
    rw [basisTerm,norm_mul,norm_mul,norm_mul,Complex.norm_conj,Complex.norm_real,gamma_step,hk,
      Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hΓ.le)]
    simp only [holWeight,norm_mul,norm_pow,Complex.norm_I,one_pow,mul_one,Complex.norm_ofNat]
    dsimp [n,v,τ,L,R]
    field_simp [Real.pi_ne_zero] <;>ring
  simp_rw [normTerm]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  calc
    _ ≤ (n*v/Real.pi)*(basisCost N p 1+basisCost N b cuspOneMatrix) :=
      mul_le_mul_of_nonneg_left M (by dsimp [n,v];positivity)
    _ = _ := by dsimp [n,v];ring

/-- Absolute before grouping by weight, including every vector of weight two. -/
theorem holomorphic_absolute (z p b : ℕ) [NeZero z] (hp : 0<p) (hb : 0<b)
    (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    Summable (fun t : (Σ j : ℕ,BasisIndex z (j+1)) =>
      ‖basisTerm z p b (spectralTest ell Y) t.1 t.2‖) := by
  apply (summable_sigma_of_nonneg (fun t => norm_nonneg _)).mpr
  refine ⟨fun j => (hasSum_fintype _).summable,?_⟩
  simp only [tsum_fintype]
  exact ((weighted_moments ell hY).mul_left
    ((basisCost z p 1+basisCost z b cuspOneMatrix)/Real.pi)).of_nonneg_of_le
      (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (fun j => weight_cost z p b j hp hb _)

/-- Physical positive sign determined by the original two markings; the diagonal uses
the scalar order-zero integral of the *same* test and the unshifted native mark. -/
theorem original_holomorphic_projection (D : OriginalData) (k : BlockKey) (negativeM : Bool)
    (ha : D.block.atom.residue≠0) (hs : traceNegative D k negativeM=false)
    (z : ℕ) [NeZero z] (J j : ℕ) {p n : ℕ} (hp : p∈commonMBlock J j)
    (hn : n∈nCarrier D k z) (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    let b := traceIndex D k negativeM z n
    let Φ := spectralTest ell Y
    0<b ∧
    Summable (fun t : (Σ l : ℕ,BasisIndex z (l+1)) => ‖basisTerm z p b.natAbs Φ t.1 t.2‖) ∧
    Summable (fun t : ℕ+ × ℕ => ‖joint z p b.natAbs Φ t‖) ∧
    Summable (fun d : ℕ+ => ‖modulusTerm (oddProjection ell Y) z p b d‖) ∧
    (∑' d : ℕ+,modulusTerm (oddProjection ell Y) z p b d)=holSpectrum z p b.natAbs Φ+
      (if z=1 ∧ (p:ℤ)=b then diagonalMoment 0 Φ/(2*(Real.pi:ℂ)) else 0) := by
  let b := traceIndex D k negativeM z n
  have pm : 0<p := lt_of_lt_of_le (pow_pos (by norm_num : 0<(2:ℕ)) j) (Finset.mem_Ico.mp hp).1
  have bn : 0<b.natAbs := traceIndex_natAbs_pos D k negativeM z hn ha
  have bi : (b.natAbs:ℤ)=b :=
    (OriginalPositivePeterssonTrace20261112.original_positive_petersson D k negativeM ha hs z 1 J j
      (by decide) hp hn).1
  have bz : 0<b := by rw [←bi];exact_mod_cast bn
  exact ⟨bz,holomorphic_absolute z p b.natAbs pm bn ell hY,
    joint_absolute z p b.natAbs pm ell hY,positive_mark_holomorphic z p pm bz ell hY⟩

end ImbalancedChen.Part3.OriginalHolomorphicWeightSum20261112
end
