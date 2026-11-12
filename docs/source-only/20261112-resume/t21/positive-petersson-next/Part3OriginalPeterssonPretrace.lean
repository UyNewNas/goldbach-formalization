import ImbalancedChen.Part3OriginalHolomorphicPeterssonSpace
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace ImbalancedChen.Part3.OriginalPeterssonPretrace20261112

noncomputable section
open UpperHalfPlane Set MeasureTheory Matrix
open scoped MatrixGroups UpperHalfPlane ModularForm InnerProductSpace ComplexConjugate
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open NativeHolomorphicFourierNormalization20261102s Gamma0ActualCuspsSourceOnly
open OriginalCompletedReciprocalSource20261102 OriginalPrimaryPacketRows20261102
open OriginalSignedTraceInput20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalCommonPoissonLanes20261102

def raw (N : ℕ) (hN : 0<N) (r : ℕ) (g : SL(2,ℤ)) (n : ℕ) :
    Forms N r →ₗ[ℂ] ℂ where
  toFun f := (qExpansion 1 (frameForm N hN r f g)).coeff n
  map_add' f f' := by
    have h : (⇑(frameForm N hN r (f+f') g) : ℍ → ℂ) =
        ⇑(frameForm N hN r f g) + ⇑(frameForm N hN r f' g) := by
      funext w
      simp [frameForm_apply, add_mul]
    simp only [h, ModularForm.qExpansion_add (by norm_num) (normalized_frame_unit_strictPeriod N hN g),
      map_add]
  map_smul' c f := by
    have h : (⇑(frameForm N hN r (c • f) g) : ℍ → ℂ) = c • ⇑(frameForm N hN r f g) := by
      funext w
      simp [frameForm_apply, mul_assoc]
    simp only [h, ModularForm.qExpansion_smul (by norm_num) (normalized_frame_unit_strictPeriod N hN g),
      PowerSeries.coeff_smul, RingHom.id_apply]

def Rmap (N : ℕ) (hN : 0<N) (r : ℕ) (g : SL(2,ℤ)) (n : ℕ) :
    Forms N r →ₗ[ℂ] ℂ := ((Real.sqrt n : ℂ) / holomorphicScale r n) • raw N hN r g n

theorem Rmap_apply (N : ℕ) (hN : 0<N) (r : ℕ) (g : SL(2,ℤ)) (n : ℕ) (f : Forms N r) :
    Rmap N hN r g n f = frameR N hN r f g n := by
  rw [frameR, holomorphicR_eq_qExpansion]
  simp [Rmap, raw, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

def Rvector (N : ℕ) [NeZero N] (r : ℕ) (g : SL(2,ℤ)) (n : ℕ) : Forms N r :=
  (InnerProductSpace.toDual ℂ (Forms N r)).symm
    ((Rmap N (NeZero.pos N) r g n).toContinuousLinearMap)

theorem Rvector_evaluates (N : ℕ) [NeZero N] (r : ℕ) (g : SL(2,ℤ)) (n : ℕ) (f : Forms N r) :
    inner ℂ (Rvector N r g n) f = frameR N (NeZero.pos N) r f g n := by
  rw [Rvector, InnerProductSpace.toDual_symm_apply]
  exact Rmap_apply N _ r g n f

/-- The right cusp acts on the left Riesz slot of the cross-cusp Gram matrix. -/
theorem full_basis_product (N : ℕ) [NeZero N] (r : ℕ) (g h : SL(2,ℤ)) (m n : ℕ) :
    ∑ i, conj (frameR N (NeZero.pos N) r (formsBasis N r i) g m) *
        frameR N (NeZero.pos N) r (formsBasis N r i) h n =
      inner ℂ (Rvector N r h n) (Rvector N r g m) := by
  rw [← (formsBasis N r).sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Rvector_evaluates N r g m, ← Rvector_evaluates N r h n, inner_conj_symm]
  ring

/-- Both marks come from the manuscript row and the sum uses every form of this weight. -/
theorem original_positive_basis_pretrace (D : OriginalData) (k : BlockKey)
    (negativeM : Bool) (ha : D.block.atom.residue ≠ 0)
    (hsign : traceNegative D k negativeM = false) (N : ℕ) [NeZero N] (r J j : ℕ) {m n : ℕ}
    (hm : m ∈ commonMBlock J j) (hn : n ∈ nCarrier D k N) :
    let h := traceIndex D k negativeM N n
    (h.natAbs : ℤ) = h ∧
      ∑ i, conj (sieveCoeff N (NeZero.pos N) r (formsBasis N r i) 1 m) *
        sieveCoeff N (NeZero.pos N) r (formsBasis N r i) cuspOneMatrix h.natAbs =
        (((4*Real.pi : ℝ) : ℂ)^(2*r)) *
          inner ℂ (Rvector N r cuspOneMatrix h.natAbs) (Rvector N r 1 m) := by
  dsimp only
  constructor
  · exact (original_positive_holomorphic_product D k negativeM ha hsign N (NeZero.pos N)
      r (0 : Forms N r) J j hm hn).1
  · rw [← full_basis_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (original_positive_holomorphic_product D k negativeM ha hsign N
      (NeZero.pos N) r (formsBasis N r i) J j hm hn).2

def mass (r m : ℕ) : ℝ :=
  (1 / (4*Real.pi*m))^(2*r-1) * Real.Gamma (2*(r : ℝ)-1)

/-- The vertical integral obtained by unfolding the original unscaled Petersson measure. -/
theorem mass_integral {r m : ℕ} (hr : 0<r) (hm : 0<m) :
    (∫ y : ℝ in Ioi 0, y^(2*r-2) * Real.exp (-(4*Real.pi*m*y))) = mass r m := by
  have hk : 0 < 2*(r : ℝ)-1 := by have : (1:ℝ) ≤ r := by exact_mod_cast hr; linarith
  have h1 : (2*(r : ℝ)-1) = ((2*r-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*r)]; push_cast; ring
  have h2 : (2*(r : ℝ)-1)-1 = ((2*r-2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2*r)]; push_cast; ring
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi hk (by positivity : 0 < 4*Real.pi*(m:ℝ))
  rw [h2, Real.rpow_natCast] at hg
  unfold mass
  convert hg using 2
  rw [h1, Real.rpow_natCast]

/-- The Riesz representative of the *unfolded* Fourier functional. -/
def Pvector (N : ℕ) [NeZero N] (r : ℕ) (g : SL(2,ℤ)) (m : ℕ) : Forms N r :=
  (mass r m : ℂ) • (InnerProductSpace.toDual ℂ (Forms N r)).symm
    ((raw N (NeZero.pos N) r g m).toContinuousLinearMap)

theorem Pvector_evaluates (N : ℕ) [NeZero N] (r : ℕ) (g : SL(2,ℤ)) (m : ℕ) (f : Forms N r) :
    inner ℂ (Pvector N r g m) f = (mass r m : ℂ) * raw N (NeZero.pos N) r g m f := by
  simp [Pvector, inner_smul_left, InnerProductSpace.toDual_symm_apply]

theorem coefficient_of_Pvector (N : ℕ) [NeZero N] (r : ℕ) (g h : SL(2,ℤ)) (m n : ℕ) :
    raw N (NeZero.pos N) r h n (Pvector N r g m) =
      (mass r m : ℂ) * ∑ i, conj (raw N (NeZero.pos N) r g m (formsBasis N r i)) *
        raw N (NeZero.pos N) r h n (formsBasis N r i) := by
  let P := Pvector N r g m
  calc
    _ = raw N (NeZero.pos N) r h n (∑ i, inner ℂ (formsBasis N r i) P • formsBasis N r i) :=
      congrArg _ (basis_complete N r P).symm
    _ = _ := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, ← inner_conj_symm, Pvector_evaluates]
      simp [mul_assoc, smul_eq_mul]

end
end ImbalancedChen.Part3.OriginalPeterssonPretrace20261112
