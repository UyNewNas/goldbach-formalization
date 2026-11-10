import ImbalancedChen.Part3ActualCharacterCuspExpansion
import ImbalancedChen.Part3CharacterMiddleSeriesAsymptotic
import ImbalancedChen.Part3Gamma0EffectiveActionKernel
import ImbalancedChen.Part3Gamma0GeneralCuspUnitPeriod

/-! Physical incoming amplitudes of the normalized parabolic series and
their actual oldform combinations. The two signed zero rows and the
dominated nonhorizontal lattice tail are evaluated in one unit-width
observing frame. The asymptotics here are for real s>1. -/
namespace ImbalancedChen.Part3.ActualParabolicIncoming20261110

noncomputable section
open Set Filter Topology Matrix Matrix.SpecialLinearGroup Complex UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators
open PrimitiveEisensteinParameterAnalytic PrimitiveEisensteinParameterAutomorphy
open PrimitiveRealEisensteinAutomorphy CharacterEisensteinSeries
open CharacterMiddleZeroFirstPairs20261026b CharacterEisensteinGrowingHeight20261026b
open CharacterMiddleSeriesAsymptotic20261026b ActualCharacterCuspExpansion20261110
open Gamma0GeneralCuspWidth20261025a Gamma0GeneralCuspUnitPeriod20261025a
open Gamma0EffectiveActionKernel20261024z Gamma0ParabolicBottomRow20261025a
open NativeAllCuspEisenstein20261026b OriginalCharacterPairDilation20261102s
open NativeAllCuspFrameCovariance20261026b Gamma0CuspLeftWidthCovariance20261026b

local instance (N : ℕ) : DecidableEq (CuspRowClass N) := Classical.decEq _
local instance (N : ℕ) : DecidableEq (NativeCusps N) := Classical.decEq _

def inClass (N : ℕ) (g h : SL(2,ℤ)) (v : PrimitivePair) : ℂ := by
  classical
  exact if allowedRow N g ((primitivePairEquiv h).symm v) then 1 else 0

private theorem norm_inClass (N : ℕ) (g h : SL(2,ℤ)) (v : PrimitivePair) :
    ‖inClass N g h v‖ ≤ 1 := by classical; unfold inClass; split <;> simp

theorem parabolic_reindex (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ)) (s : ℂ) (z : ℍ) :
    cuspEisenstein N g s (normalizedScaling N hN h • z) =
      (1/2 : ℂ)*widthFactor N g s*∑' v : PrimitivePair,
        inClass N g h v*complexSeed (scaledPoint (cuspWidth N h) (cuspWidth_pos N hN h) z) v s := by
  classical
  let Z := scaledPoint (cuspWidth N h) (cuspWidth_pos N hN h) z
  have hz : normalizedScaling N hN h • z = h • Z := by
    rw [normalizedScaling,mul_smul,integralReal_smul]
    rfl
  rw [cuspEisenstein_eq_widthFactor_mul N hN,hz]
  congr 1
  change (∑' v : {v : PrimitivePair // v ∈ {v | allowedRow N g v}}, complexSeed (h • Z) v.1 s) = _
  rw [tsum_subtype]
  rw [← (primitivePairEquiv h).tsum_eq (fun v => inClass N g h v*complexSeed Z v s)]
  apply tsum_congr
  intro v
  by_cases H : allowedRow N g v <;> simp [Set.indicator,inClass,H,complexSeed_SL2_apply]

private theorem inverse_row_plus (h : SL(2,ℤ)) :
    (primitivePairEquiv h).symm zeroFirstPlus = matrixRow h⁻¹ := by
  apply (primitivePairEquiv h).injective
  rw [Equiv.apply_symm_apply,← matrixRow_mul,inv_mul_cancel]
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [matrixRow,bottomRow,zeroFirstPlus]

private theorem inverse_row_minus (h : SL(2,ℤ)) :
    (primitivePairEquiv h).symm zeroFirstMinus = matrixRow (-h⁻¹) := by
  apply (primitivePairEquiv h).injective
  rw [Equiv.apply_symm_apply,← matrixRow_mul,neg_mul,inv_mul_cancel]
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [matrixRow,bottomRow,zeroFirstMinus]

theorem class_zero_rows (N : ℕ) (g h : SL(2,ℤ)) :
    let A := rowClass N (matrixRow g⁻¹)
    let B := rowClass N (matrixRow h⁻¹)
    inClass N g h zeroFirstPlus = (if B = A then 1 else 0) ∧
      inClass N g h zeroFirstMinus = (if B = A then 1 else 0) := by
  classical
  have hneg : rowClass N (matrixRow (-h⁻¹)) = rowClass N (matrixRow h⁻¹) := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨gamma0NegOne N,?_⟩
    change primitivePairEquiv (-1 : SL(2,ℤ)) (matrixRow h⁻¹) = _
    rw [← matrixRow_mul,mul_neg,mul_one]
  simp only [inClass,inverse_row_plus,inverse_row_minus,allowed_iff_same_class,hneg,and_self]

private theorem width_real_power (N : ℕ) (hN : 0 < N) (g : SL(2,ℤ)) (s : ℝ) :
    widthFactor N g (s : ℂ)*(((cuspWidth N g : ℝ)^s : ℝ) : ℂ) = 1 := by
  have hw : 0 < (cuspWidth N g : ℝ) := by exact_mod_cast cuspWidth_pos N hN g
  rw [widthFactor,Real.rpow_def_of_pos hw,Complex.ofReal_exp,← Complex.exp_add]
  convert Complex.exp_zero using 1
  congr 1
  push_cast
  ring

/-- Actual Kronecker incoming normalization at every integral observing
frame. Both the full genuine lattice sum and its cusp-width diagonal
are present; the limit follows from the native height-one dominating
series for its nonhorizontal rows. -/
theorem parabolic_incoming (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (s : ℝ) (hs : 1 < s) (x : ℝ) :
    Tendsto (fun y : ℝ => cuspEisenstein N g (s : ℂ) (normalizedScaling N hN h • cuspPoint x y) /
        ((y^s : ℝ) : ℂ)) atTop
      (𝓝 (if nativeFrameOrbit N h = nativeFrameOrbit N g then (1 : ℂ) else 0)) := by
  classical
  let k := cuspWidth N h
  let hk : 0 < k := cuspWidth_pos N hN h
  let Z := fun y : ℝ => scaledPoint k hk (cuspPoint x y)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hX (y : ℝ) : (Z y).re = (k : ℝ)*x := by
    simpa [Z,Complex.mul_re] using congrArg Complex.re (scaledPoint_coe k hk (cuspPoint x y))
  have hY (y : ℝ) : 1 ≤ (Z y).im := by
    change 1 ≤ (scaledPoint k hk (cuspPoint x y)).im
    rw [scaledPoint_im,cuspPoint_im]
    exact one_le_mul_of_one_le_of_one_le hk1 (le_max_left _ _)
  have h∞ : Tendsto (fun y => (Z y).im) atTop atTop := by
    simpa only [Z,scaledPoint_im] using (cuspPoint_im_tendsto x).const_mul_atTop hkR
  let W := inClass N g h
  let Y := fun v : ℝ => weightedRemainder W s (Z v)
  have ht : Tendsto Y atTop (𝓝 0) :=
    weightedRemainder_tendsto_zero W (norm_inClass N g h) s hs _ Z hX hY h∞
  let F : ℂ := (1/2 : ℂ)*widthFactor N g (s : ℂ)*(((k : ℝ)^s : ℝ) : ℂ)
  have he : (fun y : ℝ => cuspEisenstein N g (s : ℂ) (normalizedScaling N hN h • cuspPoint x y) /
      ((y^s : ℝ) : ℂ)) =ᶠ[atTop] fun y => F*(W zeroFirstPlus+W zeroFirstMinus+Y y) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
    have hpow : ((y^s : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hy0 s).ne'
    rw [parabolic_reindex,weighted_complexSeed_factor,
      weighted_kernel_sum_split _ (norm_inClass N g h) s hs,scaledPoint_im,cuspPoint_im,
      max_eq_right hy,Real.mul_rpow (Nat.cast_nonneg _) hy0.le,Complex.ofReal_mul]
    dsimp only [F,W,Y,Z,k]
    field_simp [hpow] <;> ring
  have H := ((ht.const_add (W zeroFirstPlus+W zeroFirstMinus)).const_mul F).congr' he.symm
  rw [nativeFrameOrbit_eq_iff]
  have hr := class_zero_rows N g h
  by_cases hclass : rowClass N (matrixRow h⁻¹) = rowClass N (matrixRow g⁻¹)
  · have hw : cuspWidth N h = cuspWidth N g := by
      obtain ⟨γ,k',hk'⟩ := (frames_same_class_iff N g h).mp hclass.symm
      rw [hk',cuspWidth_right_translation,cuspWidth_left_mul N _ _ γ.property]
    have hF : F*(W zeroFirstPlus+W zeroFirstMinus+0) = 1 := by
      dsimp only [F,W,k]
      rw [hr.1,hr.2,if_pos hclass,hw]
      linear_combination width_real_power N hN g s
    simpa only [if_pos hclass,hF] using H
  · simpa only [if_neg hclass,W,hr.1,hr.2,add_zero,mul_zero] using H

/-- A single physical limit recovers any coefficient of a genuine finite
parabolic combination. The observing frame can be arbitrary. -/
theorem parabolic_combination_incoming (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : CuspRowClass N → ℂ) (g : SL(2,ℤ)) (s : ℝ) (hs : 1 < s) (x : ℝ) :
    Tendsto (fun y : ℝ => (∑ b : CuspRowClass N, u b*cuspEisenstein N (classFrame b) (s : ℂ)
        (normalizedScaling N hN g • cuspPoint x y)) / ((y^s : ℝ) : ℂ))
      atTop (𝓝 (u (rowClass N (matrixRow g⁻¹)))) := by
  classical
  have H := tendsto_finsetSum (s := (Finset.univ : Finset (CuspRowClass N)))
    (fun b _ => (parabolic_incoming N hN (classFrame b) g s hs x).const_mul (u b))
  have hdiag (b : CuspRowClass N) : nativeFrameOrbit N g = nativeFrameOrbit N (classFrame b) ↔
      rowClass N (matrixRow g⁻¹) = b := by
    rw [nativeFrameOrbit_eq_iff,classFrame_row,show rowClass N b.out = b from Quotient.out_eq b]
  simp only [hdiag,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true] at H
  simpa only [Finset.sum_div,mul_div_assoc] using H

/-- In particular the native functions are independent on the real
initial half-plane. This uses the functions at every physical point. -/
theorem native_parabolic_independent (N : ℕ) [NeZero N] (hN : 0 < N)
    (s : ℝ) (hs : 1 < s) (u : CuspRowClass N → ℂ)
    (hzero : ∀ z : ℍ, ∑ b : CuspRowClass N, u b*cuspEisenstein N (classFrame b) (s : ℂ) z = 0) :
    ∀ a, u a = 0 := by
  intro a
  have H := parabolic_combination_incoming N hN u (classFrame a) s hs 0
  simp only [hzero,zero_div,classFrame_row,rowClass,Quotient.out_eq] at H
  exact tendsto_nhds_unique H tendsto_const_nhds

/-- The displayed coefficients of the original oldform are the physical
incoming amplitudes at every normalized integral observing frame. -/
theorem oldform_incoming {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (B : ℕ+)
    (N : ℕ) [NeZero N] (hN : 0 < N) (hle : q^2*(B : ℕ) ∣ N)
    (s : ℝ) (hs : 1 < s) (x : ℝ) (g : SL(2,ℤ)) :
    Tendsto (fun y : ℝ => characterLatticeOldform hq χ B (s : ℂ)
        (normalizedScaling N hN g • cuspPoint x y) / ((y^s : ℝ) : ℂ))
      atTop (𝓝 (cuspCoefficient hq χ B N g (s : ℂ))) := by
  let a := rowClass N (matrixRow g⁻¹)
  let f := classFrame a
  have he : rowClass N (matrixRow g⁻¹) = rowClass N (matrixRow f⁻¹) := by
    change a = rowClass N (matrixRow (classFrame a)⁻¹)
    rw [classFrame_row]
    exact (Quotient.out_eq a).symm
  obtain ⟨γ,k,hk⟩ := (frames_same_class_iff N g f).mp he
  have hw : cuspWidth N f = cuspWidth N g := by
    rw [hk,cuspWidth_right_translation,cuspWidth_left_mul N _ _ γ.property]
  obtain ⟨δ,hδ⟩ := Quotient.exact he
  have hx : cuspCoefficient hq χ B N f (s : ℂ) = cuspCoefficient hq χ B N g (s : ℂ) := by
    simp only [cuspCoefficient,hw,← hδ,
      ActualCharacterCuspRowReduction20261110.rowWeight_invariant hq χ B N hle]
  have H := parabolic_combination_incoming N hN
    (fun b => cuspCoefficient hq χ B N (classFrame b) (s : ℂ)) g s hs x
  rw [← hx]
  simpa only [← actual_oldform_eq_finite_cusp_sum hq χ B N hle (s : ℂ) (by simpa using hs)] using H

end
end ImbalancedChen.Part3.ActualParabolicIncoming20261110
