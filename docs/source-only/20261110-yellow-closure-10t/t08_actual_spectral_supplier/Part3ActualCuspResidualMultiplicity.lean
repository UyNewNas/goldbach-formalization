import ImbalancedChen.Part3ActualNativeResidualChannel
import ImbalancedChen.Part3Gamma0ActualConstantMode
import Mathlib.Data.Int.ModEq

/-! Counting the width multiplicity of the actual native cusp frames in
the full modular cosets calibrates the residue of the primitive level-one
oldform against every normalized parabolic at level N. -/
namespace ImbalancedChen.Part3.ActualCuspResidualMultiplicity20261110

noncomputable section
open Set Filter Topology Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualCharacterCuspExpansion20261110 ActualCharacterCuspRowReduction20261110
open ActualReflectedCuspSpans20261110 ActualNativeResidualChannel20261110
open ActualResidualCurveAtOne20261110 ActualCompletedCurveMeans20261110
open ActualYoungCriticalCusps20261110 ActualYoungCriticalD20261110
open Gamma0GeneralCuspWidth20261025a Gamma0ParabolicBottomRow20261025a
open Gamma0FiniteMeasureCarrier20261024z OriginalCharacterPairDilation20261102s
open Gamma0DegeneracyMapSourceOnly CharacterEisensteinRowAction

private def cell {N : ℕ} [NeZero N] (a : CuspRowClass N) (k : ℤ) : gamma0Classes N :=
  QuotientGroup.mk (ModularGroup.T^k*(classFrame a)⁻¹)

private theorem class_congr (N : ℕ) {A B : SL(2,ℤ)}
    (h : (QuotientGroup.mk A : gamma0Classes N) = QuotientGroup.mk B) :
    rowClass N (matrixRow A) = rowClass N (matrixRow B) := by
  let γ : CongruenceSubgroup.Gamma0 N := ⟨A⁻¹*B,QuotientGroup.eq.mp h⟩
  apply Quotient.sound
  exact ⟨γ,by rw [← matrixRow_mul,show A*(γ : SL(2,ℤ)) = B by dsimp [γ]; group]⟩

private theorem row_cell {N : ℕ} (a : CuspRowClass N) (k : ℤ) :
    rowClass N (matrixRow (ModularGroup.T^k*(classFrame a)⁻¹)) = a := by
  have he : matrixRow (ModularGroup.T^k*(classFrame a)⁻¹) = matrixRow (classFrame a)⁻¹ :=
    Subtype.ext (bottomRow_left_translation k _)
  rw [he,classFrame_row]
  exact Quotient.out_eq a

private theorem cell_eq_iff {N : ℕ} [NeZero N] (a : CuspRowClass N) (k l : ℤ) :
    cell a k = cell a l ↔ Int.ModEq (cuspWidth N (classFrame a) : ℤ) k l := by
  have HE : (ModularGroup.T^k*(classFrame a)⁻¹)⁻¹*(ModularGroup.T^l*(classFrame a)⁻¹) =
      classFrame a*ModularGroup.T^(l-k)*(classFrame a)⁻¹ := by
    rw [show l-k = -k+l by ring,zpow_add,zpow_neg]
    group
  rw [cell,cell,QuotientGroup.eq,HE,conjugated_translation_mem_iff_width_dvd N (NeZero.pos N),Int.modEq_iff_dvd]

def widthCosets (N : ℕ) [NeZero N] :
    ((a : CuspRowClass N) × Fin (cuspWidth N (classFrame a))) ≃ gamma0Classes N := by
  classical
  let F := fun v : (a : CuspRowClass N) × Fin (cuspWidth N (classFrame a)) => cell v.1 (v.2.val : ℤ)
  refine Equiv.ofBijective F ⟨?_,?_⟩
  · rintro ⟨a,k⟩ ⟨b,l⟩ he
    change cell a (k.val : ℤ) = cell b (l.val : ℤ) at he
    have hab : a = b := (row_cell a _).symm.trans ((class_congr N he).trans (row_cell b _))
    subst b
    have hkl := (cell_eq_iff a k.val l.val).mp he
    change ((k.val : ℤ)%(cuspWidth N (classFrame a) : ℤ)) =
      (l.val : ℤ)%(cuspWidth N (classFrame a) : ℤ) at hkl
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast k.isLt),
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast l.isLt)] at hkl
    have e : k = l := Fin.ext (by exact_mod_cast hkl)
    rw [e]
  · intro x
    let A : SL(2,ℤ) := Quotient.out x
    let a := rowClass N (matrixRow A)
    obtain ⟨γ,hγ⟩ := (classFrame_fiber a (matrixRow A)).mpr rfl
    obtain ⟨k,hk⟩ := (bottomRow_eq_iff_left_translation ((classFrame a)⁻¹*(γ : SL(2,ℤ))) A).mp hγ.symm
    let w : ℤ := cuspWidth N (classFrame a)
    have hw : 0 < w := by exact_mod_cast cuspWidth_pos N (NeZero.pos N) (classFrame a)
    let j := (k%w).toNat
    have hj : (j : ℤ) = k%w := Int.toNat_of_nonneg (Int.emod_nonneg _ hw.ne')
    have hjw : j < cuspWidth N (classFrame a) := by
      have HH := Int.emod_lt_of_pos k hw
      rw [← hj] at HH
      exact_mod_cast HH
    refine ⟨⟨a,⟨j,hjw⟩⟩,?_⟩
    change cell a (j : ℤ) = x
    have hjk : cell a (j : ℤ) = cell a k := (cell_eq_iff a _ _).mpr (by
      rw [hj]
      exact Int.mod_modEq k w)
    rw [hjk]
    apply Eq.trans _ (Quotient.out_eq' x)
    change (QuotientGroup.mk (ModularGroup.T^k*(classFrame a)⁻¹) : gamma0Classes N) = QuotientGroup.mk A
    apply QuotientGroup.eq.mpr
    rw [hk,show (ModularGroup.T^k*(classFrame a)⁻¹)⁻¹*
      (ModularGroup.T^k*((classFrame a)⁻¹*(γ : SL(2,ℤ)))) = (γ : SL(2,ℤ)) by group]
    exact γ.property

/-- Exact sum using each physical width once on the actual cusp quotient. -/
theorem width_sum_eq_index (N : ℕ) [NeZero N] :
    ∑ a : CuspRowClass N, cuspWidth N (classFrame a) = (CongruenceSubgroup.Gamma0 N).index := by
  letI : Fintype (gamma0Classes N) := (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex
  simpa only [Fintype.card_sigma,Fintype.card_fin,Subgroup.index,Nat.card_eq_fintype_card] using
    Fintype.card_congr (widthCosets N)

private theorem coefficient_at_one (N : ℕ) [NeZero N] (g : SL(2,ℤ)) :
    cuspCoefficient (q := 1) zero_lt_one (1 : DirichletCharacter ℂ 1) (1 : ℕ+) N g 1 =
      (cuspWidth N g : ℂ) := by
  have hχ (k : ZMod 1) : (1 : DirichletCharacter ℂ 1) k = 1 := by rw [Subsingleton.elim k 1,map_one]
  have hw : 0 < (cuspWidth N g : ℝ) := by exact_mod_cast cuspWidth_pos N (NeZero.pos N) g
  rw [cuspCoefficient_explicit _ _ _ N (NeZero.pos N)]
  simp [Int.gcd_eq_natAbs,characterWeight,hχ,← Complex.ofReal_exp,Real.exp_log hw]

/-- The common ordinary residue is exactly 3/(π[SL₂(ℤ):Γ₀(N)]).
The calibration uses the original q=B=1 dilation and all genuine widths. -/
theorem native_residue_index (N : ℕ) [NeZero N] (a : NativeCusps N) :
    nativeResidue N a = 3/((Real.pi : ℂ)*((CongruenceSubgroup.Gamma0 N).index : ℂ)) := by
  let z := (UpperHalfPlane.I : ℍ)
  let χ := (1 : DirichletCharacter ℂ 1)
  let C := fun k : CuspRowClass N => cuspCoefficient (q := 1) zero_lt_one χ (1 : ℕ+) N (classFrame k)
  have hc (k : CuspRowClass N) : Continuous (C k) := by
    unfold C cuspCoefficient rowWeight
    fun_prop
  have H := tendsto_finsetSum Finset.univ (fun k (_ : k ∈ (Finset.univ : Finset (CuspRowClass N))) =>
    ((hc k).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul (native_point_residue N (nativeCuspEquiv N k) z))
  have hseed : Tendsto (fun s : ℂ => (s-1)*ordinary χ s (degeneracyDiagonal 1 zero_lt_one • z))
      (𝓝[≠] 1) (𝓝 (3/(Real.pi : ℂ))) := by
    simpa [curveMean,dilationResidue] using ordinary_curve_residue χ
      (fun _ => degeneracyDiagonal 1 zero_lt_one • z) continuous_const
  have hnear : {s : ℂ | (1/2 : ℝ) < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have He : 3/(Real.pi : ℂ) =
      ∑ k : CuspRowClass N,C k 1*nativeResidue N (nativeCuspEquiv N k) := by
    apply tendsto_nhds_unique_of_eventuallyEq hseed H
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnear,self_mem_nhdsWithin] with w hw (h₁ : w ≠ 1)
    rw [continued_forward_dilation χ DirichletCharacter.isPrimitive_one_level_one 1 N (by simp) w hw.le h₁,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold C
    ring
  have hv : ∀ k : CuspRowClass N, C k 1 = (cuspWidth N (classFrame k) : ℂ) :=
    fun k => coefficient_at_one N (classFrame k)
  simp_rw [hv,fun k : CuspRowClass N => equal_cusp_residues N (nativeCuspEquiv N k) a] at He
  rw [← Finset.sum_mul,← Nat.cast_sum,width_sum_eq_index] at He
  have hi : ((CongruenceSubgroup.Gamma0 N).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (CongruenceSubgroup.Gamma0 N).index_ne_zero_of_finite
  have hπ := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hπ,hi] at He ⊢
  linear_combination -He

end
end ImbalancedChen.Part3.ActualCuspResidualMultiplicity20261110
