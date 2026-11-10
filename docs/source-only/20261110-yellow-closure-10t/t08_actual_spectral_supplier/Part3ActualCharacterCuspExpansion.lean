import ImbalancedChen.Part3ActualCharacterCuspRowReduction
import ImbalancedChen.Part3NativeAllCuspFrameCovariance
import ImbalancedChen.Part3ActualCharacterCriticalFamily

/-! The oldform-to-cusp direction of Young's inversion at weight zero and
trivial nebentypus. The finite indices are exactly the disjoint original
allowed-row families. Each summand is the existing normalized parabolic
Eisenstein function with its actual cusp width. -/

namespace ImbalancedChen.Part3.ActualCharacterCuspExpansion20261110

noncomputable section
open Complex Matrix Matrix.SpecialLinearGroup EisensteinSeries UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators
open PrimitiveEisensteinParameterAnalytic PrimitiveRealEisensteinAutomorphy
open PrimitiveEisensteinParameterAutomorphy CharacterEisensteinRowAction
open ActualCharacterCuspRowReduction20261110 OriginalCharacterPairDilation20261102s
open Gamma0ParabolicBottomRow20261025a Gamma0GeneralCuspWidth20261025a
open Gamma0FiniteMeasureCarrier20261024z NativeCuspAllowedRowRightAction20261026b
open NativeAllCuspEisenstein20261026b ActualCharacterCriticalFamily20261110
open Gamma0DegeneracyMapSourceOnly

private theorem pair_comp (g h : SL(2,ℤ)) (v : PrimitivePair) :
    primitivePairEquiv h (primitivePairEquiv g v) = primitivePairEquiv (g*h) v := by
  apply Subtype.ext
  simp only [primitivePairEquiv_value,Matrix.vecMul_vecMul,coe_mul]

private theorem pair_one (v : PrimitivePair) : primitivePairEquiv (1 : SL(2,ℤ)) v = v := by
  apply Subtype.ext
  simp [primitivePairEquiv_value]

/-- Literal right action on signed primitive rows. Since the central
negative identity lies in the group, the quotient counts each cusp once. -/
def rightRowSetoid (N : ℕ) : Setoid PrimitivePair where
  r v w := ∃ γ : CongruenceSubgroup.Gamma0 N, primitivePairEquiv (γ : SL(2,ℤ)) v = w
  iseqv := {
    refl := fun v => ⟨1,pair_one v⟩
    symm := by
      rintro v w ⟨γ,rfl⟩
      exact ⟨γ⁻¹,by simp only [Subgroup.coe_inv,pair_comp,mul_inv_cancel,pair_one]⟩
    trans := by
      rintro v w u ⟨γ,rfl⟩ ⟨δ,rfl⟩
      exact ⟨γ*δ,by simp only [Subgroup.coe_mul,pair_comp]⟩ }

abbrev CuspRowClass (N : ℕ) := Quotient (rightRowSetoid N)

def rowClass (N : ℕ) (v : PrimitivePair) : CuspRowClass N := Quotient.mk _ v

def matrixRow (g : SL(2,ℤ)) : PrimitivePair :=
  ⟨bottomRow g,(mem_gammaSet_one _).mpr (bottomRow_bezout g)⟩

theorem matrixRow_mul (g h : SL(2,ℤ)) :
    matrixRow (g*h) = primitivePairEquiv h (matrixRow g) := by
  apply Subtype.ext
  rw [primitivePairEquiv_value]
  exact bottomRow_mul_right g h

private theorem exists_rowFrame (v : PrimitivePair) :
    ∃ g : SL(2,ℤ), matrixRow g⁻¹ = v := by
  obtain ⟨h,hC,hD⟩ := ((mem_gammaSet_one v.1).mp v.property).exists_SL2_row 1
  refine ⟨h⁻¹,?_⟩
  rw [inv_inv]
  apply Subtype.ext
  funext j
  fin_cases j
  · exact hC
  · exact hD

/-- Every integral cusp frame belongs to its own bottom-row orbit;
the original allowed-row predicate is precisely this quotient fiber. -/
theorem allowed_iff_same_class (N : ℕ) (g : SL(2,ℤ)) (v : PrimitivePair) :
    allowedRow N g v ↔ rowClass N v = rowClass N (matrixRow g⁻¹) := by
  constructor
  · rintro ⟨γ,hγ⟩
    apply Eq.symm
    apply Quotient.sound
    refine ⟨γ,?_⟩
    rw [← matrixRow_mul]
    exact Subtype.ext hγ
  · intro h
    obtain ⟨γ,hγ⟩ := Quotient.exact h.symm
    refine ⟨γ,?_⟩
    simpa only [← matrixRow_mul] using congrArg Subtype.val hγ

/-- Equality of indices is exactly equivalence of the actual cusp frames
under the original subgroup on the left and an integral translation on the
right. The subgroup absorbs the central sign. -/
theorem frames_same_class_iff (N : ℕ) (g h : SL(2,ℤ)) :
    rowClass N (matrixRow g⁻¹) = rowClass N (matrixRow h⁻¹) ↔
      ∃ γ : CongruenceSubgroup.Gamma0 N, ∃ k : ℤ,
        h = (γ : SL(2,ℤ))*g*ModularGroup.T^k := by
  constructor
  · intro he
    obtain ⟨δ,hδ⟩ := (allowed_iff_same_class N g (matrixRow h⁻¹)).mpr he.symm
    obtain ⟨j,hj⟩ := (bottomRow_eq_iff_left_translation (g⁻¹*(δ : SL(2,ℤ))) h⁻¹).mp hδ.symm
    refine ⟨δ⁻¹,-j,?_⟩
    simpa only [inv_inv,mul_inv_rev,Subgroup.coe_inv,zpow_neg,mul_assoc] using
      congrArg Inv.inv hj
  · rintro ⟨γ,k,rfl⟩
    apply Eq.symm
    apply (allowed_iff_same_class N g _).mp
    refine ⟨γ⁻¹,?_⟩
    change bottomRow (g⁻¹*((γ⁻¹ : CongruenceSubgroup.Gamma0 N) : SL(2,ℤ))) =
      bottomRow (((γ : SL(2,ℤ))*g*ModularGroup.T^k)⁻¹)
    rw [Subgroup.coe_inv,mul_inv_rev,mul_inv_rev,← zpow_neg,bottomRow_left_translation]

private def classFromCoset (N : ℕ) [NeZero N] (x : gamma0Classes N) : CuspRowClass N :=
  rowClass N (matrixRow (Quotient.out x))

private theorem classFromCoset_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (classFromCoset N) := by
  intro x
  obtain ⟨g,hg⟩ := exists_rowFrame x.out
  let r := g⁻¹
  let a : gamma0Classes N := QuotientGroup.mk r
  have hq : (QuotientGroup.mk r : gamma0Classes N) = QuotientGroup.mk a.out :=
    (Quotient.out_eq' a).symm
  let γ : CongruenceSubgroup.Gamma0 N := ⟨r⁻¹*a.out,QuotientGroup.eq.mp hq⟩
  have H : r*(γ : SL(2,ℤ)) = a.out := by dsimp [γ]; group
  have hrow : rowClass N (matrixRow r) = classFromCoset N a := by
    apply Quotient.sound
    exact ⟨γ,by rw [← matrixRow_mul,H]⟩
  refine ⟨a,hrow.symm.trans ?_⟩
  change rowClass N (matrixRow g⁻¹) = x
  rw [hg]
  exact Quotient.out_eq x

private instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

noncomputable instance (N : ℕ) [NeZero N] : Fintype (CuspRowClass N) := by
  letI : Finite (CuspRowClass N) := Finite.of_surjective _ (classFromCoset_surjective N)
  exact Fintype.ofFinite _

def classFrame {N : ℕ} (x : CuspRowClass N) : SL(2,ℤ) :=
  Classical.choose (exists_rowFrame x.out)

theorem classFrame_row {N : ℕ} (x : CuspRowClass N) : matrixRow (classFrame x)⁻¹ = x.out :=
  Classical.choose_spec (exists_rowFrame x.out)

theorem classFrame_fiber {N : ℕ} (x : CuspRowClass N) (v : PrimitivePair) :
    allowedRow N (classFrame x) v ↔ rowClass N v = x := by
  rw [allowed_iff_same_class,classFrame_row,show rowClass N x.out = x from Quotient.out_eq x]

abbrev NativeCusps (N : ℕ) :=
  CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))

def nativeFrameOrbit (N : ℕ) [NeZero N] (g : SL(2,ℤ)) : NativeCusps N :=
  Quotient.mk'' (⟨mapGL ℝ g • (∞ : OnePoint ℝ),
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr (isCusp_SL2Z_iff'.mpr ⟨g,rfl⟩)⟩ :
      cuspsSubMulAction (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))

private theorem translates_infty (k : ℤ) : mapGL ℝ (ModularGroup.T^k) • (∞ : OnePoint ℝ) = ∞ := by
  simp [OnePoint.smul_infty_eq_self_iff,ModularGroup.coe_T_zpow,mapGL_coe_matrix]

/-- The signed primitive-row quotient is identified with Mathlib's
original projective cusp orbit, for arbitrary composite positive level. -/
theorem nativeFrameOrbit_eq_iff (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) :
    nativeFrameOrbit N g = nativeFrameOrbit N h ↔
      rowClass N (matrixRow g⁻¹) = rowClass N (matrixRow h⁻¹) := by
  rw [frames_same_class_iff]
  constructor
  · intro he
    obtain ⟨δ,hδ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact he.symm)
    obtain ⟨a,ha,ham⟩ := δ.property
    let γ : CongruenceSubgroup.Gamma0 N := ⟨a,ha⟩
    have hc : mapGL ℝ a • (mapGL ℝ g • (∞ : OnePoint ℝ)) = mapGL ℝ h • ∞ := by
      have H := congrArg (fun x : cuspsSubMulAction
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) => (x : OnePoint ℝ)) hδ
      change (δ : GL (Fin 2) ℝ) • (mapGL ℝ g • ∞) = mapGL ℝ h • ∞ at H
      simpa only [ham] using H
    let A : SL(2,ℤ) := (a*g)⁻¹*h
    have hc' : mapGL ℝ (a*g) • (∞ : OnePoint ℝ) = mapGL ℝ h • ∞ := by
      simpa only [map_mul,mul_smul] using hc
    have hfix : mapGL ℝ A • (∞ : OnePoint ℝ) = ∞ := by
      change mapGL ℝ ((a*g)⁻¹*h) • (∞ : OnePoint ℝ) = ∞
      rw [map_mul,map_inv,mul_smul,← hc',inv_smul_smul]
    have hzero : A 1 0 = 0 := by
      simpa [OnePoint.smul_infty_eq_self_iff,mapGL_coe_matrix] using hfix
    obtain ⟨k,hk|hk⟩ := (lowerLeft_zero_iff_signed_translation A).mp hzero
    · refine ⟨γ,k,?_⟩
      change h = a*g*ModularGroup.T^k
      rw [← hk]
      dsimp [A]
      group
    · let δ' : CongruenceSubgroup.Gamma0 N := ⟨-a,
        (Gamma0ActualCuspsSourceOnly.gamma0_mem_iff_level_dvd_c N _).mpr
          (by simpa using dvd_neg.mpr ((Gamma0ActualCuspsSourceOnly.gamma0_mem_iff_level_dvd_c N _).mp ha))⟩
      refine ⟨δ',k,?_⟩
      have H : h = (a*g)*A := by dsimp [A]; group
      change h = (-a)*g*ModularGroup.T^k
      simpa only [hk,mul_neg,neg_mul] using H
  · rintro ⟨γ,k,rfl⟩
    apply Eq.symm
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨mapGL ℝ (γ : SL(2,ℤ)),⟨(γ : SL(2,ℤ)),γ.property,rfl⟩⟩,?_⟩
    apply Subtype.ext
    change mapGL ℝ (γ : SL(2,ℤ)) • (mapGL ℝ g • ∞) =
      mapGL ℝ ((γ : SL(2,ℤ))*g*ModularGroup.T^k) • ∞
    simp only [map_mul,mul_smul,translates_infty]

def nativeCuspEquiv (N : ℕ) [NeZero N] : CuspRowClass N ≃ NativeCusps N := by
  apply Equiv.ofBijective (fun x => nativeFrameOrbit N (classFrame x))
  constructor
  · intro x y h
    have H := (nativeFrameOrbit_eq_iff N _ _).mp h
    simpa only [classFrame_row,rowClass,Quotient.out_eq] using H
  · intro x
    refine Quotient.inductionOn x ?_
    intro c
    obtain ⟨g,hg⟩ := isCusp_SL2Z_iff'.mp
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp c.property)
    refine ⟨rowClass N (matrixRow g⁻¹),?_⟩
    have hc : Quotient.mk'' c = nativeFrameOrbit N g := by
      apply congrArg (fun z : cuspsSubMulAction
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) => Quotient.mk'' z)
      exact Subtype.ext hg
    rw [hc,nativeFrameOrbit_eq_iff,classFrame_row]
    exact Quotient.out_eq _

private def fiberEquiv {N : ℕ} (x : CuspRowClass N) :
    {v : PrimitivePair // rowClass N v = x} ≃ AllowedPair N (classFrame x) where
  toFun v := ⟨v.1,(classFrame_fiber x v.1).mpr v.2⟩
  invFun v := ⟨v.1,(classFrame_fiber x v.1).mp v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def cuspCoefficient {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (B : ℕ+)
    (N : ℕ) (g : SL(2,ℤ)) (s : ℂ) : ℂ :=
  rowWeight χ (q*(B : ℕ)) (Nat.mul_pos hq B.pos) (matrixRow g⁻¹) s *
    Complex.exp (s*(Real.log (cuspWidth N g : ℝ) : ℂ))

/-- The factor w^s converts the existing (1/w)^s-normalized parabolic seed.
At the actual first column (a,c), the inverse row is (-c,a). Its gcd and
character evaluations use signed integer quotients, including the axes. -/
theorem cuspCoefficient_explicit {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (N : ℕ) (hN : 0 < N) (g : SL(2,ℤ)) (s : ℂ) :
    let p := q*(B : ℕ)
    let h := (g 1 0).gcd (p : ℤ)
    cuspCoefficient hq χ B N g s =
      characterWeight χ (-(g 1 0)/(h : ℤ)) ((p : ℤ)*g 0 0/(h : ℤ)) *
        Complex.exp (s*(Real.log (((h : ℝ)^2/(p : ℝ))*(cuspWidth N g : ℝ)) : ℂ)) := by
  let p := q*(B : ℕ)
  let v := matrixRow g⁻¹
  have hp : 0 < p := Nat.mul_pos hq B.pos
  have hC : v.1 0 = -(g 1 0) := by simp [v,matrixRow,bottomRow,SL2_inv_expl]
  have hD : v.1 1 = g 0 0 := by simp [v,matrixRow,bottomRow,SL2_inv_expl]
  have hg : backContent p v = (g 1 0).gcd (p : ℤ) := by
    simp only [backContent_eq_gcd,hC,Int.gcd_eq_natAbs,Int.natAbs_neg]
  have hk : 0 < backContent p v := content_pos Nat.zero_lt_one hp _
  have hkZ : (backContent p v : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have h₀ : (backPair p hp v).1 0 = -(g 1 0)/(backContent p v : ℤ) := by
    rw [← hC,← (backPair_coordinates p hp v).1,Int.mul_ediv_cancel_left _ hkZ]
  have h₁ : (backPair p hp v).1 1 = (p : ℤ)*g 0 0/(backContent p v : ℤ) := by
    rw [← hD,← (backPair_coordinates p hp v).2,Int.mul_ediv_cancel_left _ hkZ]
  have hr : 0 < rowScale p v := div_pos (sq_pos_of_pos (by exact_mod_cast hk)) (by exact_mod_cast hp)
  have hw : 0 < (cuspWidth N g : ℝ) := by exact_mod_cast cuspWidth_pos N hN g
  change primitiveWeight χ (backPair p hp v)*Complex.exp (s*(Real.log (rowScale p v) : ℂ))*
      Complex.exp (s*(Real.log (cuspWidth N g : ℝ) : ℂ)) = _
  rw [mul_assoc,← Complex.exp_add,← mul_add,← Complex.ofReal_add,← Real.log_mul hr.ne' hw.ne',
    primitiveWeight,h₀,h₁,rowScale,hg]

private theorem class_tsum {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (B : ℕ+)
    (N : ℕ) (hN : 0 < N) (hle : q^2*(B : ℕ) ∣ N)
    (s : ℂ) (hs : 1 < s.re) (z : ℍ) (x : CuspRowClass N) :
    (1/2 : ℂ) * (∑' v : {v : PrimitivePair // rowClass N v = x},
      rowWeight χ (q*(B : ℕ)) (Nat.mul_pos hq B.pos) v.1 s * complexSeed z v.1 s) =
      cuspCoefficient hq χ B N (classFrame x) s * cuspEisenstein N (classFrame x) s z := by
  let p := q*(B : ℕ)
  have hp : 0 < p := Nat.mul_pos hq B.pos
  let g := classFrame x
  have hg (v : AllowedPair N g) : rowWeight χ p hp v.1 s =
      rowWeight χ p hp (matrixRow g⁻¹) s := by
    obtain ⟨γ,hγ⟩ := v.2
    have hpair : primitivePairEquiv (γ : SL(2,ℤ)) (matrixRow g⁻¹) = v.1 := by
      rw [← matrixRow_mul]
      exact Subtype.ext hγ
    rw [← hpair,rowWeight_invariant hq χ B N hle]
  have hf : (∑' v : {v : PrimitivePair // rowClass N v = x},
      rowWeight χ p hp v.1 s*complexSeed z v.1 s) =
      rowWeight χ p hp (matrixRow g⁻¹) s*∑' v : AllowedPair N g, complexSeed z v.1 s := by
    calc
      _ = ∑' v : AllowedPair N g, rowWeight χ p hp v.1 s*complexSeed z v.1 s :=
        (fiberEquiv x).tsum_eq _
      _ = _ := by simp_rw [hg]; rw [tsum_mul_left]
  have hw : Complex.exp (s*(Real.log (cuspWidth N g : ℝ) : ℂ))*widthFactor N g s = 1 := by
    rw [widthFactor,← Complex.exp_add]
    simp
  change (1/2 : ℂ)*_ = cuspCoefficient hq χ B N g s*cuspEisenstein N g s z
  rw [hf,cuspEisenstein_eq_widthFactor_mul N hN g,cuspCoefficient]
  linear_combination -(1/2 : ℂ)*rowWeight χ p hp (matrixRow g⁻¹) s*
    (∑' v : AllowedPair N g,complexSeed z v.1 s)*hw

/-- Exact finite expansion of every legal genuine oldform into the
normalized, pairwise inequivalent parabolic functions at the same level.
No scattering coefficient, additive completeness or formal norm is assumed. -/
theorem actual_oldform_eq_finite_cusp_sum {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (N : ℕ) [NeZero N] (hle : q^2*(B : ℕ) ∣ N)
    (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    characterLatticeOldform hq χ B s z =
      ∑ x : CuspRowClass N, cuspCoefficient hq χ B N (classFrame x) s *
        cuspEisenstein N (classFrame x) s z := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hf := ((original_row_summable hq χ B s hs z).hasSum.tsum_fiberwise (rowClass N)).tsum_eq
  rw [original_row_expansion,← hf,tsum_fintype,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => class_tsum hq χ B N hN hle s hs z x)

/-- The index in this equality is the existing native cusp quotient
itself. Its finiteness comes from the genuine arithmetic subgroup. -/
theorem actual_oldform_eq_native_cusps {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (N : ℕ) [NeZero N] (hle : q^2*(B : ℕ) ∣ N)
    (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    characterLatticeOldform hq χ B s z =
      ∑' a : NativeCusps N, cuspCoefficient hq χ B N (classFrame ((nativeCuspEquiv N).symm a)) s *
        cuspEisenstein N (classFrame ((nativeCuspEquiv N).symm a)) s z := by
  rw [(nativeCuspEquiv N).symm.tsum_eq (fun x => cuspCoefficient hq χ B N (classFrame x) s *
    cuspEisenstein N (classFrame x) s z),tsum_fintype]
  exact actual_oldform_eq_finite_cusp_sum hq χ B N hle s hs z

/-- The same finite cusp sum has an explicitly constructed continuation
in the physical point z. This identifies the combination, not a termwise
continuation of each individual cusp channel. -/
theorem finite_cusp_sum_continues {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (B : ℕ+) (N : ℕ) [NeZero N]
    (hle : q^2*(B : ℕ) ∣ N) (z : ℍ) :
    (∀ s : ℂ, 1 < s.re →
      primitiveFamily χ s (degeneracyDiagonal B B.pos • z) =
        ∑ x : CuspRowClass N, cuspCoefficient hq χ B N (classFrame x) s *
          cuspEisenstein N (classFrame x) s z) ∧
    (∀ s : ℂ, 1/2 ≤ s.re →
      DifferentiableAt ℂ (fun w => primitiveFamily χ w (degeneracyDiagonal B B.pos • z)) s) := by
  constructor
  · intro s hs
    rw [primitiveFamily_initial hq h1 χ hχ s hs]
    exact actual_oldform_eq_finite_cusp_sum hq χ B N hle s hs z
  · exact primitiveFamily_differentiableAt χ _

end
end ImbalancedChen.Part3.ActualCharacterCuspExpansion20261110
