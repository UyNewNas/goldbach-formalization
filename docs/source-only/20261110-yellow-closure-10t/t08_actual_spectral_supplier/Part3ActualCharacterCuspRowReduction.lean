import ImbalancedChen.Part3ActualCharacterLatticeCompletion
import ImbalancedChen.Part3NativeCuspAllowedRowRightAction

/-! Primitive reduction of the actual dilated character Eisenstein lattice.
The inverse reduction of (C,pD), p=qB, gives the exact signed character
and the real scale of each genuine cusp row. The integral degeneracy
conjugate proves that these data are constant on its original level orbit. -/

namespace ImbalancedChen.Part3.ActualCharacterCuspRowReduction20261110

noncomputable section
open Complex Matrix Matrix.SpecialLinearGroup EisensteinSeries UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators
open PrimitiveEisensteinParameterAnalytic PrimitiveRealEisensteinAutomorphy
open PrimitiveEisensteinParameterAutomorphy CharacterEisensteinRowAction
open CharacterEisensteinSeries Gamma0DegeneracyMapSourceOnly Gamma0ActualCuspsSourceOnly
open OriginalCharacterPairDilation20261102s

private abbrev Vec := Fin 2 → ℤ

def scaleRow (a b : ℕ) (v : Vec) : Vec := ![(a : ℤ)*v 0, (b : ℤ)*v 1]

def content (a b : ℕ) (v : PrimitivePair) : ℕ := finGcdMap (scaleRow a b v.1)

theorem content_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (v : PrimitivePair) :
    0 < content a b v := by
  apply Nat.pos_of_ne_zero
  intro h
  obtain ⟨h₀,h₁⟩ := Int.gcd_eq_zero_iff.mp h
  have ha' : (a : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hb' : (b : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hC : v.1 0 = 0 := (mul_eq_zero.mp (show (a : ℤ)*v.1 0 = 0 from h₀)).resolve_left ha'
  have hD : v.1 1 = 0 := (mul_eq_zero.mp (show (b : ℤ)*v.1 1 = 0 from h₁)).resolve_left hb'
  have hv := (gammaSet_one_mem_iff _ _).mp v.property
  simp [hC,hD] at hv

def reduced {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (v : PrimitivePair) : PrimitivePair := by
  let k := content a b v
  letI : NeZero k := ⟨(content_pos ha hb v).ne'⟩
  exact gammaSetDivGcdEquiv k ⟨scaleRow a b v.1,(gammaSet_one_mem_iff _ _).mpr rfl⟩

theorem recover {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (v : PrimitivePair) :
    scaleRow a b v.1 = content a b v • (reduced ha hb v).1 := by
  exact gammaSet_eq_gcd_mul_divIntMap
    ((gammaSet_one_mem_iff (content a b v) (scaleRow a b v.1)).mpr rfl)

private theorem primitive_factor_unique {k l : ℕ} (hk : 0 < k) (v w : PrimitivePair)
    (h : k • v.1 = l • w.1) : k = l ∧ v = w := by
  have hcontent (j : ℕ) (u : PrimitivePair) : finGcdMap (j • u.1) = j := by
    simpa only [natCast_zsmul,Int.natAbs_natCast,mul_one] using
      (finGcdMap_smul (j : ℤ) ((gammaSet_one_mem_iff _ _).mp u.property))
  have hkl : k = l := by simpa only [hcontent] using congrArg finGcdMap h
  subst l
  refine ⟨rfl,Subtype.ext (funext fun i => ?_)⟩
  have hi : (k : ℤ)*v.1 i = (k : ℤ)*w.1 i := by
    simpa [Pi.smul_apply,nsmul_eq_mul] using congrFun h i
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hk.ne') hi

private theorem scale_scale (a b : ℕ) (v : Vec) :
    scaleRow b a (scaleRow a b v) = (a*b) • v := by
  ext i
  fin_cases i <;> simp [scaleRow,Pi.smul_apply,nsmul_eq_mul] <;> ring

private theorem scale_nsmul (a b k : ℕ) (v : Vec) :
    scaleRow a b (k • v) = k • scaleRow a b v := by
  ext i
  fin_cases i <;> simp [scaleRow,Pi.smul_apply,nsmul_eq_mul] <;> ring

private theorem reduced_flip {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (v : PrimitivePair) :
    reduced hb ha (reduced ha hb v) = v := by
  let u := reduced ha hb v
  have h : (content a b v * content b a u) • (reduced hb ha u).1 = (a*b) • v.1 := by
    rw [mul_smul,← recover hb ha,← scale_nsmul,← recover ha hb,scale_scale]
  exact (primitive_factor_unique (Nat.mul_pos (content_pos ha hb v) (content_pos hb ha u))
    (reduced hb ha u) v h).2

/-- Dilation of an oriented primitive line is genuinely bijective, including
both axes and the simultaneous sign. Its inverse uses the other diagonal. -/
def dilationEquiv (p : ℕ) (hp : 0 < p) : PrimitivePair ≃ PrimitivePair where
  toFun := reduced hp Nat.zero_lt_one
  invFun := reduced Nat.zero_lt_one hp
  left_inv := reduced_flip hp Nat.zero_lt_one
  right_inv := reduced_flip Nat.zero_lt_one hp

def backContent (p : ℕ) (v : PrimitivePair) : ℕ := content 1 p v

def backPair (p : ℕ) (hp : 0 < p) (v : PrimitivePair) : PrimitivePair :=
  (dilationEquiv p hp).symm v

theorem backPair_coordinates (p : ℕ) (hp : 0 < p) (v : PrimitivePair) :
    (backContent p v : ℤ)*(backPair p hp v).1 0 = v.1 0 ∧
    (backContent p v : ℤ)*(backPair p hp v).1 1 = (p : ℤ)*v.1 1 := by
  have h := recover Nat.zero_lt_one hp v
  constructor
  · simpa [backContent,backPair,dilationEquiv,scaleRow,Pi.smul_apply,nsmul_eq_mul] using
      (congrFun h 0).symm
  · simpa [backContent,backPair,dilationEquiv,scaleRow,Pi.smul_apply,nsmul_eq_mul] using
      (congrFun h 1).symm

theorem backContent_eq_gcd (p : ℕ) (v : PrimitivePair) :
    backContent p v = (v.1 0).gcd (p : ℤ) := by
  have hv := (mem_gammaSet_one v.1).mp v.property
  obtain ⟨u,w,hu⟩ := hv
  let g := backContent p v
  have hC : (g : ℤ) ∣ v.1 0 := by
    simpa [g,backContent,content,scaleRow] using
      (Int.gcd_dvd_left (v.1 0) ((p : ℤ)*v.1 1))
  have hD : (g : ℤ) ∣ (p : ℤ)*v.1 1 := by
    simpa [g,backContent,content,scaleRow] using
      (Int.gcd_dvd_right (v.1 0) ((p : ℤ)*v.1 1))
  have hp : (g : ℤ) ∣ (p : ℤ) := by
    have h := dvd_add (hC.mul_left ((p : ℤ)*u)) (hD.mul_left w)
    convert h using 1
    linear_combination -(p : ℤ)*hu
  apply Nat.dvd_antisymm
  · exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd hC hp)
  · change _ ∣ Int.gcd ((1 : ℤ)*v.1 0) ((p : ℤ)*v.1 1)
    rw [one_mul]
    exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd (Int.gcd_dvd_left _ _)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right _ _) _))

def rowScale (p : ℕ) (v : PrimitivePair) : ℝ := (backContent p v : ℝ)^2/(p : ℝ)

def rowWeight {q : ℕ} (χ : DirichletCharacter ℂ q) (p : ℕ) (hp : 0 < p)
    (v : PrimitivePair) (s : ℂ) : ℂ :=
  primitiveWeight χ (backPair p hp v) * Complex.exp (s*(Real.log (rowScale p v) : ℂ))

private theorem physical_base (p : ℕ) (hp : 0 < p) (v : PrimitivePair) (z : ℍ) :
    positiveBase (scaledPoint p hp z) (backPair p hp v) = rowScale p v * positiveBase z v := by
  let u := backPair p hp v
  let g := backContent p v
  have hg : 0 < (g : ℝ) := by exact_mod_cast content_pos Nat.zero_lt_one hp v
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have h₀ : (g : ℂ)*(u.1 0 : ℂ) = (v.1 0 : ℂ) := by
    exact_mod_cast (backPair_coordinates p hp v).1
  have h₁ : (g : ℂ)*(u.1 1 : ℂ) = (p : ℂ)*(v.1 1 : ℂ) := by
    exact_mod_cast (backPair_coordinates p hp v).2
  let A : ℂ := (u.1 0 : ℂ)*((p : ℂ)*(z : ℂ)) + (u.1 1 : ℂ)
  let B : ℂ := (v.1 0 : ℂ)*(z : ℂ) + (v.1 1 : ℂ)
  have hAB : (g : ℂ)*A = (p : ℂ)*B := by
    dsimp only [A,B]
    linear_combination (p : ℂ)*(z : ℂ)*h₀+h₁
  have hn : (g : ℝ)*‖A‖ = (p : ℝ)*‖B‖ := by
    simpa only [norm_mul,Complex.norm_natCast] using congrArg norm hAB
  have hBn : ‖B‖ ≠ 0 := by
    intro he
    have hb := positiveBase_pos z v
    change 0 < z.im/‖B‖^2 at hb
    simp [he] at hb
  have hAn : ‖A‖ = (p : ℝ)*‖B‖/g := by apply (eq_div_iff hg.ne').mpr; linarith
  rw [scaled_positiveBase]
  change (p : ℝ)*z.im/‖A‖^2 = ((g : ℝ)^2/p)*(z.im/‖B‖^2)
  rw [hAn]
  field_simp [hg.ne',hp'.ne',hBn] <;> ring

private theorem scaled_comp (q : ℕ) (hq : 0 < q) (B : ℕ+) (z : ℍ) :
    scaledPoint q hq (degeneracyDiagonal B B.pos • z) =
      scaledPoint (q*(B : ℕ)) (Nat.mul_pos hq B.pos) z := by
  apply UpperHalfPlane.ext
  simp only [scaledPoint_coe,degeneracyDiagonal_smul_coe,Nat.cast_mul]
  ring

theorem original_summand {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (s : ℂ) (z : ℍ) (v : PrimitivePair) :
    characterSeed hq χ (degeneracyDiagonal B B.pos • z)
      (backPair (q*(B : ℕ)) (Nat.mul_pos hq B.pos) v) s =
      rowWeight χ (q*(B : ℕ)) (Nat.mul_pos hq B.pos) v s * complexSeed z v s := by
  let p := q*(B : ℕ)
  have hp : 0 < p := Nat.mul_pos hq B.pos
  have hg : 0 < (backContent p v : ℝ) := by exact_mod_cast content_pos Nat.zero_lt_one hp v
  have hr : 0 < rowScale p v := div_pos (sq_pos_of_pos hg) (by exact_mod_cast hp)
  rw [characterSeed,scaled_comp,complexSeed,physical_base,Real.log_mul hr.ne' (positiveBase_pos z v).ne',
    Complex.ofReal_add,mul_add,Complex.exp_add,rowWeight,complexSeed,mul_assoc]

/-- The same primitive signed lattice is now indexed by every physical
row exactly once and retains its original factor one half. -/
theorem original_row_expansion {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (s : ℂ) (z : ℍ) :
    characterLatticeOldform hq χ B s z = (1/2 : ℂ) * ∑' v : PrimitivePair,
      rowWeight χ (q*(B : ℕ)) (Nat.mul_pos hq B.pos) v s * complexSeed z v s := by
  unfold characterLatticeOldform characterEisenstein
  congr 1
  rw [← (dilationEquiv (q*(B : ℕ)) (Nat.mul_pos hq B.pos)).symm.tsum_eq
    (fun v : PrimitivePair => characterSeed hq χ (degeneracyDiagonal B B.pos • z) v s)]
  exact tsum_congr (original_summand hq χ B s z)

theorem original_row_summable {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    Summable (fun v : PrimitivePair =>
      rowWeight χ (q*(B : ℕ)) (Nat.mul_pos hq B.pos) v s * complexSeed z v s) := by
  simpa only [← original_summand hq χ B s z,backPair] using
    (dilationEquiv (q*(B : ℕ)) (Nat.mul_pos hq B.pos)).symm.summable_iff.mpr
      (characterSeed_summable hq χ (degeneracyDiagonal B B.pos • z) s hs)

/-- The integral conjugate preserves both coordinates of the signed
character weight and the positive gcd of the unreduced row. -/
theorem rowWeight_invariant {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (N : ℕ) (hN : q^2*(B : ℕ) ∣ N) (γ : CongruenceSubgroup.Gamma0 N)
    (s : ℂ) (v : PrimitivePair) :
    rowWeight χ (q*(B : ℕ)) (Nat.mul_pos hq B.pos) (primitivePairEquiv (γ : SL(2,ℤ)) v) s =
      rowWeight χ (q*(B : ℕ)) (Nat.mul_pos hq B.pos) v s := by
  let p := q*(B : ℕ)
  have hp : 0 < p := Nat.mul_pos hq B.pos
  let M : SL(2,ℤ) := γ
  have hd : (q*p : ℕ) ∣ N := by simpa only [p,pow_two,mul_assoc] using hN
  have hγ : M ∈ CongruenceSubgroup.Gamma0 (q*p) :=
    (gamma0_mem_iff_level_dvd_c _ _).mpr ((by exact_mod_cast hd : ((q*p : ℕ) : ℤ) ∣ (N : ℤ)).trans
      ((gamma0_mem_iff_level_dvd_c _ _).mp γ.property))
  obtain ⟨M',hM',haa,hab,hca,hdd,_⟩ := exists_gamma0_degeneracy_matrix q p hq hp M hγ
  let w := primitivePairEquiv M v
  have hmatrix : scaleRow 1 p w.1 = scaleRow 1 p v.1 ᵥ* (M' : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [show w.1 = _ from primitivePairEquiv_value M v]
    ext i
    fin_cases i <;> simp [scaleRow,Matrix.vecMul,dotProduct,Fin.sum_univ_two,haa,hab,hdd,← hca] <;> ring
  have hrec : backContent p w • (backPair p hp w).1 =
      backContent p v • (primitivePairEquiv M' (backPair p hp v)).1 := by
    rw [← recover Nat.zero_lt_one hp,hmatrix,recover Nat.zero_lt_one hp v,
      primitivePairEquiv_value,Matrix.smul_vecMul]
  obtain ⟨hc,hu⟩ := primitive_factor_unique (content_pos Nat.zero_lt_one hp w)
    (backPair p hp w) (primitivePairEquiv M' (backPair p hp v)) hrec
  have htop : (q : ℤ) ∣ M' 0 1 := by
    refine ⟨(B : ℤ)*M 0 1,?_⟩
    rw [hab]
    simp [p,mul_assoc]
  have hbot := (gamma0_mem_iff_level_dvd_c q M').mp hM'
  have hχ : primitiveWeight χ (backPair p hp w) = primitiveWeight χ (backPair p hp v) := by
    rw [hu,primitiveWeight,primitivePairEquiv_value]
    exact characterWeight_vecMul χ M' htop hbot _
  change rowWeight χ p hp w s = rowWeight χ p hp v s
  simp only [rowWeight,rowScale,hχ,hc]

end
end ImbalancedChen.Part3.ActualCharacterCuspRowReduction20261110
