import ImbalancedChen.Part3ActualHeckeFiniteCover
import ImbalancedChen.Part3ActualHeckeReversalInvolution

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
A genuine dual RIGHT transversal for the actual normalized REAL SL2 Hecke
branches. The left branch representatives are not reused as right reps.
The proved Bezout identity B*gamma*B=delta gives B^-1=gamma*B*delta^-1.
Actual finite-cover factors then prove inverse closure of EVERY branch;
actual branch separation proves uniqueness, yielding an involutive index
equivalence and an exact Gamma×Branch -> Branch×Gamma right reindexing.
All B_j below are normalized determinant-one REAL matrices. No impossible
raw determinant-p integer inverse factorization is asserted. Effective
+/-I descent and locally finite compact-seed Poincare sums remain separate.
-/

namespace ImbalancedChen.Part3.ActualHeckeDualRightTransversal20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b
open ActualPrimeHeckeRealBranch20261026b ActualHeckeFiniteCover20261026b
open ActualHeckeReversalInvolution20261026b

variable (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)

def leftBranchValue (q : CongruenceSubgroup.Gamma0 N × Branch p) : SL(2, ℝ) :=
  castIntegral q.1 * branchSL p hp.pos q.2

private theorem castIntegral_injective : Function.Injective castIntegral := by
  intro g h hgh
  apply Subtype.ext
  ext i j
  have he := congrArg (fun A : SL(2, ℝ) => A i j) hgh
  have he' : (g i j : ℝ) = (h i j : ℝ) := by
    simpa [castIntegral,Matrix.SpecialLinearGroup.map_apply_coe] using he
  exact_mod_cast he'

/-- Literal left factors and physical branches are uniquely determined,
proved by cancelling the common REAL normalization and integer casting. -/
theorem leftBranchValue_injective : Function.Injective (leftBranchValue N p hp) := by
  rintro ⟨g,j⟩ ⟨h,k⟩ heq
  have hs : Real.sqrt (p : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (show (0 : ℝ) < p by exact_mod_cast hp.pos)).ne'
  have hm := congrArg (fun A : SL(2, ℝ) => (A : Matrix (Fin 2) (Fin 2) ℝ)) heq
  change (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) *
      ((Real.sqrt (p : ℝ))⁻¹ • (branchMatrix p j).map (Int.castRingHom ℝ)) =
    (((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) *
      ((Real.sqrt (p : ℝ))⁻¹ • (branchMatrix p k).map (Int.castRingHom ℝ)) at hm
  rw [Matrix.mul_smul,Matrix.mul_smul,← Matrix.map_mul,← Matrix.map_mul] at hm
  have hcancel := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => Real.sqrt (p : ℝ) • A) hm
  simp only [smul_smul,mul_inv_cancel₀ hs,one_smul] at hcancel
  have hint : ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)*branchMatrix p j =
      ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)*branchMatrix p k := by
    ext i l
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i l) hcancel
    have he' : ((((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)*branchMatrix p j) i l : ℝ) =
        ((((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)*branchMatrix p k) i l : ℝ) := by
      simpa using he
    exact_mod_cast he'
  have hjk := branch_eq_of_two_factorizations p hp j k g h hint
  subst k
  have hcast : castIntegral (g : SL(2, ℤ)) = castIntegral (h : SL(2, ℤ)) :=
    mul_right_cancel heq
  have hgh : g = h := Subtype.ext (castIntegral_injective hcast)
  exact Prod.ext hgh rfl

private theorem normalized_right_factor (g : CongruenceSubgroup.Gamma0 N) (j : Branch p) :
    ∃ h : CongruenceSubgroup.Gamma0 N, ∃ k : Branch p,
      branchSL p hp.pos j * castIntegral g = castIntegral h * branchSL p hp.pos k := by
  obtain ⟨h,hh,hfactor⟩ := branchImage_factor N p hp hpN g g.property j
  exact ⟨⟨h,hh⟩,branchImage N p hp hpN g g.property j,
    branchSL_factor p hp.pos j _ g h hfactor⟩

/-- Inverse closure starts from the ACTUAL normalized infinity branch,
using the proved integral Bezout factors on BOTH sides. -/
theorem infinity_branch_inverse :
    (branchSL p hp.pos none)⁻¹ = castIntegral (reversalGamma N p hp hpN) *
      branchSL p hp.pos none * (castIntegral (reversalDelta N p hp hpN))⁻¹ := by
  rw [← dilation_gamma_dilation N p hp hpN]
  group

/-- Every normalized real branch inverse is an actual Gamma0 left factor
times an actual physical branch. The existence is derived, not supplied. -/
theorem branch_inverse_left_factor (j : Branch p) :
    ∃ h : CongruenceSubgroup.Gamma0 N, ∃ k : Branch p,
      castIntegral h * branchSL p hp.pos k = (branchSL p hp.pos j)⁻¹ := by
  let r := coverRepresentative N p hp hpN j
  obtain ⟨a,ha,hfactor⟩ := branchImage_factor N p hp hpN r r.property none
  have hlabel := coverRepresentative_branch N p hp hpN j
  change branchImage N p hp hpN r r.property none = j at hlabel
  rw [hlabel] at hfactor
  have hreal := branchSL_factor p hp.pos none j r a hfactor
  let aG : CongruenceSubgroup.Gamma0 N := ⟨a,ha⟩
  let u : CongruenceSubgroup.Gamma0 N := (reversalDelta N p hp hpN)⁻¹*aG
  obtain ⟨b,k,hb⟩ := normalized_right_factor N p hp hpN u none
  let h : CongruenceSubgroup.Gamma0 N := r⁻¹*reversalGamma N p hp hpN*b
  have hh : castIntegral h = (castIntegral r)⁻¹ * castIntegral (reversalGamma N p hp hpN) * castIntegral b := by
    simp only [h,Subgroup.coe_mul,Subgroup.coe_inv,castIntegral,map_mul,map_inv]
  have hu : castIntegral u = (castIntegral (reversalDelta N p hp hpN))⁻¹*castIntegral a := by
    simp only [u,aG,Subgroup.coe_mul,Subgroup.coe_inv,castIntegral,map_mul,map_inv]
  refine ⟨h,k,?_⟩
  calc
    _ = (castIntegral r)⁻¹ * castIntegral (reversalGamma N p hp hpN) *
        (castIntegral b * branchSL p hp.pos k) := by rw [hh]; group
    _ = (castIntegral r)⁻¹ * castIntegral (reversalGamma N p hp hpN) *
        (branchSL p hp.pos none * castIntegral u) := by rw [hb]
    _ = (castIntegral r)⁻¹ *
        (castIntegral (reversalGamma N p hp hpN)*branchSL p hp.pos none*
          (castIntegral (reversalDelta N p hp hpN))⁻¹) * castIntegral a := by rw [hu]; group
    _ = (castIntegral r)⁻¹ * (branchSL p hp.pos none)⁻¹ * castIntegral a := by
      rw [← infinity_branch_inverse N p hp hpN]
    _ = _ := by
      have hbranch : branchSL p hp.pos j = (castIntegral a)⁻¹*branchSL p hp.pos none*castIntegral r := by
        rw [mul_assoc,hreal]
        group
      rw [hbranch]
      group

/-- Actual inverse closure of the entire normalized real double-coset
parameterization, with every group factor still in original Gamma0(N). -/
theorem exists_inverse_pair (q : CongruenceSubgroup.Gamma0 N × Branch p) :
    ∃ r : CongruenceSubgroup.Gamma0 N × Branch p,
      leftBranchValue N p hp r = (leftBranchValue N p hp q)⁻¹ := by
  obtain ⟨a,k,ha⟩ := branch_inverse_left_factor N p hp hpN q.2
  obtain ⟨b,l,hb⟩ := normalized_right_factor N p hp hpN q.1⁻¹ k
  refine ⟨⟨a*b,l⟩,?_⟩
  change castIntegral (a*b : CongruenceSubgroup.Gamma0 N) * branchSL p hp.pos l = _
  rw [show castIntegral (a*b : CongruenceSubgroup.Gamma0 N) = castIntegral a * castIntegral b by
    simp only [Subgroup.coe_mul,castIntegral,map_mul]]
  calc
    _ = castIntegral a*(branchSL p hp.pos k*castIntegral q.1⁻¹) := by rw [hb]; group
    _ = (castIntegral a*branchSL p hp.pos k)*(castIntegral q.1)⁻¹ := by
      simp only [Subgroup.coe_inv,castIntegral,map_inv]
      group
    _ = _ := by rw [ha]; unfold leftBranchValue; group

def inversePair (q : CongruenceSubgroup.Gamma0 N × Branch p) : CongruenceSubgroup.Gamma0 N × Branch p :=
  Classical.choose (exists_inverse_pair N p hp hpN q)

theorem inversePair_value (q : CongruenceSubgroup.Gamma0 N × Branch p) :
    leftBranchValue N p hp (inversePair N p hp hpN q) = (leftBranchValue N p hp q)⁻¹ :=
  Classical.choose_spec (exists_inverse_pair N p hp hpN q)

theorem inversePair_involutive : Function.Involutive (inversePair N p hp hpN) := by
  intro q
  apply leftBranchValue_injective N p hp
  rw [inversePair_value,inversePair_value,inv_inv]

def normalizedDoubleCosetInversion :
    (CongruenceSubgroup.Gamma0 N × Branch p) ≃ (CongruenceSubgroup.Gamma0 N × Branch p) where
  toFun := inversePair N p hp hpN
  invFun := inversePair N p hp hpN
  left_inv := inversePair_involutive N p hp hpN
  right_inv := inversePair_involutive N p hp hpN

private def inverseSwap : (CongruenceSubgroup.Gamma0 N × Branch p) ≃ (Branch p × CongruenceSubgroup.Gamma0 N) where
  toFun q := (q.2,q.1⁻¹)
  invFun q := (q.2⁻¹,q.1)
  left_inv := by rintro ⟨g,j⟩; simp
  right_inv := by rintro ⟨j,g⟩; simp

/-- Correct dual right transversal: the representatives are B_j^-1.
This is an ACTUAL index equivalence, not a presumed double-coset equality. -/
def actualDualRightTransversal :
    (CongruenceSubgroup.Gamma0 N × Branch p) ≃ (Branch p × CongruenceSubgroup.Gamma0 N) :=
  (normalizedDoubleCosetInversion N p hp hpN).trans (inverseSwap N p)

theorem actualDualRightTransversal_value (q : CongruenceSubgroup.Gamma0 N × Branch p) :
    (branchSL p hp.pos (actualDualRightTransversal N p hp hpN q).1)⁻¹ *
      castIntegral (actualDualRightTransversal N p hp hpN q).2 = leftBranchValue N p hp q := by
  change (branchSL p hp.pos (inversePair N p hp hpN q).2)⁻¹ *
    castIntegral ((inversePair N p hp hpN q).1⁻¹) = _
  have hcast : castIntegral ((inversePair N p hp hpN q).1⁻¹) =
      (castIntegral (inversePair N p hp hpN q).1)⁻¹ := by
    simp only [Subgroup.coe_inv,castIntegral,map_inv]
  rw [hcast]
  calc
    _ = (leftBranchValue N p hp (inversePair N p hp hpN q))⁻¹ := by unfold leftBranchValue; group
    _ = _ := by rw [inversePair_value,inv_inv]

end
end ImbalancedChen.Part3.ActualHeckeDualRightTransversal20261026b

