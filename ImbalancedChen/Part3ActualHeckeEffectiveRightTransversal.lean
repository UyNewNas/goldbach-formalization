import ImbalancedChen.Part3ActualHeckeDualRightTransversal
import ImbalancedChen.Part3Gamma0EffectiveFiniteUnfolding

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual normalized Hecke dual right-transversal descends through the
FULL original Gamma0 action kernel, including -I. Kernel multiplication
is explicitly carried through inversion, so the induced effective index
map is genuinely well defined and involutive. The final effective right
index equivalence preserves actual upper-half-plane action pointwise.
No extra factor two, assumed quotient bijection, seed sum or Poincare
identity is introduced. Compact-seed summability is a subsequent consumer.
-/

namespace ImbalancedChen.Part3.ActualHeckeEffectiveRightTransversal20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeRealBranch20261026b
open ActualHeckeDualRightTransversal20261026b
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a

variable (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)

private theorem castKernel_sign (n : CongruenceSubgroup.Gamma0 N) (hn : n ∈ gamma0ActionKernel N) :
    castIntegral n = 1 ∨ castIntegral n = -1 := by
  rcases (gamma0_actionKernel_iff N n).mp hn with hn | hn
  · left
    simp [castIntegral,hn]
  · right
    apply Subtype.ext
    ext i j
    simp [castIntegral,hn,Matrix.SpecialLinearGroup.map_apply_coe]

private theorem castKernel_inv (n : CongruenceSubgroup.Gamma0 N) (hn : n ∈ gamma0ActionKernel N) :
    (castIntegral n)⁻¹ = castIntegral n := by
  rcases castKernel_sign N n hn with heq | heq <;> rw [heq] <;> simp

private theorem castKernel_commute (n : CongruenceSubgroup.Gamma0 N)
    (hn : n ∈ gamma0ActionKernel N) (A : SL(2, ℝ)) : castIntegral n*A=A*castIntegral n := by
  rcases castKernel_sign N n hn with heq | heq <;> rw [heq] <;> simp

/-- The inverse factorization carries the genuine central kernel on the
left factor and keeps the physical branch index unchanged. -/
theorem inversePair_kernel_left (n : CongruenceSubgroup.Gamma0 N) (hn : n ∈ gamma0ActionKernel N)
    (q : CongruenceSubgroup.Gamma0 N × Branch p) :
    inversePair N p hp hpN (n*q.1,q.2) =
      (n*(inversePair N p hp hpN q).1,(inversePair N p hp hpN q).2) := by
  apply leftBranchValue_injective N p hp
  rw [inversePair_value]
  have hleft : leftBranchValue N p hp (n*q.1,q.2) = castIntegral n*leftBranchValue N p hp q := by
    simp only [leftBranchValue,Subgroup.coe_mul,castIntegral,map_mul]
    group
  have hright : leftBranchValue N p hp (n*(inversePair N p hp hpN q).1,
      (inversePair N p hp hpN q).2) = castIntegral n*leftBranchValue N p hp (inversePair N p hp hpN q) := by
    simp only [leftBranchValue,Subgroup.coe_mul,castIntegral,map_mul]
    group
  rw [hleft,hright,inversePair_value]
  calc
    _ = (leftBranchValue N p hp q)⁻¹*(castIntegral n)⁻¹ := by group
    _ = _ := rw [castKernel_inv N n hn,castKernel_commute N n hn]

/-- Explicit well-definedness on the actual action quotient. No choice
of representative may change either branch or effective factor. -/
theorem inversePair_class_congr (g h : CongruenceSubgroup.Gamma0 N)
    (hclass : (QuotientGroup.mk g : effectiveGamma0 N)=QuotientGroup.mk h) (j : Branch p) :
    ((QuotientGroup.mk (inversePair N p hp hpN (g,j)).1 : effectiveGamma0 N),
      (inversePair N p hp hpN (g,j)).2) =
    (QuotientGroup.mk (inversePair N p hp hpN (h,j)).1,
      (inversePair N p hp hpN (h,j)).2) := by
  let n : CongruenceSubgroup.Gamma0 N := h*g⁻¹
  have hn : n ∈ gamma0ActionKernel N := by
    apply (QuotientGroup.eq_one_iff n).mp
    simp only [n,QuotientGroup.mk_mul,QuotientGroup.mk_inv]
    rw [hclass]
    simp
  have hh : h=n*g := by dsimp [n]; group
  rw [hh,inversePair_kernel_left N p hp hpN n hn (g,j)]
  simp only [Prod.fst,Prod.snd,QuotientGroup.mk_mul]
  rw [(QuotientGroup.eq_one_iff n).mpr hn]
  simp

def effectiveInversePair (q : effectiveGamma0 N × Branch p) : effectiveGamma0 N × Branch p :=
  (QuotientGroup.mk (inversePair N p hp hpN (effectiveRepresentative N q.1,q.2)).1,
    (inversePair N p hp hpN (effectiveRepresentative N q.1,q.2)).2)

theorem effectiveInversePair_mk (g : CongruenceSubgroup.Gamma0 N) (j : Branch p) :
    effectiveInversePair N p hp hpN (QuotientGroup.mk g,j) =
      ((QuotientGroup.mk (inversePair N p hp hpN (g,j)).1 : effectiveGamma0 N),
        (inversePair N p hp hpN (g,j)).2) :=
  inversePair_class_congr N p hp hpN _ g (effectiveRepresentative_class N (QuotientGroup.mk g)) j

theorem effectiveInversePair_involutive : Function.Involutive (effectiveInversePair N p hp hpN) := by
  rintro ⟨q,j⟩
  refine Quotient.inductionOn q (fun g => ?_)
  rw [effectiveInversePair_mk,effectiveInversePair_mk]
  exact congrArg (fun r : CongruenceSubgroup.Gamma0 N × Branch p =>
    ((QuotientGroup.mk r.1 : effectiveGamma0 N),r.2))
      (inversePair_involutive N p hp hpN (g,j))

def effectiveDoubleCosetInversion : (effectiveGamma0 N × Branch p) ≃ (effectiveGamma0 N × Branch p) where
  toFun := effectiveInversePair N p hp hpN
  invFun := effectiveInversePair N p hp hpN
  left_inv := effectiveInversePair_involutive N p hp hpN
  right_inv := effectiveInversePair_involutive N p hp hpN

private def effectiveInverseSwap : (effectiveGamma0 N × Branch p) ≃ (Branch p × effectiveGamma0 N) where
  toFun q := (q.2,q.1⁻¹)
  invFun q := (q.2⁻¹,q.1)
  left_inv := by rintro ⟨g,j⟩; simp
  right_inv := by rintro ⟨j,g⟩; simp

/-- Genuine effective dual right-transversal: once per full +/-I class. -/
def effectiveDualRightTransversal : (effectiveGamma0 N × Branch p) ≃ (Branch p × effectiveGamma0 N) :=
  (effectiveDoubleCosetInversion N p hp hpN).trans (effectiveInverseSwap N p)

theorem effectiveDualRightTransversal_mk (g : CongruenceSubgroup.Gamma0 N) (j : Branch p) :
    effectiveDualRightTransversal N p hp hpN (QuotientGroup.mk g,j) =
      ((actualDualRightTransversal N p hp hpN (g,j)).1,
        (QuotientGroup.mk (actualDualRightTransversal N p hp hpN (g,j)).2 : effectiveGamma0 N)) := by
  change ((effectiveInversePair N p hp hpN (QuotientGroup.mk g,j)).2,
    (effectiveInversePair N p hp hpN (QuotientGroup.mk g,j)).1⁻¹) = _
  rw [effectiveInversePair_mk]
  change ((inversePair N p hp hpN (g,j)).2,
    (QuotientGroup.mk (inversePair N p hp hpN (g,j)).1 : effectiveGamma0 N)⁻¹) = _
  rw [← QuotientGroup.mk_inv]
  rfl

private theorem effectiveMatrixAction_mk (g : CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    effectiveMatrixAction N (QuotientGroup.mk g) z = g • z :=
  same_effective_class_action N _ g (effectiveRepresentative_class N (QuotientGroup.mk g)) z

/-- Exact action identity for the actual effective index equivalence.
It is now legitimate to reindex a convergent seed sum by this equivalence. -/
theorem effectiveDualRightTransversal_action (q : effectiveGamma0 N × Branch p) (z : ℍ) :
    (branchSL p hp.pos (effectiveDualRightTransversal N p hp hpN q).1)⁻¹ •
      effectiveMatrixAction N (effectiveDualRightTransversal N p hp hpN q).2 z =
        effectiveMatrixAction N q.1 (branchSL p hp.pos q.2 • z) := by
  rcases q with ⟨q,j⟩
  refine Quotient.inductionOn q (fun g => ?_)
  rw [effectiveDualRightTransversal_mk,effectiveMatrixAction_mk,effectiveMatrixAction_mk]
  have h := congrArg (fun A : SL(2, ℝ) => A • z)
    (actualDualRightTransversal_value N p hp hpN (g,j))
  simpa only [leftBranchValue,mul_smul,castIntegral_smul] using h

end
end ImbalancedChen.Part3.ActualHeckeEffectiveRightTransversal20261026b
