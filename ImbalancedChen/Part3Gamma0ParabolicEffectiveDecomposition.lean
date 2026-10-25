import ImbalancedChen.Part3GammaInfinityStripPeriodization
import ImbalancedChen.Part3Gamma0ComplexL1PoincareUnfolding
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

A genuine bijection between effective Gamma0 and integer translation
labels times ACTUAL GammaInfinity-leftcosets. The complete central kernel
lies in the actual parabolic subgroup. Injection is proved by actual
subgroup arithmetic and the real coordinate of T^k acting at i; surjection
uses the proven actual +/-T^k classification through its action.
No hEquiv, finite-fiber supplier, normal parabolic quotient, or duplicated
central sign is introduced. The exact reindex then turns a strip-indicator
seed into the true parabolic coset seed sum.
-/

namespace ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0NonnegativePoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a

/-- The old actual parabolic quotient's chosen integral representative. -/
def parabolicRepresentative (N : ℕ) (q : GammaInfinityCosets N) :
    CongruenceSubgroup.Gamma0 N := Quotient.out q

@[simp] theorem parabolicRepresentative_class (N : ℕ) (q : GammaInfinityCosets N) :
    (Quotient.mk'' (parabolicRepresentative N q) : GammaInfinityCosets N) = q :=
  Quotient.out_eq' q

def translationGamma (N : ℕ) (k : ℤ) : CongruenceSubgroup.Gamma0 N :=
  (infinityTranslation N k).val

@[simp] theorem translationGamma_smul (N : ℕ) (k : ℤ) (z : UpperHalfPlane) :
    translationGamma N k • z = translate k z := rfl

/-- The FULL genuine action kernel, including -I, belongs to GammaInfinity. -/
theorem actionKernel_le_gammaInfinity (N : ℕ) :
    gamma0ActionKernel N ≤ gammaInfinity N := by
  intro γ hγ
  change (γ : SL(2, ℤ)) 1 0 = 0
  rcases (gamma0_actionKernel_iff N γ).mp hγ with h | h <;> rw [h] <;> simp

private theorem relative_mem_gammaInfinity_of_effective_eq (N : ℕ)
    (a b : CongruenceSubgroup.Gamma0 N)
    (h : (QuotientGroup.mk a : effectiveGamma0 N) = QuotientGroup.mk b) :
    a * b⁻¹ ∈ gammaInfinity N := by
  apply actionKernel_le_gammaInfinity N
  apply (QuotientGroup.eq_one_iff (a * b⁻¹)).mp
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, mul_inv_cancel]

private theorem effective_eq_of_same_action (N : ℕ)
    (a b : CongruenceSubgroup.Gamma0 N)
    (h : ∀ z : UpperHalfPlane, a • z = b • z) :
    (QuotientGroup.mk a : effectiveGamma0 N) = QuotientGroup.mk b := by
  apply QuotientGroup.kerLift_injective (gamma0PermHom N)
  rw [QuotientGroup.kerLift_mk, QuotientGroup.kerLift_mk]
  apply Equiv.ext
  exact h

/-- Integer translation on the LEFT of a true parabolic coset representative. -/
def parabolicPairToEffective (N : ℕ) (p : GammaInfinityCosets N × ℤ) :
    effectiveGamma0 N :=
  QuotientGroup.mk (translationGamma N p.2 * parabolicRepresentative N p.1)

theorem parabolicPairToEffective_injective (N : ℕ) :
    Function.Injective (parabolicPairToEffective N) := by
  rintro ⟨q, k⟩ ⟨r, l⟩ heff
  let a := translationGamma N k * parabolicRepresentative N q
  let b := translationGamma N l * parabolicRepresentative N r
  have hab : (QuotientGroup.mk a : effectiveGamma0 N) = QuotientGroup.mk b := heff
  have hrel := relative_mem_gammaInfinity_of_effective_eq N a b hab
  have hrep : parabolicRepresentative N q * (parabolicRepresentative N r)⁻¹ ∈
      gammaInfinity N := by
    have hmem := (gammaInfinity N).mul_mem
      ((gammaInfinity N).mul_mem
        ((gammaInfinity N).inv_mem (infinityTranslation N k).property) hrel)
      (infinityTranslation N l).property
    have heq : parabolicRepresentative N q * (parabolicRepresentative N r)⁻¹ =
        (translationGamma N k)⁻¹ * (a * b⁻¹) * translationGamma N l := by
      dsimp [a, b]
      group
    rw [heq]
    exact hmem
  have hqr : q = r := by
    calc
      q = Quotient.mk'' (parabolicRepresentative N q) :=
        (parabolicRepresentative_class N q).symm
      _ = Quotient.mk'' (parabolicRepresentative N r) :=
        Quotient.sound ((parabolic_orbit_iff_relative N _ _).mpr hrep)
      _ = r := parabolicRepresentative_class N r
  subst r
  have hact := same_effective_class_action N a b hab
    ((parabolicRepresentative N q)⁻¹ • UpperHalfPlane.I)
  have htrans : translate k UpperHalfPlane.I = translate l UpperHalfPlane.I := by
    simpa [a, b, mul_smul] using hact
  have hkl : k = l := by
    have hcoord := congrArg UpperHalfPlane.re htrans
    simp only [translate_re] at hcoord
    exact_mod_cast (add_right_cancel hcoord)
  exact Prod.ext rfl hkl

theorem parabolicPairToEffective_surjective (N : ℕ) :
    Function.Surjective (parabolicPairToEffective N) := by
  intro e
  let γ := effectiveRepresentative N e
  let q : GammaInfinityCosets N := Quotient.mk'' γ
  let r := parabolicRepresentative N q
  have hclass : (Quotient.mk'' γ : GammaInfinityCosets N) = Quotient.mk'' r :=
    (parabolicRepresentative_class N q).symm
  have hrel : γ * r⁻¹ ∈ gammaInfinity N :=
    (parabolic_orbit_iff_relative N γ r).mp (Quotient.exact hclass)
  let η : gammaInfinity N := ⟨γ * r⁻¹, hrel⟩
  obtain ⟨k, hk⟩ := parabolic_action_integer N η
  refine ⟨(q, k), ?_⟩
  calc
    parabolicPairToEffective N (q, k) = (QuotientGroup.mk γ : effectiveGamma0 N) := by
      apply effective_eq_of_same_action N
      intro z
      change (translationGamma N k * r) • z = γ • z
      calc
        (translationGamma N k * r) • z = translate k (r • z) := by
          rw [mul_smul, translationGamma_smul]
        _ = η • (r • z) := (hk (r • z)).symm
        _ = γ • z := by
          change (γ * r⁻¹) • (r • z) = γ • z
          simp [mul_smul]
    _ = e := effectiveRepresentative_class N e

/-- Constructed actual bijection; central +/- matrices occur only once. -/
def parabolicEffectiveEquiv (N : ℕ) :
    (GammaInfinityCosets N × ℤ) ≃ effectiveGamma0 N :=
  Equiv.ofBijective (parabolicPairToEffective N)
    ⟨parabolicPairToEffective_injective N, parabolicPairToEffective_surjective N⟩

def effectiveIntegerParabolicEquiv (N : ℕ) :
    effectiveGamma0 N ≃ ℤ × GammaInfinityCosets N :=
  (parabolicEffectiveEquiv N).symm.trans (Equiv.prodComm _ _)

/-- Exact action formula for the constructed pair index. -/
theorem parabolicPair_action (N : ℕ) (q : GammaInfinityCosets N) (k : ℤ)
    (z : UpperHalfPlane) :
    effectiveMatrixAction N (parabolicEffectiveEquiv N (q, k)) z =
      translate k (parabolicRepresentative N q • z) := by
  calc
    _ = (translationGamma N k * parabolicRepresentative N q) • z :=
      same_effective_class_action N _ _
        (effectiveRepresentative_class N (parabolicPairToEffective N (q, k))) z
    _ = _ := by rw [mul_smul, translationGamma_smul]

/-- One and only one integer translate of a point lies in the half-open strip. -/
theorem unique_translate_mem_strip (z : UpperHalfPlane) :
    ∃! k : ℤ, translate k z ∈ strip := by
  obtain ⟨n, hn, hu⟩ := unique_horizontal_period z
  refine ⟨-n, ?_, ?_⟩
  · simpa only [strip, mem_setOf_eq, translate_re, Int.cast_neg, neg_add_eq_sub] using hn
  · intro k hk
    have hmem : z.re - ((-k : ℤ) : ℝ) ∈ Ico (0 : ℝ) 1 := by
      simpa only [strip, mem_setOf_eq, translate_re, Int.cast_neg, sub_neg_eq_add,
        add_comm] using hk
    have heq := hu (-k) hmem
    omega

/-- Periodizing a strip-indicator of a genuine periodic function recovers
that function exactly, since there is a unique nonzero strip tile. -/
theorem periodic_strip_indicator_tsum {A : Type*} [AddCommMonoid A]
    [TopologicalSpace A] [T2Space A] [ContinuousAdd A]
    (F : UpperHalfPlane → A)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z) (z : UpperHalfPlane) :
    (∑' k : ℤ, strip.indicator F (translate k z)) = F z := by
  classical
  obtain ⟨k0, hk0, hu⟩ := unique_translate_mem_strip z
  calc
    _ = strip.indicator F (translate k0 z) := tsum_eq_single k0 (fun k hk => by
      have hnot : translate k z ∉ strip := fun hm => hk (hu k hm)
      exact indicator_of_notMem hnot F)
    _ = F z := by rw [indicator_of_mem hk0, hperiod]

/-- Pointwise true nonnegative parabolic-coset reindex. The only analytic
operation is a nonnegative double sum, so no hAbsSum is assumed. -/
theorem nonnegative_effective_trace_eq_parabolic (N : ℕ)
    (F : UpperHalfPlane → ℝ≥0∞)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z) (z : UpperHalfPlane) :
    fullSeedTrace N (strip.indicator F) z =
      ∑' q : GammaInfinityCosets N, F (parabolicRepresentative N q • z) := by
  change (∑' e : effectiveGamma0 N,
    strip.indicator F (effectiveMatrixAction N e z)) = _
  calc
    _ = ∑' p : GammaInfinityCosets N × ℤ,
        strip.indicator F (effectiveMatrixAction N (parabolicEffectiveEquiv N p) z) :=
      ((parabolicEffectiveEquiv N).tsum_eq _).symm
    _ = ∑' p : GammaInfinityCosets N × ℤ,
        strip.indicator F (translate p.2 (parabolicRepresentative N p.1 • z)) := by
      apply tsum_congr
      rintro ⟨q, k⟩
      rw [parabolicPair_action]
    _ = ∑' q : GammaInfinityCosets N, ∑' k : ℤ,
        strip.indicator F (translate k (parabolicRepresentative N q • z)) :=
      ENNReal.tsum_prod
    _ = _ := by simp_rw [periodic_strip_indicator_tsum F hperiod]

end
end ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a
