import ImbalancedChen.Part3ActualCompactBruhatAllModuli
import ImbalancedChen.Part3ActualEisensteinPrimitiveResidues
import ImbalancedChen.Part3ActualEisensteinPositiveCFourier

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

A genuine normal-form index for the existing actual GammaInfinity\Gamma0
quotient: one zero-lower-left class, plus positive lower-left primitive
fibers. The existing unitTranslateEquiv is reused on every positive fiber.
Actual periodic Fourier-radial seeds are evaluated on the original cosets,
including the exact single c=0 contribution. No canonical-series identity
is substituted for the actual coset sum.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.CompactParabolicNormalIndex20261025a

open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEisensteinHalfPairs20261025a
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a (PrimitiveD)
open ImbalancedChen.Part3.ActualEisensteinPrimitiveResidues20261025a
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly

abbrev PositiveRowIndex (N : ℕ) := Σ c : ℕ+, PrimitiveD N ((c : ℕ) : ℤ)
abbrev NormalRowIndex (N : ℕ) := Unit ⊕ PositiveRowIndex N

/-- Normalized primitive rows, retaining their actual level gate. -/
def normalRow (N : ℕ) : NormalRowIndex N → LevelPrimitiveRow N
  | Sum.inl _ => ⟨![0, 1], by simp⟩
  | Sum.inr ⟨c, d⟩ => ⟨![((c : ℕ) : ℤ), d.1], by simpa using d.property⟩

def normalRowClass (N : ℕ) (i : NormalRowIndex N) : SignedPrimitiveRows N :=
  Quotient.mk'' (normalRow N i)

/-- The central sign cannot identify two positive first coordinates, and
the zero-first-coordinate primitive pair has only one signed class. -/
theorem normalRowClass_injective (N : ℕ) : Function.Injective (normalRowClass N) := by
  intro i j hij
  have hrel : (normalRow N i).1 = (normalRow N j).1 ∨
      (normalRow N i).1 = -(normalRow N j).1 := Quotient.exact hij
  rcases i with ⟨⟩ | ⟨c, d⟩ <;> rcases j with ⟨⟩ | ⟨e, f⟩
  · rfl
  · have hepos : (0 : ℤ) < (e : ℕ) := by exact_mod_cast e.property
    rcases hrel with h | h
    · have h0 := congrFun h 0
      change (0 : ℤ) = ((e : ℕ) : ℤ) at h0
      linarith
    · have h0 := congrFun h 0
      change (0 : ℤ) = -((e : ℕ) : ℤ) at h0
      linarith
  · have hcpos : (0 : ℤ) < (c : ℕ) := by exact_mod_cast c.property
    rcases hrel with h | h
    · have h0 := congrFun h 0
      change ((c : ℕ) : ℤ) = 0 at h0
      linarith
    · have h0 := congrFun h 0
      change ((c : ℕ) : ℤ) = 0 at h0
      linarith
  · rcases hrel with h | h
    · have h0 := congrFun h 0
      change ((c : ℕ) : ℤ) = ((e : ℕ) : ℤ) at h0
      have hnat : (c : ℕ) = (e : ℕ) := by exact_mod_cast h0
      have hce : c = e := Subtype.ext hnat
      subst e
      have h1 := congrFun h 1
      change d.1 = f.1 at h1
      have hdf : d = f := Subtype.ext h1
      subst f
      rfl
    · have h0 := congrFun h 0
      change ((c : ℕ) : ℤ) = -((e : ℕ) : ℤ) at h0
      have hcpos : (0 : ℤ) < (c : ℕ) := by exact_mod_cast c.property
      have hepos : (0 : ℤ) < (e : ℕ) := by exact_mod_cast e.property
      linarith

private theorem normalRowClass_surjective_nonneg (N : ℕ) (v : LevelPrimitiveRow N)
    (hc : 0 ≤ v.1 0) : ∃ i : NormalRowIndex N, normalRowClass N i = Quotient.mk'' v := by
  by_cases hzero : v.1 0 = 0
  · have hdunit : IsUnit (v.1 1) := isCoprime_zero_left.mp (by
      simpa only [hzero] using v.property.1)
    refine ⟨Sum.inl (), Quotient.sound ?_⟩
    change (normalRow N (Sum.inl ())).1 = v.1 ∨ (normalRow N (Sum.inl ())).1 = -v.1
    rcases Int.isUnit_eq_one_or hdunit with hd | hd
    · left
      funext j
      fin_cases j <;> simp [normalRow, hzero, hd]
    · right
      funext j
      fin_cases j <;> simp [normalRow, hzero, hd]
  · have hcpos : 0 < v.1 0 := by omega
    let c : ℕ+ := ⟨(v.1 0).toNat, by omega⟩
    have hcast : ((c : ℕ) : ℤ) = v.1 0 := by
      exact Int.toNat_of_nonneg hc
    let d : PrimitiveD N ((c : ℕ) : ℤ) := ⟨v.1 1, by
      simpa only [hcast] using v.property⟩
    refine ⟨Sum.inr ⟨c, d⟩, Quotient.sound (Or.inl ?_)⟩
    funext j
    fin_cases j <;> simp [normalRow, d, hcast]

/-- Every actual signed primitive row has exactly one of the normal forms.
Negation uses the existing actual rowNeg; no normalization premise is used. -/
theorem normalRowClass_surjective (N : ℕ) : Function.Surjective (normalRowClass N) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  by_cases hc : 0 ≤ v.1 0
  · exact normalRowClass_surjective_nonneg N v hc
  · have hn : 0 ≤ (rowNeg N v).1 0 := by
      change 0 ≤ -(v.1 0)
      omega
    obtain ⟨i, hi⟩ := normalRowClass_surjective_nonneg N (rowNeg N v) hn
    refine ⟨i, hi.trans (Quotient.sound (Or.inr ?_))⟩
    rfl

def normalRowEquiv (N : ℕ) : NormalRowIndex N ≃ SignedPrimitiveRows N :=
  Equiv.ofBijective (normalRowClass N)
    ⟨normalRowClass_injective N, normalRowClass_surjective N⟩

/-- This is an equivalence from the ORIGINAL actual parabolic coset type.
It reuses the established actual coset-to-signed-row equivalence. -/
def parabolicNormalIndexEquiv (N : ℕ) : GammaInfinityCosets N ≃ NormalRowIndex N :=
  (parabolicPrimitiveRowEquiv N).trans (normalRowEquiv N).symm

theorem parabolicNormalIndexEquiv_symm_row (N : ℕ) (i : NormalRowIndex N) :
    parabolicRowMap N ((parabolicNormalIndexEquiv N).symm i) = normalRowClass N i := by
  change (parabolicPrimitiveRowEquiv N)
    ((parabolicPrimitiveRowEquiv N).symm ((normalRowEquiv N) i)) = (normalRowEquiv N) i
  exact (parabolicPrimitiveRowEquiv N).apply_symm_apply _

/-- Equality to a normal coset is derived from an actual bottom row. -/
theorem normalIndex_coset_of_row (N : ℕ) (i : NormalRowIndex N)
    (g : CongruenceSubgroup.Gamma0 N) (hrow : gamma0BottomRow N g = normalRow N i) :
    (parabolicNormalIndexEquiv N).symm i = Quotient.mk'' g := by
  apply parabolicRowMap_injective N
  rw [parabolicNormalIndexEquiv_symm_row, parabolicRowMap_mk]
  change Quotient.mk'' (normalRow N i) = Quotient.mk'' (gamma0BottomRow N g)
  rw [hrow]

/-- The actual Fourier-radial seed is integer-periodic, so it genuinely
descends to the existing parabolic coset quotient. -/
theorem fourierRadialSeed_integer_periodic (m : ℤ) (ψ : ℝ → ℂ) :
    ∀ k : ℤ, ∀ z : UpperHalfPlane,
      fourierRadialSeed m ψ ((k : ℝ) +ᵥ z) = fourierRadialSeed m ψ z := by
  intro k z
  have hk : ((k : ℝ) : UnitAddCircle) = 0 :=
    AddCircle.coe_eq_zero_iff.mpr ⟨k, by simp⟩
  rw [fourierRadialSeed_translate, hk]
  simp

def compactCosetSeed (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ) (z : UpperHalfPlane) :
    GammaInfinityCosets N → ℂ :=
  periodicSeedOnCosets N (fourierRadialSeed m ψ) (fourierRadialSeed_integer_periodic m ψ) z

/-- The original actual parabolic Poincare definition, before reindexing. -/
def actualCompactPoincare (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑' q : GammaInfinityCosets N, compactCosetSeed N m ψ z q

def indexedCompactSeed (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ) (z : UpperHalfPlane)
    (i : NormalRowIndex N) : ℂ :=
  compactCosetSeed N m ψ z ((parabolicNormalIndexEquiv N).symm i)

/-- The c=0 primitive pair becomes ONE actual parabolic class and has
exactly the original seed value, with no leftover factor 2 or 1/2. -/
theorem indexedCompactSeed_zero (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ) (z : UpperHalfPlane) :
    indexedCompactSeed N m ψ z (Sum.inl ()) = fourierRadialSeed m ψ z := by
  have hrow : gamma0BottomRow N (1 : CongruenceSubgroup.Gamma0 N) =
      normalRow N (Sum.inl ()) := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [gamma0BottomRow, bottomRow, normalRow]
  unfold indexedCompactSeed compactCosetSeed
  rw [normalIndex_coset_of_row N _ 1 hrow, periodicSeedOnCosets_mk]
  simp

/-- The existing actual unit-residue/integer-translate equivalence
identifies each positive normal class with the actual canonical matrix
right-translated by T^k. -/
theorem indexedCompactSeed_unit_translate (N : ℕ) (c : ℕ+)
    (hNc : (N : ℤ) ∣ ((c : ℕ) : ℤ)) (m : ℤ) (ψ : ℝ → ℂ)
    (z : UpperHalfPlane) (u : (ZMod (c : ℕ))ˣ) (k : ℤ) :
    indexedCompactSeed N m ψ z
      (Sum.inr ⟨c, primitiveDUnitTranslateEquiv N (c : ℕ) hNc (u, k)⟩) =
      fourierRadialSeed m ψ
        ((canonicalMatrix (c : ℕ) ⟨(u : ZMod (c : ℕ)), u.isUnit⟩ * ModularGroup.T ^ k) • z) := by
  have hNcNat : N ∣ (c : ℕ) := by exact_mod_cast hNc
  let U : UnitResidue (c : ℕ) := ⟨(u : ZMod (c : ℕ)), u.isUnit⟩
  let G : CongruenceSubgroup.Gamma0 N :=
    ⟨canonicalMatrix (c : ℕ) U * ModularGroup.T ^ k,
      mul_mem (canonicalMatrix_mem_gamma0 N (c : ℕ) hNcNat U) (translation_mem_gamma0 N k)⟩
  have hrow : gamma0BottomRow N G = normalRow N
      (Sum.inr ⟨c, primitiveDUnitTranslateEquiv N (c : ℕ) hNc (u, k)⟩) := by
    apply Subtype.ext
    funext j
    fin_cases j <;>
      simp [gamma0BottomRow, bottomRow, G, U, normalRow, canonicalMatrix,
        lowerRepresentative, primitiveDUnitTranslateEquiv_value, coe_mul,
        ModularGroup.coe_T_zpow, Matrix.mul_fin_two]
  unfold indexedCompactSeed compactCosetSeed
  rw [normalIndex_coset_of_row N _ G hrow, periodicSeedOnCosets_mk]
  rfl

/-- Actual coset reindexing, justified by the proved actual bijection.
Subsequent splitting/grouping still requires actual summability. -/
theorem actualCompactPoincare_eq_indexed (N : ℕ) (m : ℤ)
    (ψ : ℝ → ℂ) (z : UpperHalfPlane) :
    actualCompactPoincare N m ψ z =
      ∑' i : NormalRowIndex N, indexedCompactSeed N m ψ z i := by
  exact ((parabolicNormalIndexEquiv N).symm.tsum_eq (compactCosetSeed N m ψ z)).symm

end ImbalancedChen.Part3.CompactParabolicNormalIndex20261025a
