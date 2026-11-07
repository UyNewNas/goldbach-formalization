import ImbalancedChen.Part3CompactParabolicNormalIndex
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The ORIGINAL actual GammaInfinity\Gamma0 compact Fourier-radial Poincare
sum is reindexed by the proved actual normal-form equivalence, with actual
summability supplied before grouping. Its c=0 contribution is the seed
once; each positive-c primitive fiber is the actual canonical section via
the existing P0 unit/translate equivalence. The previously proved concrete
uniform cutoff then gives the full geometric finite Kloosterman Fourier
expansion. No Bessel evaluation or spectral/Kuznetsov identity is asserted.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.ActualCompactPoincareFourier20261025a

open Set MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators FourierTransform
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a (PrimitiveD)
open ImbalancedChen.Part3.ActualEisensteinPrimitiveResidues20261025a
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open ImbalancedChen.Part3.ActualCompactBruhatAllModuli20261025a
open ImbalancedChen.Part3.CompactParabolicNormalIndex20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly

/-- The existing unit-group index and actual unit-residue subtype agree. -/
def unitsUnitResidueEquiv (c : ℕ) : (ZMod c)ˣ ≃ UnitResidue c where
  toFun u := ⟨(u : ZMod c), u.isUnit⟩
  invFun u := u.2.unit
  left_inv u := Units.ext u.isUnit.unit_spec
  right_inv u := Subtype.ext u.2.unit_spec

/-- Pointwise translate summability is inherited from the proved local
norm summability of the actual compact kernel. -/
theorem kernel_translates_summable (c : ℝ) (hc : c ≠ 0) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ)
    (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    Summable (fun k : ℤ => actualKernel c hc y hy m ψ (x + (k : ℝ))) := by
  have hm := ContinuousMap.summable_of_locally_summable_norm
    (actualKernel_translates_locally_summable c hc y hy m ψ hψ hcompact hpositive)
  simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
    actualKernelMap, ContinuousMap.coe_mk] using
      (ContinuousMap.hasSum_apply hm.hasSum x).summable

/-- Actual original coset values on each unit/translate normal class are
the actual compact Weyl kernel with its actual upper-left phase. -/
theorem indexedSeed_unit_kernel (N : ℕ) (c : ℕ+)
    (hNc : (N : ℤ) ∣ ((c : ℕ) : ℤ)) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (x : ℝ) (u : (ZMod (c : ℕ))ˣ) (k : ℤ) :
    indexedCompactSeed N m ψ (horizontalPoint y hy x)
      (Sum.inr ⟨c, primitiveDUnitTranslateEquiv N (c : ℕ) hNc (u, k)⟩) =
      AddCircle.fourier m
        (((upperRepresentative (c : ℕ) ⟨(u : ZMod (c : ℕ)), u.isUnit⟩ : ℤ) : ℝ) /
          (c : ℝ) : UnitAddCircle) *
      actualKernel (c : ℝ) (by exact_mod_cast (Nat.ne_of_gt c.property)) y hy m ψ
        ((x + ((u : ZMod (c : ℕ)).val : ℝ) / (c : ℝ)) + (k : ℝ)) := by
  let U : UnitResidue (c : ℕ) := ⟨(u : ZMod (c : ℕ)), u.isUnit⟩
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt c.property)
  rw [indexedCompactSeed_unit_translate, mul_smul, UpperHalfPlane.modular_T_zpow_smul]
  have hb := fourierRadialSeed_actual_bruhat m ψ (canonicalMatrix (c : ℕ) U)
    (by simpa only [canonicalMatrix, Int.cast_natCast] using hc)
    ((k : ℝ) +ᵥ horizontalPoint y hy x)
  have hpoint :
      ((lowerRepresentative (c : ℕ) U : ℝ) / (c : ℝ)) +ᵥ
        ((k : ℝ) +ᵥ horizontalPoint y hy x) =
      horizontalPoint y hy
        ((x + ((u : ZMod (c : ℕ)).val : ℝ) / (c : ℝ)) + (k : ℝ)) := by
    apply UpperHalfPlane.ext
    ext <;> simp [horizontalPoint, lowerRepresentative, U, UpperHalfPlane.coe_vadd] <;> ring
  change fourierRadialSeed m ψ
      (canonicalMatrix (c : ℕ) U • ((k : ℝ) +ᵥ horizontalPoint y hy x)) = _
  rw [hb]
  change _ * fourierRadialSeed m ψ
    (scaledWeyl (c : ℝ) hc •
      (((lowerRepresentative (c : ℕ) U : ℝ) / (c : ℝ)) +ᵥ
        ((k : ℝ) +ᵥ horizontalPoint y hy x))) = _
  rw [hpoint]
  rfl

/-- Actual positive primitive fibers are absolutely summable, obtained
from the genuine unit/translate bijection and actual compact kernels. -/
theorem indexed_positive_fiber_norm_summable (N : ℕ) (c : ℕ+)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    Summable (fun d : PrimitiveD N ((c : ℕ) : ℤ) =>
      ‖indexedCompactSeed N m ψ (horizontalPoint y hy x) (Sum.inr ⟨c, d⟩)‖) := by
  by_cases hNc : (N : ℤ) ∣ ((c : ℕ) : ℤ)
  · apply (primitiveDUnitTranslateEquiv N (c : ℕ) hNc).summable_iff.mp
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    refine ⟨?_, summable_fintype _⟩
    intro u
    simp_rw [indexedSeed_unit_kernel]
    simp only [norm_mul]
    exact (kernel_translates_summable (c : ℝ)
      (by exact_mod_cast (Nat.ne_of_gt c.property)) y hy m ψ hψ hcompact hpositive
      (x + ((u : ZMod (c : ℕ)).val : ℝ) / (c : ℝ))).norm.mul_left _
  · letI : IsEmpty (PrimitiveD N ((c : ℕ) : ℤ)) := ⟨fun d => hNc d.property.2⟩
    exact summable_empty

/-- The actual original positive-index values satisfy the same proved
uniform modulus cutoff, before any sigma grouping is performed. -/
theorem indexed_positive_zero_of_large (N : ℕ) (c : ℕ+)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (x : ℝ)
    (a : ℝ) (ha : 0 < a) (hfloor : ∀ t : ℝ, ψ t ≠ 0 → a ≤ t)
    (hlarge : 1 < a * (c : ℝ) ^ 2 * y) (d : PrimitiveD N ((c : ℕ) : ℤ)) :
    indexedCompactSeed N m ψ (horizontalPoint y hy x) (Sum.inr ⟨c, d⟩) = 0 := by
  obtain ⟨⟨u, k⟩, rfl⟩ :=
    (primitiveDUnitTranslateEquiv N (c : ℕ) d.property.2).surjective d
  rw [indexedSeed_unit_kernel,
    actualKernel_zero_of_large_modulus _ _ y hy m ψ a ha hfloor hlarge, mul_zero]

/-- Absolute summability of the ORIGINAL positive normal-index series.
Both the fiber convergence and the finite c cutoff are concrete theorems. -/
theorem indexed_positive_sigma_norm_summable (N : ℕ) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ)
    (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    Summable (fun p : PositiveRowIndex N =>
      ‖indexedCompactSeed N m ψ (horizontalPoint y hy x) (Sum.inr p)‖) := by
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun c => indexed_positive_fiber_norm_summable N c y hy m ψ hψ hcompact hpositive x, ?_⟩
  obtain ⟨a, ha, hfloor⟩ := radial_support_positive_floor ψ hcompact hpositive
  obtain ⟨C, hC⟩ := exists_positive_modulus_cutoff a y ha hy
  apply summable_of_ne_finset_zero (s := Finset.Icc (1 : ℕ+) C)
  intro c hc
  have hcone : (1 : ℕ+) ≤ c := by change 1 ≤ (c : ℕ); exact c.property
  have hcc : C < c := lt_of_not_ge (fun hle => hc (Finset.mem_Icc.mpr ⟨hcone, hle⟩))
  have hz := indexed_positive_zero_of_large N c y hy m ψ x a ha hfloor
    (large_modulus_of_cutoff a y ha hy C c hC hcc)
  simp only [hz, norm_zero, tsum_zero]

private theorem canonicalFiniteSection_eq_units (c : ℕ) [NeZero c] (m : ℤ)
    (F : UnitAddCircle → ℂ) (x : ℝ) :
    canonicalFiniteSection c m F (x : UnitAddCircle) =
      ∑ u : (ZMod c)ˣ,
        AddCircle.fourier m
          (((upperRepresentative c ⟨(u : ZMod c), u.isUnit⟩ : ℤ) : ℝ) /
            (c : ℝ) : UnitAddCircle) *
        F (((x + ((u : ZMod c).val : ℝ) / (c : ℝ)) : ℝ) : UnitAddCircle) := by
  simp only [canonicalFiniteSection, Finset.sum_apply,
    P3CuspTranslationFourierPhaseSourceOnly.translated, canonicalMatrix,
    lowerRepresentative, Int.cast_natCast, ← AddCircle.coe_add]
  exact (Fintype.sum_equiv (unitsUnitResidueEquiv c) _ _ (fun _ => rfl)).symm

/-- The sum over each ORIGINAL actual positive-c primitive fiber equals
the concrete canonical section, by the existing unit/translate equivalence. -/
theorem indexed_positive_fiber_eq_section (N : ℕ) (c : ℕ+)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    (∑' d : PrimitiveD N ((c : ℕ) : ℤ),
      indexedCompactSeed N m ψ (horizontalPoint y hy x) (Sum.inr ⟨c, d⟩)) =
      positiveModulusSection N c y hy m ψ hψ (x : UnitAddCircle) := by
  by_cases hNcNat : N ∣ (c : ℕ)
  · have hNc : (N : ℤ) ∣ ((c : ℕ) : ℤ) := by exact_mod_cast hNcNat
    let e := primitiveDUnitTranslateEquiv N (c : ℕ) hNc
    have hsum := e.summable_iff.mpr
      (indexed_positive_fiber_norm_summable N c y hy m ψ hψ hcompact hpositive x).of_norm
    rw [← e.tsum_eq, hsum.tsum_prod, tsum_fintype]
    simp_rw [indexedSeed_unit_kernel, tsum_mul_left]
    simp_rw [← periodizedKernelCircle_coe (c : ℝ)
      (by exact_mod_cast (Nat.ne_of_gt c.property)) y hy m ψ hψ hcompact hpositive]
    unfold positiveModulusSection
    rw [if_pos hNcNat, canonicalFiniteSection_eq_units]
  · have hNc : ¬ (N : ℤ) ∣ ((c : ℕ) : ℤ) := by
      exact fun h => hNcNat (by exact_mod_cast h)
    letI : IsEmpty (PrimitiveD N ((c : ℕ) : ℤ)) := ⟨fun d => hNc d.property.2⟩
    simp [positiveModulusSection, hNcNat]

/-- The ORIGINAL actual coset series is absolutely summable. This is
transported through the proved actual quotient bijection from the genuine
compact-kernel fiber convergence and the genuine common c cutoff. -/
theorem actualCompactPoincare_norm_summable (N : ℕ) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ)
    (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    Summable (fun q : GammaInfinityCosets N =>
      ‖compactCosetSeed N m ψ (horizontalPoint y hy x) q‖) := by
  apply (parabolicNormalIndexEquiv N).symm.summable_iff.mp
  have hzero : Summable (fun u : Unit =>
      ‖indexedCompactSeed N m ψ (horizontalPoint y hy x) (Sum.inl u)‖) := summable_fintype _
  have hpos := indexed_positive_sigma_norm_summable N y hy m ψ hψ hcompact hpositive x
  exact Summable.sum _ hzero hpos
/-- THE ORIGINAL actual compact parabolic Poincare sum equals the single
original seed plus the level-gated positive-modulus canonical sections.
Every reindexing and series grouping is justified above. -/
theorem actualCompactPoincare_eq_seed_add_sections (N : ℕ) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ)
    (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    actualCompactPoincare N m ψ (horizontalPoint y hy x) =
      fourierRadialSeed m ψ (horizontalPoint y hy x) +
        allPositiveModulusSections N y hy m ψ hψ (x : UnitAddCircle) := by
  have hpos := (indexed_positive_sigma_norm_summable N y hy m ψ hψ hcompact hpositive x).of_norm
  have hzero : Summable (fun u : Unit =>
      indexedCompactSeed N m ψ (horizontalPoint y hy x) (Sum.inl u)) := summable_fintype _
  rw [actualCompactPoincare_eq_indexed, hzero.tsum_sum hpos]
  simp only [tsum_fintype, Fintype.sum_unique, indexedCompactSeed_zero]
  rw [hpos.tsum_sigma]
  simp_rw [indexed_positive_fiber_eq_section N _ y hy m ψ hψ hcompact hpositive x]
  rfl

/-- The Fourier coefficient is defined directly from the ORIGINAL coset
Poincare sum on the actual horizontal period. -/
def actualCompactPoincareFourier (N : ℕ) (y : ℝ) (hy : 0 < y)
    (m n : ℤ) (ψ : ℝ → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    AddCircle.fourier (-n) (x : UnitAddCircle) *
      actualCompactPoincare N m ψ (horizontalPoint y hy x)

private def seedCircle (y : ℝ) (m : ℤ) (ψ : ℝ → ℂ) (x : UnitAddCircle) : ℂ :=
  AddCircle.fourier m x * ψ y

private theorem seedCircle_integrable (y : ℝ) (m : ℤ) (ψ : ℝ → ℂ) :
    Integrable (seedCircle y m ψ) AddCircle.haarAddCircle := by
  have hc : Continuous (seedCircle y m ψ) :=
    (map_continuous (AddCircle.fourier m)).mul continuous_const
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem seedCircle_fourierCoeff (y : ℝ) (m n : ℤ) (ψ : ℝ → ℂ) :
    AddCircle.fourierCoeff (seedCircle y m ψ) n = if n = m then ψ y else 0 := by
  have heq : seedCircle y m ψ = fun x : UnitAddCircle => ψ y * AddCircle.fourier m x := by
    funext x
    exact mul_comm _ _
  rw [heq, AddCircle.fourierCoeff.const_mul, AddCircle.fourierCoeff_fourier]
  by_cases hnm : n = m <;> simp [Pi.single_apply, hnm, eq_comm]

/-- Full geometric Fourier/Kloosterman expansion of the ORIGINAL actual
compact cusp Poincare series. The zero-modulus contribution is exactly
its seed mode, and all positive moduli form a proved finite sum. -/
theorem actualCompactPoincareFourier_eq_finite_kloosterman (N : ℕ)
    (y : ℝ) (hy : 0 < y) (m n : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ))
    (a : ℝ) (ha : 0 < a) (hfloor : ∀ t : ℝ, ψ t ≠ 0 → a ≤ t)
    (C : ℕ+) (hC : 1 / (a * y) < (C : ℝ)) :
    actualCompactPoincareFourier N y hy m n ψ =
      (if n = m then ψ y else 0) +
      ∑ c ∈ Finset.Icc (1 : ℕ+) C,
        if N ∣ (c : ℕ) then
          kloosterman (c : ℕ) n m *
            𝓕 (actualKernel (c : ℝ) (by exact_mod_cast (Nat.ne_of_gt c.property))
              y hy m ψ) (n : ℝ)
        else 0 := by
  have hcircle : actualCompactPoincareFourier N y hy m n ψ =
      AddCircle.fourierCoeff
        (seedCircle y m ψ + allPositiveModulusSections N y hy m ψ hψ) n := by
    rw [AddCircle.fourierCoeff_eq_intervalIntegral _ n 0]
    simp only [div_one, one_smul, zero_add, smul_eq_mul]
    unfold actualCompactPoincareFourier
    apply intervalIntegral.integral_congr
    intro x hx
    rw [actualCompactPoincare_eq_seed_add_sections N y hy m ψ hψ hcompact hpositive x]
    rfl
  rw [hcircle]
  have hadd := congrFun (AddCircle.fourierCoeff.add (seedCircle_integrable y m ψ)
    (allPositiveModulusSections_integrable N y hy m ψ hψ hcompact hpositive)) n
  rw [hadd]
  simp only [Pi.add_apply]
  rw [seedCircle_fourierCoeff, allPositiveModulusSections_fourierCoeff N y hy m n ψ hψ
    hcompact hpositive a ha hfloor C hC]

end ImbalancedChen.Part3.ActualCompactPoincareFourier20261025a

