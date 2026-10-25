import ImbalancedChen.Part3ActualEisensteinFourierInterchange
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual coprime integer second coordinate at each positive first
coordinate c is bijective to an ACTUAL unit residue of ZMod c times an
integer translate. The map is literally (u,k) -> val(u)+c*k; injection
and surjection are proved, including modulus one. At a true level N|c
this reindexes the genuine primitive-row seed sum, with summability
derived from the original seed series. The literal seed is factored by
c^(-2s), and the integer translates become the existing power-seed
periodization. No residue dictionary or periodization is assumed.
-/

namespace ImbalancedChen.Part3.ActualEisensteinPrimitiveResidues20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PowerSeedGaussianLaplace
open ImbalancedChen.Part3.PowerSeedPeriodization
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a

abbrev CoprimeD (c : ℕ) := {d : ℤ // IsCoprime (c : ℤ) d}

/-- The literal unit residue plus integer translate is coprime to c. -/
def unitTranslateLift (c : ℕ) [NeZero c] (p : (ZMod c)ˣ × ℤ) : CoprimeD c :=
  ⟨((p.1 : ZMod c).val : ℤ) + (c : ℤ) * p.2, by
    apply (ZMod.coe_int_isUnit_iff_isCoprime _ c).mp
    have hcast :
        ((((p.1 : ZMod c).val : ℤ) + (c : ℤ) * p.2 : ℤ) : ZMod c) = p.1 := by
      simp
    rw [hcast]
    exact p.1.isUnit⟩

theorem unitTranslateLift_injective (c : ℕ) [NeZero c] :
    Function.Injective (unitTranslateLift c) := by
  intro p q hpq
  have hraw : ((p.1 : ZMod c).val : ℤ) + (c : ℤ) * p.2 =
      ((q.1 : ZMod c).val : ℤ) + (c : ℤ) * q.2 := congrArg Subtype.val hpq
  have hu : (p.1 : ZMod c) = q.1 := by
    have h := congrArg (fun d : ℤ => (d : ZMod c)) hraw
    simpa using h
  have hunit : p.1 = q.1 := Units.ext hu
  have hc : (c : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne c
  rw [hunit] at hraw
  have hk : p.2 = q.2 := mul_left_cancel₀ hc (add_left_cancel hraw)
  exact Prod.ext hunit hk

theorem unitTranslateLift_surjective (c : ℕ) [NeZero c] :
    Function.Surjective (unitTranslateLift c) := by
  intro d
  have hunit : IsUnit (d.1 : ZMod c) :=
    (ZMod.coe_int_isUnit_iff_isCoprime d.1 c).mpr d.property
  let u : (ZMod c)ˣ := hunit.unit
  have hcast : (d.1 : ZMod c) = u := hunit.unit_spec.symm
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_iff c d.1 (u : ZMod c)).mp hcast
  refine ⟨(u, k), ?_⟩
  apply Subtype.ext
  exact hk.symm

def unitTranslateEquiv (c : ℕ) [NeZero c] : (ZMod c)ˣ × ℤ ≃ CoprimeD c :=
  Equiv.ofBijective (unitTranslateLift c)
    ⟨unitTranslateLift_injective c, unitTranslateLift_surjective c⟩

/-- The true level condition is attached to each primitive second-coordinate
index; it is not dropped from the actual Eisenstein row sum. -/
def primitiveDLevelEquiv (N c : ℕ) (hNc : (N : ℤ) ∣ (c : ℤ)) :
    CoprimeD c ≃ PrimitiveD N (c : ℤ) where
  toFun d := ⟨d.1, d.property, hNc⟩
  invFun d := ⟨d.1, d.property.1⟩
  left_inv d := by apply Subtype.ext; rfl
  right_inv d := by apply Subtype.ext; rfl

def primitiveDUnitTranslateEquiv (N c : ℕ) [NeZero c]
    (hNc : (N : ℤ) ∣ (c : ℤ)) : (ZMod c)ˣ × ℤ ≃ PrimitiveD N (c : ℤ) :=
  (unitTranslateEquiv c).trans (primitiveDLevelEquiv N c hNc)

theorem primitiveDUnitTranslateEquiv_value (N c : ℕ) [NeZero c]
    (hNc : (N : ℤ) ∣ (c : ℤ)) (p : (ZMod c)ˣ × ℤ) :
    (primitiveDUnitTranslateEquiv N c hNc p).1 =
      ((p.1 : ZMod c).val : ℤ) + (c : ℤ) * p.2 := rfl

/-- At every actual positive c and actual allowed level, the primitive
second-coordinate seed series is absolutely summable. -/
theorem fixed_first_seed_summable (N c : ℕ) [NeZero c]
    (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    Summable (fun d : PrimitiveD N (c : ℤ) => seed s z ![(c : ℤ), d.1]) := by
  apply (seed_summable s hs z).comp_injective
  intro d e h
  apply Subtype.ext
  exact congrFun h 1

/-- The actual primitive integer sum is reindexed by all unit residues and
all integer translates before any Fourier or Gamma/K evaluation. -/
theorem fixed_first_seed_eq_unit_translates (N c : ℕ) [NeZero c]
    (hNc : (N : ℤ) ∣ (c : ℤ)) (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    (∑' d : PrimitiveD N (c : ℤ), seed s z ![(c : ℤ), d.1]) =
      ∑ u : (ZMod c)ˣ, ∑' k : ℤ,
        seed s z ![(c : ℤ), ((u : ZMod c).val : ℤ) + (c : ℤ) * k] := by
  let e := primitiveDUnitTranslateEquiv N c hNc
  have hsum := e.summable_iff.mpr (fixed_first_seed_summable N c s hs z)
  calc
    _ = ∑' p : (ZMod c)ˣ × ℤ,
        seed s z ![(c : ℤ), ((p.1 : ZMod c).val : ℤ) + (c : ℤ) * p.2] :=
      (e.tsum_eq _).symm
    _ = _ := by rw [hsum.tsum_prod, tsum_fintype]

/-- Exact c^(-2s) factorization of the literal primitive-row seed at a
horizontal point. The factor is proved from the actual complex linear form. -/
theorem seed_positive_first_eq_powerSeed (c : ℕ) [NeZero c]
    (s y : ℝ) (hy : 0 < y) (d : ℤ) (x : ℝ) :
    seed s (horizontalPoint y hy x) ![(c : ℤ), d] =
      (c : ℝ) ^ (-(2 * s)) * powerSeed s y (x + (d : ℝ) / (c : ℝ)) := by
  have hc : 0 < (c : ℝ) := by exact_mod_cast NeZero.pos c
  let w := horizontalPoint y hy (x + (d : ℝ) / (c : ℝ))
  have hlinear : (c : ℂ) * (horizontalPoint y hy x : ℂ) + (d : ℂ) =
      (c : ℂ) * (w : ℂ) := by
    apply Complex.ext <;>
      simp [horizontalPoint, w, Complex.mul_re, Complex.mul_im] <;>
      field_simp [hc.ne'] <;> ring
  have hnorm : ‖(c : ℂ) * (horizontalPoint y hy x : ℂ) + (d : ℂ)‖ =
      (c : ℝ) * ‖(w : ℂ)‖ := by
    rw [hlinear, norm_mul]
    simp
  have hw2 : ‖(w : ℂ)‖ ^ 2 = (x + (d : ℝ) / (c : ℝ)) ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, horizontalPoint, w]
  have hpow : ‖(w : ℂ)‖ ^ (2 * s) =
      ((x + (d : ℝ) / (c : ℝ)) ^ 2 + y ^ 2) ^ s := by
    calc
      _ = (‖(w : ℂ)‖ ^ (2 : ℝ)) ^ s := Real.rpow_mul (norm_nonneg _) 2 s
      _ = _ := by rw [Real.rpow_two, hw2]
  have hseed : seed s (horizontalPoint y hy x) ![(c : ℤ), d] =
      y ^ s / ‖(c : ℂ) * (horizontalPoint y hy x : ℂ) + (d : ℂ)‖ ^ (2 * s) := by
    simp [seed_eq_quotient, horizontalPoint]
  rw [hseed, hnorm, Real.mul_rpow hc.le (norm_nonneg _), hpow,
    Real.rpow_neg hc.le]
  unfold powerSeed
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Full primitive-d periodization at a fixed actual positive c. This is
the real c-row block of the original Eisenstein series, not a single-seed
coefficient in isolation. -/
theorem fixed_first_seed_eq_unit_periodization (N c : ℕ) [NeZero c]
    (hNc : (N : ℤ) ∣ (c : ℤ)) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    (∑' d : PrimitiveD N (c : ℤ), seed s (horizontalPoint y hy x) ![(c : ℤ), d.1]) =
      (c : ℝ) ^ (-(2 * s)) *
        ∑ u : (ZMod c)ˣ,
          periodizedPowerSeed s y (x + ((u : ZMod c).val : ℝ) / (c : ℝ)) := by
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have harg (u : (ZMod c)ˣ) (k : ℤ) :
      x + ((((u : ZMod c).val : ℤ) + (c : ℤ) * k : ℤ) : ℝ) / (c : ℝ) =
        (x + ((u : ZMod c).val : ℝ) / (c : ℝ)) + (k : ℝ) := by
    push_cast
    field_simp [hc] <;> ring
  rw [fixed_first_seed_eq_unit_translates N c hNc s hs]
  simp_rw [seed_positive_first_eq_powerSeed c s y hy, harg, tsum_mul_left]
  simp only [periodizedPowerSeed, Finset.mul_sum]

end
end ImbalancedChen.Part3.ActualEisensteinPrimitiveResidues20261025a