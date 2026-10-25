import ImbalancedChen.Part3Gamma0ParabolicBottomRow
import ImbalancedChen.Part3CuspKloostermanMatrix
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

A genuine GammaInfinity\Gamma0 dictionary. Every primitive integral row
(c,d) with N|c is completed to an ACTUAL Gamma0(N) matrix from its Bezout
coefficients, using the existing cusp-parameter determinant constructor.
The actual GammaInfinity left-action quotient is bijective to those rows
modulo the simultaneous central sign. Neither surjectivity nor a coset
normalization is supplied as a hypothesis. Periodic cusp seeds descend
through this actual parabolic quotient, without being treated as L1(H).
No half-pair Eisenstein sum identity or spectral assertion is made here.
-/

namespace ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a

noncomputable section

open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.CuspKloostermanMatrixSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a

/-- The actual primitive row condition and the exact level condition. -/
abbrev LevelPrimitiveRow (N : ℕ) :=
  {v : Fin 2 → ℤ // IsCoprime (v 0) (v 1) ∧ (N : ℤ) ∣ v 0}

/-- Bottom rows of actual Gamma0 matrices carry their own determinant
Bezout certificate and their own actual level-divisibility proof. -/
def gamma0BottomRow (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    LevelPrimitiveRow N :=
  ⟨bottomRow (g : SL(2, ℤ)), bottomRow_bezout (g : SL(2, ℤ)),
    (gamma0_mem_iff_level_dvd_c N (g : SL(2, ℤ))).mp g.property⟩

/-- Primitive-row surjectivity is a genuine Bezout construction, not an
assumed completion-to-SL2 or parabolic quotient field. -/
theorem gamma0BottomRow_surjective (N : ℕ) : Function.Surjective (gamma0BottomRow N) := by
  intro v
  obtain ⟨u, w, hbez⟩ := v.property.1
  obtain ⟨k, hk⟩ := v.property.2
  have hparam : w * (v.1 0 + v.1 1) - (N : ℤ) * k * (w - u) = 1 := by
    rw [← hk]
    linear_combination hbez
  let g : SL(2, ℤ) :=
    matrixOfCuspParameters N (v.1 0 + v.1 1) k (w - u) w hparam
  have hg : g ∈ CongruenceSubgroup.Gamma0 N :=
    matrixOfCuspParameters_mem_gamma0 N (v.1 0 + v.1 1) k (w - u) w hparam
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext
  funext j
  fin_cases j <;>
    simp [gamma0BottomRow, bottomRow, g, matrixOfCuspParameters, hk] <;> ring

/-- Simultaneously reversing both primitive row entries is the precise
unoriented-row relation. -/
def signedRowSetoid (N : ℕ) : Setoid (LevelPrimitiveRow N) where
  r v w := v.1 = w.1 ∨ v.1 = -w.1
  iseqv := by
    refine ⟨fun v => Or.inl rfl, ?_, ?_⟩
    · intro v w hvw
      rcases hvw with h | h
      · exact Or.inl h.symm
      · right
        have hn := congrArg (fun a : Fin 2 → ℤ => -a) h
        simpa only [neg_neg] using hn.symm
    · intro v w u hvw hwu
      rcases hvw with hvw | hvw <;> rcases hwu with hwu | hwu
      · exact Or.inl (hvw.trans hwu)
      · exact Or.inr (hvw.trans hwu)
      · exact Or.inr (hvw.trans (congrArg (fun a : Fin 2 → ℤ => -a) hwu))
      · left
        rw [hvw, hwu, neg_neg]

abbrev SignedPrimitiveRows (N : ℕ) := Quotient (signedRowSetoid N)

/-- This is the genuine NONNORMAL parabolic left-action quotient. -/
abbrev GammaInfinityCosets (N : ℕ) :=
  Quotient (MulAction.orbitRel (gammaInfinity N) (CongruenceSubgroup.Gamma0 N))

def bottomRowClass (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) : SignedPrimitiveRows N :=
  Quotient.mk'' (gamma0BottomRow N g)

/-- Actual left action by GammaInfinity is equivalent to the literal
relative-matrix subgroup condition. -/
theorem parabolic_orbit_iff_relative (N : ℕ)
    (g h : CongruenceSubgroup.Gamma0 N) :
    MulAction.orbitRel (gammaInfinity N) (CongruenceSubgroup.Gamma0 N) g h ↔
      g * h⁻¹ ∈ gammaInfinity N := by
  constructor
  · intro hrel
    obtain ⟨η, hη⟩ := MulAction.orbitRel_apply.mp hrel
    rw [← hη]
    change (((η : CongruenceSubgroup.Gamma0 N) * h) * h⁻¹) ∈ gammaInfinity N
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using η.property
  · intro hrel
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨g * h⁻¹, hrel⟩, ?_⟩
    change (g * h⁻¹) * h = g
    group

/-- Equality of actual signed-row classes is EXACTLY the actual parabolic
left-coset relation. No normality of the stabilizer is assumed. -/
theorem bottomRowClass_eq_iff_orbit (N : ℕ)
    (g h : CongruenceSubgroup.Gamma0 N) :
    bottomRowClass N g = bottomRowClass N h ↔
      MulAction.orbitRel (gammaInfinity N) (CongruenceSubgroup.Gamma0 N) g h := by
  constructor
  · intro hrow
    have hsigned : bottomRow (g : SL(2, ℤ)) = bottomRow (h : SL(2, ℤ)) ∨
        bottomRow (g : SL(2, ℤ)) = -bottomRow (h : SL(2, ℤ)) :=
      Quotient.exact hrow
    exact (parabolic_orbit_iff_relative N g h).mpr
      ((gammaInfinity_left_relation_iff N h g).mpr hsigned)
  · intro horbit
    apply Quotient.sound
    exact (gammaInfinity_left_relation_iff N h g).mp
      ((parabolic_orbit_iff_relative N g h).mp horbit)

/-- The actual bottom-row map on actual parabolic cosets. -/
def parabolicRowMap (N : ℕ) : GammaInfinityCosets N → SignedPrimitiveRows N :=
  Quotient.lift (bottomRowClass N)
    (fun g h hrel => (bottomRowClass_eq_iff_orbit N g h).mpr hrel)

theorem parabolicRowMap_mk (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    parabolicRowMap N (Quotient.mk'' g) = bottomRowClass N g := rfl

theorem parabolicRowMap_injective (N : ℕ) : Function.Injective (parabolicRowMap N) := by
  intro q r hqr
  revert hqr
  refine Quotient.inductionOn₂ q r ?_
  intro g h hqr
  exact Quotient.sound ((bottomRowClass_eq_iff_orbit N g h).mp hqr)

theorem parabolicRowMap_surjective (N : ℕ) : Function.Surjective (parabolicRowMap N) := by
  intro v
  refine Quotient.inductionOn v ?_
  intro w
  obtain ⟨g, hg⟩ := gamma0BottomRow_surjective N w
  refine ⟨Quotient.mk'' g, ?_⟩
  change Quotient.mk'' (gamma0BottomRow N g) = Quotient.mk'' w
  rw [hg]

/-- Actual GammaInfinity\Gamma0 is in bijection with primitive integral
bottom rows satisfying N|c, modulo their simultaneous central sign. -/
def parabolicPrimitiveRowEquiv (N : ℕ) :
    GammaInfinityCosets N ≃ SignedPrimitiveRows N :=
  Equiv.ofBijective (parabolicRowMap N)
    ⟨parabolicRowMap_injective N, parabolicRowMap_surjective N⟩

/-- A periodic seed descends through the ACTUAL parabolic quotient; no
full-Gamma0 L1 statement or assumed quotient dictionary is used. -/
def periodicSeedOnCosets {A : Type*} (N : ℕ)
    (F : UpperHalfPlane → A)
    (hperiod : ∀ k : ℤ, ∀ z : UpperHalfPlane, F ((k : ℝ) +ᵥ z) = F z)
    (z : UpperHalfPlane) : GammaInfinityCosets N → A :=
  Quotient.lift (fun g : CongruenceSubgroup.Gamma0 N => F (g • z))
    (fun g h hrel => periodic_seed_representative_independence N F hperiod h g
      ((parabolic_orbit_iff_relative N g h).mp hrel) z)

theorem periodicSeedOnCosets_mk {A : Type*} (N : ℕ)
    (F : UpperHalfPlane → A)
    (hperiod : ∀ k : ℤ, ∀ z : UpperHalfPlane, F ((k : ℝ) +ᵥ z) = F z)
    (z : UpperHalfPlane) (g : CongruenceSubgroup.Gamma0 N) :
    periodicSeedOnCosets N F hperiod z (Quotient.mk'' g) = F (g • z) := rfl

end
end ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a