import ImbalancedChen.Part3InfinityZeroBruhatSeed
import ImbalancedChen.Part3Gamma0ParabolicCosetRows

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

An original GammaInfinity-left-coset fiber, not a replacement canonical
series, is parametrized by actual zero-cusp residues and actual integral
right-parabolic translates. Positive d eliminates the central sign. The
integer parameter is k=val(r)-d*v, so the normalized right translation
has period one, with no extra N or sqrt(N) in its period.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.InfinityZeroActualDenominatorFiber20261026a

open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a

abbrev ZeroPrimitiveK (N d : ℕ) :=
  {k : ℤ // IsUnit ((N : ZMod d) * (k : ZMod d))}

def residueTranslateLift (N d : ℕ) [NeZero d]
    (p : ZeroResidue N d × ℤ) : ZeroPrimitiveK N d :=
  ⟨(p.1.1.val : ℤ) - (d : ℤ) * p.2, by
    have hcast : (((p.1.1.val : ℤ) - (d : ℤ) * p.2 : ℤ) : ZMod d) = p.1.1 := by
      simp
    rw [hcast]
    exact p.1.property⟩

theorem residueTranslateLift_injective (N d : ℕ) [NeZero d] :
    Function.Injective (residueTranslateLift N d) := by
  intro p q hpq
  have hraw : (p.1.1.val : ℤ) - (d : ℤ) * p.2 =
      (q.1.1.val : ℤ) - (d : ℤ) * q.2 := congrArg Subtype.val hpq
  have hr : p.1 = q.1 := by
    apply Subtype.ext
    have h := congrArg (fun k : ℤ => (k : ZMod d)) hraw
    simpa using h
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [hr] at hraw
  have hm : (d : ℤ) * p.2 = (d : ℤ) * q.2 := by linarith
  have hv : p.2 = q.2 := mul_left_cancel₀ hd hm
  exact Prod.ext hr hv

theorem residueTranslateLift_surjective (N d : ℕ) [NeZero d] :
    Function.Surjective (residueTranslateLift N d) := by
  intro k
  let r : ZeroResidue N d := ⟨(k.1 : ZMod d), k.property⟩
  obtain ⟨v, hv⟩ := (ZMod.intCast_eq_iff d k.1 r.1).mp (by rfl)
  refine ⟨(r, -v), ?_⟩
  apply Subtype.ext
  change (r.1.val : ℤ) - (d : ℤ) * -v = k.1
  rw [hv]
  ring

def residueTranslateEquiv (N d : ℕ) [NeZero d] :
    ZeroResidue N d × ℤ ≃ ZeroPrimitiveK N d :=
  Equiv.ofBijective (residueTranslateLift N d)
    ⟨residueTranslateLift_injective N d, residueTranslateLift_surjective N d⟩

/-- The actual matrix representing the residue and its zero-cusp translation. -/
def zeroPairMatrix (N d : ℕ) [NeZero d] (p : ZeroResidue N d × ℤ) : SL(2, ℤ) :=
  zeroCanonicalMatrix N d p.1 * zeroParabolic N p.2

theorem zeroPairMatrix_entries (N d : ℕ) [NeZero d] (p : ZeroResidue N d × ℤ) :
    zeroPairMatrix N d p 1 0 = (N : ℤ) * ((p.1.1.val : ℤ) - (d : ℤ) * p.2) ∧
    zeroPairMatrix N d p 1 1 = (d : ℤ) ∧
    zeroPairMatrix N d p 0 1 = canonicalB N d p.1.1 := by
  simp [zeroPairMatrix, zeroCanonicalMatrix, zeroParabolic, coe_mul, Matrix.mul_fin_two]
  ring

def zeroPairGamma (N d : ℕ) [NeZero d] (p : ZeroResidue N d × ℤ) :
    CongruenceSubgroup.Gamma0 N :=
  ⟨zeroPairMatrix N d p,
    mul_mem (zeroCanonicalMatrix_mem_gamma0 N d p.1) (zeroParabolic_mem_gamma0 N p.2)⟩

/-- This subtype is a fiber of the ORIGINAL actual parabolic quotient.
The denominator condition is existential on an actual representative. -/
abbrev ZeroDenominatorCosets (N d : ℕ) :=
  {q : GammaInfinityCosets N // ∃ g : CongruenceSubgroup.Gamma0 N,
    Quotient.mk'' g = q ∧ (g : SL(2, ℤ)) 1 1 = (d : ℤ)}

def zeroPairCoset (N d : ℕ) [NeZero d] (p : ZeroResidue N d × ℤ) :
    ZeroDenominatorCosets N d :=
  ⟨Quotient.mk'' (zeroPairGamma N d p),
    zeroPairGamma N d p, rfl, (zeroPairMatrix_entries N d p).2.1⟩

/-- No central +/- duplication survives at positive lower-right d. -/
theorem zeroPairCoset_injective (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d] :
    Function.Injective (zeroPairCoset N d) := by
  intro p q hpq
  have hcoset := congrArg Subtype.val hpq
  have hrow := congrArg (parabolicRowMap N) hcoset
  change bottomRowClass N (zeroPairGamma N d p) =
    bottomRowClass N (zeroPairGamma N d q) at hrow
  have hsigned : bottomRow (zeroPairMatrix N d p) = bottomRow (zeroPairMatrix N d q) ∨
      bottomRow (zeroPairMatrix N d p) = -bottomRow (zeroPairMatrix N d q) :=
    Quotient.exact hrow
  rcases hsigned with heq | hneg
  · apply residueTranslateLift_injective N d
    apply Subtype.ext
    have h0 := congrFun heq 0
    change zeroPairMatrix N d p 1 0 = zeroPairMatrix N d q 1 0 at h0
    rw [(zeroPairMatrix_entries N d p).1, (zeroPairMatrix_entries N d q).1] at h0
    exact mul_left_cancel₀ (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0) h0
  · have h1 := congrFun hneg 1
    change zeroPairMatrix N d p 1 1 = -zeroPairMatrix N d q 1 1 at h1
    rw [(zeroPairMatrix_entries N d p).2.1, (zeroPairMatrix_entries N d q).2.1] at h1
    have hdpos : (0 : ℤ) < d := by exact_mod_cast NeZero.pos d
    omega

theorem zeroPairCoset_surjective (N : ℕ) (d : ℕ) [NeZero d] :
    Function.Surjective (zeroPairCoset N d) := by
  intro q
  obtain ⟨g, hg, hd⟩ := q.property
  obtain ⟨k, hk⟩ := (gamma0_mem_iff_level_dvd_c N (g : SL(2, ℤ))).mp g.property
  have hunit : IsUnit ((N : ZMod d) * (k : ZMod d)) :=
    zero_actual_residue_isUnit N d (g : SL(2, ℤ)) k hk hd
  obtain ⟨p, hp⟩ := residueTranslateLift_surjective N d ⟨k, hunit⟩
  have hraw : (p.1.1.val : ℤ) - (d : ℤ) * p.2 = k := congrArg Subtype.val hp
  have hbottom : bottomRow (zeroPairMatrix N d p) = bottomRow (g : SL(2, ℤ)) := by
    funext j
    fin_cases j
    · change zeroPairMatrix N d p 1 0 = (g : SL(2, ℤ)) 1 0
      rw [(zeroPairMatrix_entries N d p).1, hraw, hk]
    · change zeroPairMatrix N d p 1 1 = (g : SL(2, ℤ)) 1 1
      rw [(zeroPairMatrix_entries N d p).2.1, hd]
  have hclass : bottomRowClass N (zeroPairGamma N d p) = bottomRowClass N g :=
    Quotient.sound (Or.inl hbottom)
  have horbit := (bottomRowClass_eq_iff_orbit N (zeroPairGamma N d p) g).mp hclass
  refine ⟨p, Subtype.ext ?_⟩
  exact (Quotient.sound horbit).trans hg

/-- A proved actual mixed-cusp fiber equivalence, including N=1 and d=1. -/
def zeroDenominatorCosetEquiv (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d] :
    ZeroResidue N d × ℤ ≃ ZeroDenominatorCosets N d :=
  Equiv.ofBijective (zeroPairCoset N d)
    ⟨zeroPairCoset_injective N hN d, zeroPairCoset_surjective N d⟩

end ImbalancedChen.Part3.InfinityZeroActualDenominatorFiber20261026a
