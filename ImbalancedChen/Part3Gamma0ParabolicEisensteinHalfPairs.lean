import ImbalancedChen.Part3Gamma0ParabolicCosetRows
import ImbalancedChen.Part3PrimitiveRealEisensteinAutomorphy
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The factor 1/2 in the actual parabolic Eisenstein sum is DERIVED. Primitive
level rows have no fixed point under simultaneous negation. Every signed
row fiber is explicitly equivalent to Bool, and summable even seeds have
all-row sum equal to twice the actual GammaInfinity\Gamma0 coset sum.
For the literal real Eisenstein seed this holds at every level N for s>1.
At N=1 the actual parabolic Poincare series is identified with the existing
primitiveEisenstein object, including its previously written factor 1/2.
No hNormalization, assumed fiber size, or full-Gamma L1 substitution occurs.
-/

namespace ImbalancedChen.Part3.Gamma0ParabolicEisensteinHalfPairs20261025a

noncomputable section

open Set Matrix UpperHalfPlane EisensteinSeries
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy

/-- Simultaneous sign reversal preserves the actual primitive level rows. -/
def rowNeg (N : ℕ) (v : LevelPrimitiveRow N) : LevelPrimitiveRow N :=
  ⟨-v.1, by
    constructor
    · obtain ⟨u, w, h⟩ := v.property.1
      refine ⟨-u, -w, ?_⟩
      simpa only [Pi.neg_apply, neg_mul_neg] using h
    · simpa only [Pi.neg_apply, dvd_neg] using v.property.2⟩

theorem rowNeg_ne_self (N : ℕ) (v : LevelPrimitiveRow N) : rowNeg N v ≠ v := by
  intro h
  have hc := congrArg (fun w : LevelPrimitiveRow N => w.1 0) h
  have hd := congrArg (fun w : LevelPrimitiveRow N => w.1 1) h
  change -(v.1 0) = v.1 0 at hc
  change -(v.1 1) = v.1 1 at hd
  have hc0 : v.1 0 = 0 := by omega
  have hd0 : v.1 1 = 0 := by omega
  obtain ⟨u, w, hbez⟩ := v.property.1
  have hbad : (0 : ℤ) = 1 := by simpa only [hc0, hd0, mul_zero, zero_add] using hbez
  norm_num at hbad

def rowProjection (N : ℕ) (v : LevelPrimitiveRow N) : SignedPrimitiveRows N :=
  Quotient.mk'' v

theorem rowProjection_neg (N : ℕ) (v : LevelPrimitiveRow N) :
    rowProjection N (rowNeg N v) = rowProjection N v :=
  Quotient.sound (Or.inr rfl)

def rowRepresentative (N : ℕ) (q : SignedPrimitiveRows N) : LevelPrimitiveRow N :=
  Quotient.out q

theorem rowRepresentative_class (N : ℕ) (q : SignedPrimitiveRows N) :
    rowProjection N (rowRepresentative N q) = q := Quotient.out_eq' q

abbrev RowFiber (N : ℕ) (q : SignedPrimitiveRows N) :=
  {v : LevelPrimitiveRow N // rowProjection N v = q}

/-- The TWO elements in a signed primitive-row fiber, constructed rather
than postulated: the chosen row and its simultaneous negative. -/
def signedFiberParam (N : ℕ) (q : SignedPrimitiveRows N) : Bool → RowFiber N q
  | false => ⟨rowRepresentative N q, rowRepresentative_class N q⟩
  | true => ⟨rowNeg N (rowRepresentative N q),
      (rowProjection_neg N (rowRepresentative N q)).trans (rowRepresentative_class N q)⟩

theorem signedFiberParam_injective (N : ℕ) (q : SignedPrimitiveRows N) :
    Function.Injective (signedFiberParam N q) := by
  intro a b hab
  cases a <;> cases b
  · rfl
  · have h := congrArg (fun v : RowFiber N q => v.1) hab
    exact False.elim (rowNeg_ne_self N (rowRepresentative N q) h.symm)
  · have h := congrArg (fun v : RowFiber N q => v.1) hab
    exact False.elim (rowNeg_ne_self N (rowRepresentative N q) h)
  · rfl

theorem signedFiberParam_surjective (N : ℕ) (q : SignedPrimitiveRows N) :
    Function.Surjective (signedFiberParam N q) := by
  intro v
  have hclass : rowProjection N v.1 = rowProjection N (rowRepresentative N q) :=
    v.property.trans (rowRepresentative_class N q).symm
  have hsign : v.1.1 = (rowRepresentative N q).1 ∨
      v.1.1 = -(rowRepresentative N q).1 := Quotient.exact hclass
  rcases hsign with h | h
  · refine ⟨false, ?_⟩
    apply Subtype.ext
    exact (Subtype.ext h).symm
  · refine ⟨true, ?_⟩
    apply Subtype.ext
    exact (Subtype.ext h).symm

def signedFiberEquiv (N : ℕ) (q : SignedPrimitiveRows N) : Bool ≃ RowFiber N q :=
  Equiv.ofBijective (signedFiberParam N q)
    ⟨signedFiberParam_injective N q, signedFiberParam_surjective N q⟩

theorem signedFiberEquiv_apply (N : ℕ) (q : SignedPrimitiveRows N) (b : Bool) :
    signedFiberEquiv N q b = signedFiberParam N q b := rfl

/-- An even seed descends through the actual simultaneous-sign relation. -/
def signedSeed (N : ℕ) (f : LevelPrimitiveRow N → ℝ)
    (hneg : ∀ v, f (rowNeg N v) = f v) : SignedPrimitiveRows N → ℝ :=
  Quotient.lift f (fun v w h => by
    rcases h with h | h
    · exact congrArg f (Subtype.ext h)
    · have hv : v = rowNeg N w := Subtype.ext h
      rw [hv]
      exact hneg w)

theorem signedSeed_mk (N : ℕ) (f : LevelPrimitiveRow N → ℝ)
    (hneg : ∀ v, f (rowNeg N v) = f v) (v : LevelPrimitiveRow N) :
    signedSeed N f hneg (rowProjection N v) = f v := rfl

theorem signedSeed_representative (N : ℕ) (f : LevelPrimitiveRow N → ℝ)
    (hneg : ∀ v, f (rowNeg N v) = f v) (q : SignedPrimitiveRows N) :
    signedSeed N f hneg q = f (rowRepresentative N q) := by
  rw [← rowRepresentative_class N q]
  rfl

theorem tsum_signed_fiber (N : ℕ) (f : LevelPrimitiveRow N → ℝ)
    (hneg : ∀ v, f (rowNeg N v) = f v) (q : SignedPrimitiveRows N) :
    (∑' v : RowFiber N q, f v.1) = 2 * signedSeed N f hneg q := by
  calc
    _ = ∑' b : Bool, f (signedFiberEquiv N q b).1 :=
      ((signedFiberEquiv N q).tsum_eq (fun v : RowFiber N q => f v.1)).symm
    _ = f (rowRepresentative N q) + f (rowNeg N (rowRepresentative N q)) := by
      simp [tsum_fintype, signedFiberEquiv_apply, signedFiberParam]
    _ = _ := by rw [hneg, signedSeed_representative]; ring

/-- Exact factor-two counting on actual parabolic cosets, proved from the
true two-point fibers and supplied summability of the ORIGINAL row seed. -/
theorem tsum_rows_eq_two_parabolic_cosets (N : ℕ) (f : LevelPrimitiveRow N → ℝ)
    (hneg : ∀ v, f (rowNeg N v) = f v) (hsum : Summable f) :
    (∑' v : LevelPrimitiveRow N, f v) =
      2 * ∑' q : GammaInfinityCosets N,
        signedSeed N f hneg (parabolicPrimitiveRowEquiv N q) := by
  have hgroup : HasSum (fun q : SignedPrimitiveRows N =>
      ∑' v : RowFiber N q, f v.1) (∑' v : LevelPrimitiveRow N, f v) :=
    hsum.hasSum.tsum_fiberwise (rowProjection N)
  have h := hgroup.tsum_eq
  simp_rw [tsum_signed_fiber N f hneg] at h
  rw [tsum_mul_left] at h
  rw [(parabolicPrimitiveRowEquiv N).tsum_eq (signedSeed N f hneg)]
  exact h.symm

/-- Summability also descends through the actual two-point fibers; hence
the quotient sums below do not rely on the default value of a divergent tsum. -/
theorem signedSeed_summable (N : ℕ) (f : LevelPrimitiveRow N → ℝ)
    (hneg : ∀ v, f (rowNeg N v) = f v) (hsum : Summable f) :
    Summable (signedSeed N f hneg) := by
  have hgroup : HasSum (fun q : SignedPrimitiveRows N =>
      ∑' v : RowFiber N q, f v.1) (∑' v : LevelPrimitiveRow N, f v) :=
    hsum.hasSum.tsum_fiberwise (rowProjection N)
  have htwo : Summable (fun q : SignedPrimitiveRows N => 2 * signedSeed N f hneg q) := by
    simpa only [tsum_signed_fiber N f hneg] using hgroup.summable
  exact (summable_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0)).mp htwo
/-- The literal y^s cusp seed is integer-periodic, with no integrability
on all of H claimed. -/
def realCuspSeed (s : ℝ) (z : UpperHalfPlane) : ℝ := z.im ^ s

theorem realCuspSeed_periodic (s : ℝ) :
    ∀ k : ℤ, ∀ z : UpperHalfPlane,
      realCuspSeed s ((k : ℝ) +ᵥ z) = realCuspSeed s z := by
  intro k z
  simp only [realCuspSeed, UpperHalfPlane.vadd_im]

/-- The actual parabolic Poincare/Eisenstein sum at level N. -/
def actualParabolicEisenstein (N : ℕ) (s : ℝ) (z : UpperHalfPlane) : ℝ :=
  ∑' q : GammaInfinityCosets N,
    periodicSeedOnCosets N (realCuspSeed s) (realCuspSeed_periodic s) z q

def levelRowSeed (N : ℕ) (s : ℝ) (z : UpperHalfPlane)
    (v : LevelPrimitiveRow N) : ℝ := seed s z v.1

theorem levelRowSeed_even (N : ℕ) (s : ℝ) (z : UpperHalfPlane) :
    ∀ v, levelRowSeed N s z (rowNeg N v) = levelRowSeed N s z v :=
  fun v => seed_neg s z v.1

theorem levelRowSeed_summable (N : ℕ) (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    Summable (levelRowSeed N s z) := (seed_summable s hs z).subtype _

/-- Actual transformed cusp height is the literal bottom-row Eisenstein
summand, using the existing exact SL2 seed transformation at (0,1). -/
theorem seed_bottomRow_eq_im_pow (s : ℝ) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    seed s z (bottomRow g) = (g • z).im ^ s := by
  have hrow : (![0, 1] : Fin 2 → ℤ) ᵥ* (g : Matrix (Fin 2) (Fin 2) ℤ) =
      bottomRow g := by
    funext j
    fin_cases j <;> simp [Matrix.vecMul, Fin.sum_univ_two, bottomRow]
  have h := seed_SL2_apply s (![0, 1] : Fin 2 → ℤ) g z
  simpa [hrow, seed] using h.symm

theorem parabolic_seed_row_dictionary (N : ℕ) (s : ℝ) (z : UpperHalfPlane)
    (q : GammaInfinityCosets N) :
    periodicSeedOnCosets N (realCuspSeed s) (realCuspSeed_periodic s) z q =
      signedSeed N (levelRowSeed N s z) (levelRowSeed_even N s z)
        (parabolicPrimitiveRowEquiv N q) := by
  refine Quotient.inductionOn q ?_
  intro g
  change (g • z).im ^ s = seed s z (bottomRow (g : SL(2, ℤ)))
  exact (seed_bottomRow_eq_im_pow s (g : SL(2, ℤ)) z).symm

/-- The actual parabolic Eisenstein seed is summable on its genuine
GammaInfinity\Gamma0 index set for s>1. -/
theorem actualParabolicEisenstein_summable
    (N : ℕ) (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    Summable (fun q : GammaInfinityCosets N =>
      periodicSeedOnCosets N (realCuspSeed s) (realCuspSeed_periodic s) z q) := by
  have h := (parabolicPrimitiveRowEquiv N).summable_iff.mpr
    (signedSeed_summable N (levelRowSeed N s z)
      (levelRowSeed_even N s z) (levelRowSeed_summable N s hs z))
  simpa only [← parabolic_seed_row_dictionary N s z] using h
/-- The actual 1/2 normalization is now a THEOREM at every level N, from
s>1 seed convergence and the actual two-to-one signed-row fibers. -/
theorem actualParabolicEisenstein_eq_half_pair_sum
    (N : ℕ) (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    actualParabolicEisenstein N s z =
      (1 / 2 : ℝ) * ∑' v : LevelPrimitiveRow N, seed s z v.1 := by
  have h := tsum_rows_eq_two_parabolic_cosets N (levelRowSeed N s z)
    (levelRowSeed_even N s z) (levelRowSeed_summable N s hs z)
  simp_rw [← parabolic_seed_row_dictionary N s z] at h
  change (∑' v : LevelPrimitiveRow N, seed s z v.1) =
    2 * actualParabolicEisenstein N s z at h
  linarith

/-- At level one the row type is precisely Mathlib's actual primitive
integer-pair type used by the existing primitive Eisenstein family. -/
def levelOnePrimitiveEquiv : LevelPrimitiveRow 1 ≃ EisensteinSeries.gammaSet 1 1 0 where
  toFun v := ⟨v.1, (EisensteinSeries.mem_gammaSet_one v.1).mpr v.property.1⟩
  invFun v := ⟨v.1, (EisensteinSeries.mem_gammaSet_one v.1).mp v.property, by simp⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl

/-- Genuine GammaInfinity\SL2(Z) Poincare caller bridge to the EXISTING
actual primitive Eisenstein series, with factor 1/2 derived, for s>1. -/
theorem actualParabolicEisenstein_one_eq_primitive
    (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    actualParabolicEisenstein 1 s z = primitiveEisenstein s z := by
  rw [actualParabolicEisenstein_eq_half_pair_sum 1 s hs z]
  unfold primitiveEisenstein
  congr 1
  exact levelOnePrimitiveEquiv.tsum_eq
    (fun v : EisensteinSeries.gammaSet 1 1 0 => seed s z v.1)

end
end ImbalancedChen.Part3.Gamma0ParabolicEisensteinHalfPairs20261025a