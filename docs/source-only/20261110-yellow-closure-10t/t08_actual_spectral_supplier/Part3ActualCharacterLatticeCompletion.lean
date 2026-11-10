import ImbalancedChen.Part3OriginalCharacterPairDilation
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

/-!
Young (3.8), weight zero and trivial nebentypus. This is the actual
primitive-to-unrestricted character sum, including the factor L(2s,chi²).
The gcd fibers are those of the original two-dimensional integer lattice.
-/
namespace ImbalancedChen.Part3.ActualCharacterLatticeCompletion20261110

noncomputable section
open Complex Set EisensteinSeries UpperHalfPlane
open scoped BigOperators UpperHalfPlane MatrixGroups
open RealEisensteinSeedConvergence PrimitiveEisensteinParameterAnalytic
open CharacterEisensteinSeries CharacterEisensteinRowAction
open OriginalCharacterPairDilation20261102s Gamma0DegeneracyMapSourceOnly

abbrev Vec := Fin 2 → ℤ

def latticeBase (z : ℍ) (v : Vec) : ℝ :=
  z.im / ‖(v 0 : ℂ)*(z : ℂ) + (v 1 : ℂ)‖^2

theorem latticeBase_pos (z : ℍ) {v : Vec} (hv : v ≠ 0) : 0 < latticeBase z v := by
  have hn : (fun i : Fin 2 => (v i : ℝ)) ≠ 0 := by
    intro h
    apply hv
    ext i
    exact_mod_cast congrFun h i
  have hlin : (v 0 : ℂ)*(z : ℂ) + (v 1 : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_intCast] using UpperHalfPlane.linear_ne_zero z hn
  exact div_pos z.im_pos (sq_pos_of_pos (norm_pos_iff.mpr hlin))

def latticeSeed (z : ℍ) (s : ℂ) (v : Vec) : ℂ :=
  if v = 0 then 0 else Complex.exp (s * (Real.log (latticeBase z v) : ℂ))

def latticeTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℍ) (s : ℂ) (v : Vec) : ℂ :=
  characterWeight χ (v 0) (v 1) * latticeSeed z s v

theorem norm_latticeSeed (z : ℍ) (s : ℂ) (hs : 1 < s.re) (v : Vec) :
    ‖latticeSeed z s v‖ = seed s.re z v := by
  by_cases hv : v = 0
  · subst v
    simp [latticeSeed, seed, Real.zero_rpow (by linarith : -(2*s.re) ≠ 0)]
  · have hp := latticeBase_pos z hv
    have hpow : (‖(v 0 : ℂ)*(z : ℂ) + (v 1 : ℂ)‖^2) ^ s.re =
        ‖(v 0 : ℂ)*(z : ℂ) + (v 1 : ℂ)‖ ^ (2*s.re) := by
      simpa only [Real.rpow_natCast] using
        (Real.rpow_mul (norm_nonneg ((v 0 : ℂ)*(z : ℂ) + (v 1 : ℂ))) 2 s.re).symm
    rw [latticeSeed, if_neg hv, Complex.norm_exp]
    calc
      _ = (latticeBase z v) ^ s.re := by
        rw [Real.rpow_def_of_pos hp]
        simp [Complex.mul_re, mul_comm]
      _ = _ := by
        rw [latticeBase, Real.div_rpow z.im_pos.le (sq_nonneg _) s.re, hpow, seed_eq_quotient]

theorem latticeTerm_norm_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : Vec => ‖latticeTerm χ z s v‖) := by
  apply (seed_summable s.re hs z).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro v
  rw [latticeTerm, norm_mul, ← norm_latticeSeed z s hs v]
  exact mul_le_of_le_one_left (norm_nonneg _) (characterWeight_norm_le_one χ _ _)

def latticeG {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (s : ℂ) (w : ℍ) : ℂ :=
  (1/2 : ℂ) * ∑' v : Vec, latticeTerm χ (scaledPoint q hq w) s v

private theorem primitive_ne_zero (v : PrimitivePair) : v.val ≠ 0 := by
  intro hv
  have h := (gammaSet_one_mem_iff _).mp v.property
  simp [hv] at h

private theorem smul_seed (z : ℍ) (s : ℂ) {a : ℕ} (ha : 0 < a) (v : PrimitivePair) :
    latticeSeed z s (a • v.val) = (a : ℂ) ^ (-(2*s)) * complexSeed z v s := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hv : (a • v.val : Vec) ≠ 0 := by
    intro h
    apply primitive_ne_zero v
    ext i
    have hi := congrFun h i
    simpa [Pi.smul_apply, nsmul_eq_mul, ha.ne'] using hi
  have hlin : (((a • v.val : Vec) 0 : ℤ) : ℂ)*(z : ℂ) +
      (((a • v.val : Vec) 1 : ℤ) : ℂ) =
      (a : ℂ) * ((v.val 0 : ℂ)*(z : ℂ) + (v.val 1 : ℂ)) := by
    simp [Pi.smul_apply, nsmul_eq_mul]
    ring
  have hb : latticeBase z (a • v.val) = positiveBase z v / (a : ℝ)^2 := by
    rw [latticeBase, hlin, norm_mul, Complex.norm_natCast, mul_pow, positiveBase]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hlog : Complex.log (a : ℂ) = (Real.log (a : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log haR.le).symm
  rw [latticeSeed, if_neg hv, hb, Real.log_div (positiveBase_pos z v).ne'
    (pow_ne_zero _ haR.ne'), Real.log_pow, complexSeed, Complex.cpow_def_of_ne_zero haC,
    hlog, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private def dirichletTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (a : ℕ) : ℂ :=
  LSeries.term (fun n : ℕ => (χ^2) (n : ZMod q)) (2*s) a

private theorem scaled_latticeTerm {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (w : ℍ) (s : ℂ) {a : ℕ} (ha : 0 < a) (v : PrimitivePair) :
    latticeTerm χ (scaledPoint q hq w) s (a • v.val) =
      dirichletTerm χ s a * characterSeed hq χ w v s := by
  have hχ : characterWeight χ ((a • v.val : Vec) 0) ((a • v.val : Vec) 1) =
      (χ^2) (a : ZMod q) * primitiveWeight χ v := by
    simp only [primitiveWeight, characterWeight, Pi.smul_apply, nsmul_eq_mul,
      Int.cast_mul, Int.cast_natCast, map_mul, pow_two, MulChar.mul_apply]
    ring
  rw [latticeTerm, hχ, smul_seed _ _ ha, dirichletTerm, LSeries.term_of_ne_zero ha.ne',
    characterSeed, Complex.cpow_neg]
  ring

private theorem gcd_sum {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (w : ℍ) (s : ℂ) (a : ℕ) :
    (∑' v : gammaSet 1 a 0, latticeTerm χ (scaledPoint q hq w) s v.val) =
      dirichletTerm χ s a * ∑' v : PrimitivePair, characterSeed hq χ w v s := by
  by_cases ha : a = 0
  · subst a
    have hv (v : gammaSet 1 0 0) : v.val = 0 := by
      simpa only [zero_smul] using gammaSet_eq_gcd_mul_divIntMap v.property
    simp [hv, latticeTerm, latticeSeed, dirichletTerm]
  · letI : NeZero a := ⟨ha⟩
    rw [← tsum_mul_left]
    rw [← (gammaSetDivGcdEquiv a).tsum_eq (fun v : PrimitivePair =>
      dirichletTerm χ s a * characterSeed hq χ w v s)]
    apply tsum_congr
    intro v
    have hv : v.val = a • (gammaSetDivGcdEquiv a v).val :=
      gammaSet_eq_gcd_mul_divIntMap v.property
    calc
      _ = latticeTerm χ (scaledPoint q hq w) s (a • (gammaSetDivGcdEquiv a v).val) :=
        congrArg _ hv
      _ = _ := scaled_latticeTerm hq χ w s (Nat.pos_of_ne_zero ha) _

/-- The literal full character lattice sum equals the native Dirichlet L
factor times the existing genuine primitive automorphic function. -/
theorem latticeG_eq_LFunction_mul {q : ℕ} [NeZero q] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (w : ℍ) (s : ℂ) (hs : 1 < s.re) :
    latticeG hq χ s w = (χ^2).LFunction (2*s) * characterEisenstein hq χ s w := by
  have h2 : 1 < (2*s).re := by simp [Complex.mul_re]; linarith
  have hsum := (latticeTerm_norm_summable χ (scaledPoint q hq w) s hs).of_norm
  have hf := gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr hsum
  rw [latticeG, ← gammaSetDivGcdSigmaEquiv.symm.tsum_eq, hf.tsum_sigma]
  simp_rw [gammaSetDivGcdSigmaEquiv_symm_eq, gcd_sum hq χ w s]
  rw [tsum_mul_right, DirichletCharacter.LFunction_eq_LSeries _ h2, characterEisenstein]
  unfold LSeries dirichletTerm
  ring

/-- Same established equality for every original occupied level and every
legal dilation. The all-lattice side has proved automorphy there. -/
theorem original_latticeG_oldform {q : ℕ} [NeZero q] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (N : ℕ) (d : ℕ+) (hN : q^2*(d : ℕ) ∣ N) (s : ℂ) (hs : 1 < s.re)
    (g : SL(2,ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (w : ℍ) :
    latticeG hq χ s (degeneracyDiagonal d d.pos • (g • w)) =
      (χ^2).LFunction (2*s) * characterLatticeOldform hq χ d s w := by
  rw [latticeG_eq_LFunction_mul hq χ _ _ hs]
  change _ * characterLatticeOldform hq χ d s (g • w) = _
  rw [characterLatticeOldform_invariant N hq χ d hN s hs g hg w]

end
end ImbalancedChen.Part3.ActualCharacterLatticeCompletion20261110
