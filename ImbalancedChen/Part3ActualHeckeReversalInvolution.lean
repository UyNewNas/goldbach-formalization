import ImbalancedChen.Part3ActualHeckeSecondProjection
import Mathlib.RingTheory.Coprime.Lemmas

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
A literal prime Atkin-Lehner correspondence reversal. Bezout supplies
ap-bN=1; gamma=[a,b;N,p], delta=[pa,b;N,1] lie in Gamma0(N),
and W=gamma*diag(sqrt(p),1/sqrt(p)) satisfies B*gamma*B=delta.
The actual prime-level normalizer, square deck transformation, quotient
involution, and exact interchange of BOTH physical projections are proved.
No double-coset reversal, quotient symmetry or quotient measure is assumed.
-/

namespace ImbalancedChen.Part3.ActualHeckeReversalInvolution20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b
open ActualPrimeHeckeRealBranch20261026b ActualHeckeIntersectionSubgroup20261026b
open ActualHeckeCarrierFundamental20261026b ActualHeckeSecondProjection20261026b
open ActualHeckeForgetCoverMeasure20261026b Gamma0ActualCuspsSourceOnly
open Gamma0QuotientCellPushforward20261025a

variable (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)

def reversalBezout : {ab : ℤ × ℤ // (p : ℤ)*ab.1-(N : ℤ)*ab.2=1} := by
  have hcop : Nat.Coprime N p := (hp.coprime_iff_not_dvd.mpr hpN).symm
  obtain ⟨u,v,hbez⟩ := hcop.isCoprime
  exact ⟨(v,-u), by linear_combination hbez⟩

def reversalA : ℤ := (reversalBezout N p hp hpN).val.1
def reversalB : ℤ := (reversalBezout N p hp hpN).val.2

theorem reversal_bezout : (p : ℤ)*reversalA N p hp hpN-(N : ℤ)*reversalB N p hp hpN=1 :=
  (reversalBezout N p hp hpN).property

def reversalGamma : CongruenceSubgroup.Gamma0 N :=
  ⟨⟨!![reversalA N p hp hpN,reversalB N p hp hpN;(N : ℤ),(p : ℤ)], by
    simp only [Matrix.det_fin_two_of]
    linear_combination reversal_bezout N p hp hpN⟩, by
      rw [gamma0_mem_iff_level_dvd_c]
      exact dvd_refl _⟩

def reversalDelta : CongruenceSubgroup.Gamma0 N :=
  ⟨⟨!![(p : ℤ)*reversalA N p hp hpN,reversalB N p hp hpN;(N : ℤ),1], by
    simp only [Matrix.det_fin_two_of, mul_one]
    exact reversal_bezout N p hp hpN⟩, by
      rw [gamma0_mem_iff_level_dvd_c]
      exact dvd_refl _⟩

def reversalSL : SL(2, ℝ) :=
  castIntegral (reversalGamma N p hp hpN) * branchSL p hp.pos none

/-- The second real conjugation is itself an actual integral base-level
matrix. This exact equality pays every square-root normalization. -/
theorem dilation_gamma_dilation :
    branchSL p hp.pos none * castIntegral (reversalGamma N p hp hpN) * branchSL p hp.pos none =
      castIntegral (reversalDelta N p hp hpN) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsq := Real.sq_sqrt hpR.le
  have hmat : (branchMatrix p none).map (Int.castRingHom ℝ) *
      (((reversalGamma N p hp hpN : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) *
        (branchMatrix p none).map (Int.castRingHom ℝ) =
      (p : ℝ) • ((((reversalDelta N p hp hpN : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [branchMatrix,reversalGamma,reversalDelta,Matrix.mul_fin_two,smul_eq_mul] <;> ring
  apply Subtype.ext
  change ((Real.sqrt (p : ℝ))⁻¹ • (branchMatrix p none).map (Int.castRingHom ℝ)) *
      (((reversalGamma N p hp hpN : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) *
        ((Real.sqrt (p : ℝ))⁻¹ • (branchMatrix p none).map (Int.castRingHom ℝ)) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two, ← inv_pow, hsq, hmat, smul_smul]
  simp [hpR.ne']

/-- Literal conjugation of a prime-level deck matrix remains prime-level;
actual branch factorization supplies the integral intermediate matrix. -/
theorem reversal_deck (g : CongruenceSubgroup.Gamma0 (N*p)) :
    ∃ h : CongruenceSubgroup.Gamma0 (N*p),
      reversalSL N p hp hpN * castIntegral g = castIntegral h * reversalSL N p hp hpN := by
  let G := includePrimeLevel N p g
  have hfix := (heckeIntersection_mem_iff_fixed N p hp hpN G).mp
    (includePrimeLevel_mem_intersection N p g)
  obtain ⟨k,hk,hfactor⟩ := branchImage_factor N p hp hpN G G.property none
  rw [hfix] at hfactor
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 1) hfactor
  simp [branchMatrix,Matrix.mul_fin_two] at h01
  have hpk : (p : ℤ) ∣ k 0 1 := ⟨g 0 1, by simpa [G,includePrimeLevel] using h01.symm⟩
  let H : CongruenceSubgroup.Gamma0 N := reversalGamma N p hp hpN * ⟨k,hk⟩ * (reversalGamma N p hp hpN)⁻¹
  have hentry : (H : SL(2, ℤ)) 1 0 =
      (N : ℤ)*(p : ℤ)*k 0 0+(p : ℤ)^2*k 1 0-
        (N : ℤ)^2*k 0 1-(N : ℤ)*(p : ℤ)*k 1 1 := by
    simp [H,reversalGamma,SL2_inv_expl,Matrix.mul_fin_two]
    ring
  have hHp : (p : ℤ) ∣ (H : SL(2, ℤ)) 1 0 := by
    rw [hentry]
    exact dvd_sub (dvd_sub (dvd_add (by exact ⟨(N : ℤ)*k 0 0, by ring⟩)
      (by exact ⟨(p : ℤ)*k 1 0, by ring⟩)) (dvd_mul_of_dvd_right hpk _))
      (by exact ⟨(N : ℤ)*k 1 1, by ring⟩)
  have hH : (H : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 (N*p) :=
    (gamma0_product_prime_mem_iff N p hp hpN H H.property).mpr hHp
  refine ⟨⟨H,hH⟩,?_⟩
  have hreal := branchSL_factor p hp.pos none none g k (by simpa [G,includePrimeLevel] using hfactor)
  change castIntegral (reversalGamma N p hp hpN) * branchSL p hp.pos none * castIntegral g =
    castIntegral (H : SL(2, ℤ)) * (castIntegral (reversalGamma N p hp hpN) * branchSL p hp.pos none)
  rw [mul_assoc, hreal]
  simp only [H,Subgroup.coe_mul,Subgroup.coe_inv,castIntegral,map_mul,map_inv]
  group

def reversalSquareDeck : CongruenceSubgroup.Gamma0 (N*p) :=
  ⟨(reversalGamma N p hp hpN : SL(2, ℤ)) * (reversalDelta N p hp hpN : SL(2, ℤ)), by
    rw [gamma0_mem_iff_level_dvd_c]
    refine ⟨reversalA N p hp hpN+1,?_⟩
    simp [reversalGamma,reversalDelta,Matrix.mul_fin_two]
    ring⟩

theorem reversal_square : reversalSL N p hp hpN * reversalSL N p hp hpN =
    castIntegral (reversalSquareDeck N p hp hpN) := by
  change (castIntegral (reversalGamma N p hp hpN)*branchSL p hp.pos none) *
    (castIntegral (reversalGamma N p hp hpN)*branchSL p hp.pos none) = _
  calc
    _ = castIntegral (reversalGamma N p hp hpN) *
        (branchSL p hp.pos none * castIntegral (reversalGamma N p hp hpN) * branchSL p hp.pos none) := by group
    _ = _ := by rw [dilation_gamma_dilation]; simp [reversalSquareDeck,castIntegral,map_mul]

def quotientReversal : Gamma0OrbitSpace (N*p) → Gamma0OrbitSpace (N*p) :=
  Quotient.lift (fun z : ℍ => orbitProjection (N*p) (reversalSL N p hp hpN • z)) (by
    intro z w hzw
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp hzw
    obtain ⟨h,hh⟩ := reversal_deck N p hp hpN g
    have hact (u : ℍ) : reversalSL N p hp hpN • (g • u) = h • (reversalSL N p hp hpN • u) := by
      rw [← castIntegral_smul g,← mul_smul,hh,mul_smul,castIntegral_smul]
    calc
      _ = orbitProjection (N*p) (reversalSL N p hp hpN • (g • w)) := congrArg _ hg.symm
      _ = orbitProjection (N*p) (h • (reversalSL N p hp hpN • w)) := congrArg _ (hact w)
      _ = _ := orbitProjection_smul (N*p) h _)

theorem quotientReversal_projection (z : ℍ) :
    quotientReversal N p hp hpN (orbitProjection (N*p) z) =
      orbitProjection (N*p) (reversalSL N p hp hpN • z) := rfl

theorem quotientReversal_measurable : Measurable (quotientReversal N p hp hpN) :=
  measurable_from_quotient.mpr ((orbitProjection_measurable (N*p)).comp
    (continuous_const_smul (reversalSL N p hp hpN)).measurable)

theorem quotientReversal_involutive : Function.Involutive (quotientReversal N p hp hpN) := by
  intro q
  refine Quotient.inductionOn q (fun z => ?_)
  rw [quotientReversal_projection,quotientReversal_projection,← mul_smul,reversal_square,
    castIntegral_smul]
  exact orbitProjection_smul (N*p) (reversalSquareDeck N p hp hpN) z

/-- Exact interchange of the first and second ACTUAL quotient projections. -/
theorem firstProjection_reversal (q : Gamma0OrbitSpace (N*p)) :
    forgetPrimeLevel N p (quotientReversal N p hp hpN q) = secondProjection N p hp hpN q := by
  refine Quotient.inductionOn q (fun z => ?_)
  rw [quotientReversal_projection,forgetPrimeLevel_projection,secondProjection_projection]
  change orbitProjection N ((castIntegral (reversalGamma N p hp hpN)*branchSL p hp.pos none) • z) = _
  rw [mul_smul,castIntegral_smul]
  exact orbitProjection_smul N (reversalGamma N p hp hpN) _

theorem secondProjection_reversal (q : Gamma0OrbitSpace (N*p)) :
    secondProjection N p hp hpN (quotientReversal N p hp hpN q) = forgetPrimeLevel N p q := by
  refine Quotient.inductionOn q (fun z => ?_)
  rw [quotientReversal_projection,secondProjection_projection,forgetPrimeLevel_projection]
  change orbitProjection N (branchSL p hp.pos none •
    ((castIntegral (reversalGamma N p hp hpN)*branchSL p hp.pos none) • z)) = _
  rw [← mul_smul,← mul_assoc,dilation_gamma_dilation,castIntegral_smul]
  exact orbitProjection_smul N (reversalDelta N p hp hpN) z

end
end ImbalancedChen.Part3.ActualHeckeReversalInvolution20261026b
