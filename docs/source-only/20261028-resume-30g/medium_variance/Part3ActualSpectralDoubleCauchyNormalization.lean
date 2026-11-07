import ImbalancedChen.Part3ActualSpectralMonomialMargins
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual equation(25)--(26) normalization on the original occupied owner.
The two Cauchy powers, zero difference, zero Poisson mode and |a|/x
term are all retained. These are identities of the original scales,
not an assumed spectral return or an assumed bound for W_bare.
-/

namespace ImbalancedChen.Part3.ActualSpectralDoubleCauchyNormalization20261028
noncomputable section
open ActualOriginalSpectralScales20261028 MediumGlobalDyadicOwnership20261028

def bareCauchyPrefactor (atom : MediumAtom) (k : Key) : ℝ :=
  atom.U/(atom.Q1*roughR k*roughS k*Real.sqrt (roughS k))
def originalBareScale (atom : MediumAtom) : ℝ := atom.U^2/atom.Q1
def countingH (atom : MediumAtom) (k : Key) (loss : ℝ) : ℝ :=
  loss*atom.Q1*(roughR k)^2*(roughS k)^2/atom.V
def countingMass (atom : MediumAtom) (k : Key) (loss : ℝ) : ℝ :=
  (countingH atom k loss*roughS k)^2*countingF atom
def zeroDifferenceCost (atom : MediumAtom) (k : Key) (loss : ℝ) : ℝ :=
  countingH atom k loss*roughS k*spectralB atom k*countingF atom*spectralC atom k
def fourthNormalization (atom : MediumAtom) (k : Key) (loss : ℝ) : ℝ :=
  (bareCauchyPrefactor atom k)^4*countingMass atom k loss/(originalBareScale atom)^4

/-- The displayed square-root denominator is exactly S^(3/2). -/
theorem bareCauchyPrefactor_eq_original (atom : MediumAtom) (k : Key) :
    bareCauchyPrefactor atom k = atom.U/(atom.Q1*roughR k*(roughS k)^(3/2 : ℝ)) := by
  have hS : 0 < roughS k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).2
  have hs : roughS k*Real.sqrt (roughS k) = (roughS k)^(3/2 : ℝ) := by
    calc
      _ = (roughS k)^(1 : ℝ)*(roughS k)^(1/2 : ℝ) := by
        rw [Real.rpow_one,Real.sqrt_eq_rpow]
      _ = (roughS k)^((1 : ℝ)+1/2) := (Real.rpow_add hS _ _).symm
      _ = _ := by congr 1; norm_num
  dsimp only [bareCauchyPrefactor]
  rw [mul_assoc (atom.Q1*roughR k),hs]

private theorem bareCauchyPrefactor_sq {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom) (k : Key) :
    (bareCauchyPrefactor atom k)^2 = atom.U^2/(atom.Q1^2*(roughR k)^2*(roughS k)^3) := by
  have hS : 0 ≤ roughS k := zero_le_one.trans (rough_scales_one_le k).2
  unfold bareCauchyPrefactor
  rw [div_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hS]
  congr 1
  ring

/-- Normalize the actual counting mass AFTER both Cauchy operations.
loss is kept literal; it is not assumed subpower or small. -/
theorem fourthNormalization_eq_original {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (loss : ℝ) :
    fourthNormalization atom k loss = loss^2*atom.Q1/(atom.U*atom.scale^2) := by
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hM : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  have hQ : 0 < atom.Q1 := lt_of_lt_of_le zero_lt_one hA.2.2.1
  have hR : 0 < roughR k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).1
  have hS : 0 < roughS k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).2
  unfold fourthNormalization
  rw [show (bareCauchyPrefactor atom k)^4 = ((bareCauchyPrefactor atom k)^2)^2 by ring,
    bareCauchyPrefactor_sq hA k]
  dsimp only [countingMass,countingH,countingF,originalBareScale,MediumAtom.scale]
  field_simp [hN.ne',hM.ne',hQ.ne',hR.ne',hS.ne'] <;> ring

/-- The separate y=0/k=0 difference contributes loss*D0 to the
normalized SQUARED bound. It is not an entry of the nonzero count. -/
theorem zeroDifference_normalization {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (loss : ℝ) :
    (bareCauchyPrefactor atom k)^2*zeroDifferenceCost atom k loss/
      (originalBareScale atom)^2 = loss*D0 atom k := by
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hM : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  have hQ : 0 < atom.Q1 := lt_of_lt_of_le zero_lt_one hA.2.2.1
  have hR : 0 < roughR k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).1
  have hS : 0 < roughS k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).2
  rw [bareCauchyPrefactor_sq hA k]
  dsimp only [zeroDifferenceCost,countingH,countingF,spectralB,spectralC,
    originalBareScale,D0,MediumAtom.scale]
  field_simp [hN.ne',hM.ne',hQ.ne',hR.ne',hS.ne'] <;> ring

/-- The two genuine regular monomials normalize to D1 and
(|a|/x)*D1. In particular the second is never silently removed. -/
theorem regular_monomial_normalization {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (loss : ℝ) :
    fourthNormalization atom k loss*(atom.residue.natAbs : ℝ)^theta*
        (spectralC atom k*spectralB atom k*(spectralZ k)^2) = loss^2*D1 atom k ∧
      fourthNormalization atom k loss*(atom.residue.natAbs : ℝ)^theta*
        ((atom.residue.natAbs : ℝ)*spectralU atom k*spectralZ k) =
          loss^2*((atom.residue.natAbs : ℝ)/atom.scale)*D1 atom k := by
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hM : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  rw [fourthNormalization_eq_original hA k loss]
  constructor <;>
    dsimp only [spectralC,spectralB,spectralZ,spectralU,D1,MediumAtom.scale] <;>
    field_simp [hN.ne',hM.ne'] <;> ring

private theorem exceptional_scale_product {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom) (k : Key) :
    (spectralC atom k)^(1+2*theta)*spectralB atom k*(spectralZ k)^(2-2*theta) =
      atom.U*(atom.U^(1+2*theta)*(roughR k)^(2+2*theta)*(roughS k)^(5-2*theta)) := by
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hR : 0 < roughR k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).1
  have hS : 0 < roughS k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).2
  have hz : ((roughS k)^2)^(2-2*theta) = (roughS k)^(4-4*theta) := by
    rw [← Real.rpow_two (roughS k),← Real.rpow_mul hS.le]
    congr 1
    ring
  have hr : (roughR k)^(1+2*theta)*roughR k = (roughR k)^(2+2*theta) := by
    calc
      _ = (roughR k)^(1+2*theta)*(roughR k)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (roughR k)^((1+2*theta)+1) := (Real.rpow_add hR _ _).symm
      _ = _ := by congr 1; ring
  have hs : (roughS k)^(1+2*theta)*(roughS k)^(4-4*theta) =
      (roughS k)^(5-2*theta) := by
    rw [← Real.rpow_add hS]
    congr 1
    ring
  dsimp only [spectralC,spectralB,spectralZ]
  rw [Real.mul_rpow (mul_nonneg hN.le hR.le) hS.le,
    Real.mul_rpow hN.le hR.le,hz]
  calc
    _ = atom.U*atom.U^(1+2*theta)*
        ((roughR k)^(1+2*theta)*roughR k)*
        ((roughS k)^(1+2*theta)*(roughS k)^(4-4*theta)) := by ring
    _ = _ := by rw [hr,hs]; ring

/-- The improved exceptional monomial becomes D2 at the original
scale, with no lost Bspec/D or arithmetic-residue packet factor. -/
theorem exceptional_monomial_normalization {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (loss : ℝ) :
    fourthNormalization atom k loss*(spectralC atom k)^(1+2*theta)*
      spectralB atom k*(spectralZ k)^(2-2*theta) = loss^2*D2 atom k := by
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hx : 0 < atom.scale := by
    change 0 < atom.U*atom.V
    have hM : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
    positivity
  rw [show fourthNormalization atom k loss*(spectralC atom k)^(1+2*theta)*
      spectralB atom k*(spectralZ k)^(2-2*theta) =
      fourthNormalization atom k loss*((spectralC atom k)^(1+2*theta)*
        spectralB atom k*(spectralZ k)^(2-2*theta)) by ring,
    exceptional_scale_product hA k,fourthNormalization_eq_original hA k loss]
  dsimp only [D2]
  field_simp [hN.ne',hx.ne'] <;> ring

/-- The genuine zero POISSON mode is retained in the returned norm.
Under the separately displayed Bspec^2<=x gate it fits the regular
monomial; it is not the separate y=0 difference above. -/
theorem zeroPoisson_monomial_le_regular {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (hB : (spectralB atom k)^2 ≤ atom.scale) :
    (spectralB atom k)^2*spectralU atom k*spectralZ k ≤
      spectralC atom k*spectralB atom k*(spectralZ k)^2 := by
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hM : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  have hR : 0 < roughR k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).1
  have hS : 0 < roughS k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).2
  calc
    _ ≤ atom.scale*spectralU atom k*spectralZ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB
        (by dsimp [spectralU]; positivity)) (by dsimp [spectralZ]; positivity)
    _ = _ := by rw [← (actual_spectral_normalizations hA k).2.1]; ring

end
end ImbalancedChen.Part3.ActualSpectralDoubleCauchyNormalization20261028
