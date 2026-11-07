import ImbalancedChen.P2SeedOmegaLiteralFibre

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact semantic binding of the ORIGINAL repaired ordinary functional to
the expression consumed by certify_second_seed_omega_envelope.py.
This is the omega-envelope functional, with the stated constant envelope
and the uniform M20/M21 unit summands retained. It is not a count licence
or a proof that this envelope majorizes every switched domain. Those and
the missing finite rational passing witness remain OPEN for Dots.
-/

namespace ImbalancedChen.P2SeedOmegaLiteralFunctional
noncomputable section
open Set MeasureTheory
open scoped Interval BigOperators
open P2SeedOmegaLiteralFibre

def correction (w : ℝ) : ℝ := ∫ x in (2:ℝ)..w-1,Real.log (x-1)/x
def negative (top : ℝ) : ℝ :=
  ∫ u in a0..top,Real.log (s0*(1-u)-1)/(u*(1-u))

def triangleLogIntegral (top : ℝ) : ℝ :=
  ∫ u in a0..top,Real.log (top*(1-2*u)/(u*(1-u-top)))/(u*(1-u))
def rectangleLogIntegral (lo hi : ℝ) : ℝ :=
  ∫ u in a0..a1,Real.log (hi*(1-u-lo)/(lo*(1-u-hi)))/(u*(1-u))

def badOrdinaryDouble : ℝ :=
  (∫ u in corner..(1/3:ℝ),∫ v in (1-2*u)..a2,pairKernel u v)+
  (∫ u in (1/3:ℝ)..a2,∫ v in u..a2,pairKernel u v)

def badRoughDouble : ℝ :=
  (∫ u in corner..(1/3:ℝ),∫ v in (1-2*u)..a2,roughPairKernel u v)+
  (∫ u in (1/3:ℝ)..a2,∫ v in u..a2,roughPairKernel u v)

def badOldLog : ℝ :=
  (∫ u in corner..(1/3:ℝ),
    Real.log (a2*u/((1-2*u)*(1-u-a2)))/(u*(1-u)))+
  (∫ u in (1/3:ℝ)..a2,
    Real.log (a2*(1-2*u)/(u*(1-u-a2)))/(u*(1-u)))

def badMassLog : ℝ :=
  (∫ u in corner..(1/3:ℝ),Real.log (a2/(1-2*u))/u)+
  (∫ u in (1/3:ℝ)..a2,Real.log (a2/u)/u)

theorem badOrdinaryDouble_eq_original_log : badOrdinaryDouble=badOldLog := by
  unfold badOrdinaryDouble badOldLog
  congr 1
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num [corner])] at hu
    exact bad_first_pair_fibre hu
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num [a2])] at hu
    exact bad_second_pair_fibre hu

theorem badRoughDouble_eq_original_log : badRoughDouble=badMassLog := by
  unfold badRoughDouble badMassLog
  congr 1
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num [corner])] at hu
    exact bad_first_rough_fibre hu
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num [a2])] at hu
    exact bad_second_rough_fibre hu

def l01 : ℝ := Real.log (s0/phi1)
def l12 : ℝ := Real.log (phi1/phi2)
def l23 : ℝ := Real.log (phi2/phi3)
def l3b : ℝ := Real.log (phi3/s)

/-- Exactly the script's thirteen uniform mass expressions. In
particular the two final entries contain BOTH nonunit and unit terms. -/
def switchedMass : Fin 13 → ℝ := ![
  omegaCap*((phi1+phi3)*Real.log (phi1/phi3)-2*(phi1-phi3)),
  omegaCap*(phi1-phi2*(1+l12))*Real.log (phi2/s),
  omegaCap*l12*(phi2*(l23-1)+phi3),
  omegaCap*(s0-phi1*(1+l01))*l3b,
  omegaCap*l01*(phi1-phi2)*Real.log (phi2/s),
  omegaCap*l01*(phi2*(Real.log (phi2/s)-1)+s),
  omegaCap*l12*(phi2-phi3)*l3b,
  phi2*l23^4/24,
  phi2*l23^3*l3b/6,
  phi3*l23^2*l3b^2/4,
  phi3*l12*l3b^3/6,
  phi3*l23*l3b^4/24+phi2*l3b^4/24,
  phi3*l3b^6/720+phi3*l3b^5/120]

def switchCost : ℝ := (K/4)*∑ i,switchedMass i

/-- Literal repaired double-integral functional. The bad ordinary
integral is removed exactly once and its positive rough envelope inserted
exactly once. These are the old four ordinary pieces, without feedback. -/
def actualJ2omega : ℝ :=
  (-(4*correction s0+correction phi1)+
    (negative b+negative a2+negative a3)-
    (ordinaryTriangle a2+ordinaryRectangle a2 a3+
      ordinaryTriangle a1+ordinaryRectangle a1 a2)-
    ((K*omegaCap*s0/4)*badRoughDouble-badOrdinaryDouble)-switchCost)/5

/-- Same literal functional with the original bad region left intact,
before the certificate's one-third split. -/
theorem actualJ2omega_eq_unsplit : actualJ2omega=
    (-(4*correction s0+correction phi1)+
      (negative b+negative a2+negative a3)-
      (ordinaryTriangle a2+ordinaryRectangle a2 a3+
        ordinaryTriangle a1+ordinaryRectangle a1 a2)-
      ((K*omegaCap*s0/4)*
        (∫ u in corner..a2,∫ v in badLower u..a2,roughPairKernel u v)-
        (∫ u in corner..a2,∫ v in badLower u..a2,pairKernel u v))-switchCost)/5 := by
  simp only [actualJ2omega,badRoughDouble,badOrdinaryDouble,
    bad_rough_partition,bad_pair_partition]

def originalOneDimensionalExpression : ℝ :=
  (-(4*correction s0+correction phi1)+
    (negative b+negative a2+negative a3)-
    (triangleLogIntegral a2+rectangleLogIntegral a2 a3+
      triangleLogIntegral a1+rectangleLogIntegral a1 a2)-
    ((K*omegaCap*s0/4)*badMassLog-badOldLog)-switchCost)/5

/-- Analytic reduction of the actual literal double integrals, with
every parameter and the original division by five fixed in the types. -/
theorem actualJ2omega_eq_original_expression :
    actualJ2omega=originalOneDimensionalExpression := by
  have ht2 := ordinaryTriangle_eq_original_log
    (top:=a2) (by norm_num [a0,a2]) le_rfl
  have ht1 := ordinaryTriangle_eq_original_log
    (top:=a1) (by norm_num [a0,a1]) (by norm_num [a1,a2])
  have hr23 := ordinaryRectangle_eq_original_log
    (lo:=a2) (hi:=a3) (by norm_num [a2]) (by norm_num [a2,a3]) le_rfl
  have hr12 := ordinaryRectangle_eq_original_log
    (lo:=a1) (hi:=a2) (by norm_num [a1]) (by norm_num [a1,a2])
    (by norm_num [a2,a3])
  change ordinaryTriangle a2=triangleLogIntegral a2 at ht2
  change ordinaryTriangle a1=triangleLogIntegral a1 at ht1
  change ordinaryRectangle a2 a3=rectangleLogIntegral a2 a3 at hr23
  change ordinaryRectangle a1 a2=rectangleLogIntegral a1 a2 at hr12
  simp only [actualJ2omega,originalOneDimensionalExpression,ht2,ht1,hr23,hr12,
    badRoughDouble_eq_original_log,badOrdinaryDouble_eq_original_log]

/-- Original normalization is explicit; the target is 20249/10^6.
No theorem in this module asserts this predicate. -/
def RequiredLowerBound : Prop := (20249/1000000:ℝ)≤actualJ2omega

end
end ImbalancedChen.P2SeedOmegaLiteralFunctional
