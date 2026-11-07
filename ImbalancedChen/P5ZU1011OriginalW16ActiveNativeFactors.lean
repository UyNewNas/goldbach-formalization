import ImbalancedChen.P5ZU1011OriginalW16JointSmallBeta
import ImbalancedChen.P5ZU1011OriginalFifteenJointSelectedSupport

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

An ACTUAL nonzero original W native upper-Rosser coefficient supplies its
literal residual prime vector, full well support, and every late-prime
cutoff. No hResidualWell or pre-certified rough-vector premise remains.
The primary odd-cubic support theorem is reused from the genuine native
coefficient proof, not re-proved and not replaced by a unit bound.

The SAME existing JOINT W completion functions then factor the literal
fullPrefix*d and, after actual small-beta attachment, e*(fullPrefix*d),
with the original three monomials uniform over the fixed kappa interval.
Both U10 low and U11 high bands remain native jointSelector tuples.
Coefficient-unit/regroup, beta presieve compatibility, AP/PP distribution,
W density and H248 analytic licences remain OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16ActiveNativeFactors
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalW16NearCapNative
open U1011OriginalW16AttachedWellSupport (specified specified_product)
open U1011OriginalFifteenJointSelectedSupport (residualPrimes actual_plus_residual_well residualPrimes_product)
open U1011OriginalW16SmallBetaMonomials (SmallBetaActive)
open P5U1011JointOverlap

/-- Actual coefficient support fixes every residual prime below Z,
including the literal decreasing order and all original occurrences. -/
theorem active_residual_slots {N cap d : ℕ} {Z R : ℝ}
    (hd : actualSmallRosserPlus N cap Z R d≠0) :
    ∀q∈residualPrimes d,Nat.Prime q ∧ (q:ℝ)<Z := by
  have hs := (actualSmallRosserPlus_active hd).2.2
  intro q hq
  have hlist : q∈d.primeFactorsList := List.mem_reverse.mp hq
  have hprime := Nat.prime_of_mem_primeFactorsList hlist
  have hmem : q∈d.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hprime,Nat.dvd_of_mem_primeFactorsList hlist,hs.1⟩
  exact ⟨hprime,hs.2 q hmem⟩

/-- The true native lambda activity supplies BOTH residual inputs of the
W support/algorithm chain, and the original exact integer product. -/
theorem active_native_support {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest wPolicy B=true)
    (hbox : coordinates N t∈B.region) (hd : coefficient B eta N d≠0) :
    actualDwellSupport (U1011OriginalW16NearCapSupport.runLevel B eta N)
      (specified t++residualPrimes d) ∧
      (specified t++residualPrimes d).prod=fullPrefix t*d ∧
      (∀q∈residualPrimes d,Nat.Prime q ∧ (q:ℝ)<Z B eta N) := by
  have hwell : actualDwellSupport (D B eta N) (residualPrimes d) := actual_plus_residual_well hd
  refine ⟨U1011OriginalW16NearCapSupport.attached_well_support hN ht B eta heta hvalid hpositive
    htest hbox (residualPrimes d) hwell,?_,active_residual_slots hd⟩
  rw [List.prod_append,specified_product,residualPrimes_product hd]

def completedFactors (B : Box) (eta : ℚ) (N : ℕ) (t : Four) (A : ℝ) (d : ℕ) : ℕ×ℕ×ℕ :=
  U1011OriginalW16JointFactors.completedFactors B eta N t A (residualPrimes d)
def attachedFactors (B : Box) (eta : ℚ) (N : ℕ) (t : Four) (A : ℝ) (d e : ℕ) : ℕ×ℕ×ℕ :=
  U1011OriginalW16JointSmallBeta.attachedFactors B eta N t A (residualPrimes d) e

/-- A native nonzero lambda atom has the actual positive natural
factorization of its modulus and SAME factors for the entire kappa range.
No well-support, final monomial or factorability target is an input. -/
theorem active_native_monomials {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest wPolicy B=true)
    (hbox : coordinates N t∈B.region) (hd : coefficient B eta N d≠0)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) :
    let abc := completedFactors B eta N t A d
    let delta := (delta B eta:ℝ)
    abc.1*abc.2.1*abc.2.2=fullPrefix t*d ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀kappa:ℝ,0≤kappa → kappa≤delta →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-4*delta) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-4*delta) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-39*delta/8) := by
  have hwell : actualDwellSupport (D B eta N) (residualPrimes d) := actual_plus_residual_well hd
  have hslots := active_residual_slots hd
  have h := U1011OriginalW16JointFactors.fixed_factors_uniform_residue hN ht B eta heta
    hvalid hpositive htest hbox A hA hAupper (residualPrimes d) hwell hslots
  simpa only [completedFactors,residualPrimes_product hd] using h

/-- Genuine active beta attaches to the SAME third factor of the actual
native lambda modulus. All original support and factorization hypotheses
are supplied from lambda activity, not postulated as an analytic licence. -/
theorem active_native_beta_monomials {N enumeration d e : ℕ} (hN : 1<N)
    {E : ℕ×ℕ → Prop} {t : Four} (ht : t∈jointSelector N E)
    (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region)
    (hd : coefficient B eta N d≠0) (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ))
    (w ell : ℝ) (hell : 0<ell) (hellsmall : ell≤(delta B eta:ℝ)/2)
    (he : SmallBetaActive N enumeration e w ell) :
    let abc := attachedFactors B eta N t A d e
    let delta := (delta B eta:ℝ)
    abc.1*abc.2.1*abc.2.2=e*(fullPrefix t*d) ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀kappa:ℝ,0≤kappa → kappa≤delta →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-3*delta) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-3*delta) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-2*delta) := by
  have hwell : actualDwellSupport (D B eta N) (residualPrimes d) := actual_plus_residual_well hd
  have hslots := active_residual_slots hd
  have h := U1011OriginalW16JointSmallBeta.fixed_beta_attached_monomials hN ht B eta heta
    hvalid hpositive htest hbox A hA hAupper (residualPrimes d) hwell hslots w ell hell hellsmall he
  simpa only [attachedFactors,residualPrimes_product hd] using h

/-- The atom input is exactly the actual all16 JOINT eta-native W row,
with the same support/coefficient, not a replacement sieve weight. -/
theorem compiled_W_activity {N d : ℕ} (B : Box) (eta : ℚ)
    (hd : U1011OriginalSixteenJointNearCapCompiler.rowCoefficient wPolicy B eta N d≠0) :
    coefficient B eta N d≠0 := by
  rw [←(U1011OriginalSixteenJointNearCapCompiler.W_native_binding B eta N).2.2.2 d]
  exact hd

end
end ImbalancedChen.P5Z.U1011OriginalW16ActiveNativeFactors
