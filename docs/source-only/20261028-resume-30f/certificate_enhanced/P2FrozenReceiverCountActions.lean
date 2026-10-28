import ImbalancedChen.P2EnhancedActualBuchstabTransfer
import MathlibNt.Wu2008DoubleSieve.Buchstab

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact source actions with a fixed original receiver predicate. Every
receiver remains a literal prime label at most N; masks and strict prime
windows are inherited. The signed AP discrepancy uses the same frozen
predicate and the same genuine ordinary Rosser coefficient. No assertion
that this discrepancy is small, or that a table seed is licensed, occurs.
-/
namespace ImbalancedChen.P2FrozenReceiverCountActions

noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedActualBuchstabTransfer (childWindow childLevel child_level_geometry)
open MathlibNt.SieveTheory.LinearSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical BigOperators

/-- The original unscaled source, with one immutable receiver test. -/
def frozenCarrier (N d : ℕ) (E : ℕ → Prop) (z : ℝ) : Finset ℕ :=
  (sourceSieveCarrier N d (d*N) z).filter E

def frozenCount (N d : ℕ) (E : ℕ → Prop) (z : ℝ) : ℤ :=
  (frozenCarrier N d E z).card

def quotientCount (N d M : ℕ) (E : ℕ → Prop) (z : ℝ) : ℤ :=
  ((sieveCarrier N d M z).filter E).card

/-- Filtering receiver labels commutes with the existing first-divisor
partition. The fixed predicate is neither recomputed nor discarded. -/
theorem frozen_quotient_buchstab (N d M : ℕ) (E : ℕ → Prop)
    {z w : ℝ} (hzw : z≤w) :
    quotientCount N d M E w = quotientCount N d M E z-
      ∑ q∈primeWindow M z w,quotientCount N (d*q) M E (q:ℝ) := by
  have h := finite_buchstab ((sieveCarrier N d M z).filter E)
    (fun ell => (N-ell)/d) (primeWindow M z w)
  have hs : siftedIndices ((sieveCarrier N d M z).filter E)
      (fun ell => (N-ell)/d) (primeWindow M z w) =
      (sieveCarrier N d M w).filter E := by
    rw [←siftedIndices_sieveCarrier N d M hzw]
    ext ell
    simp only [siftedIndices,mem_filter]
    tauto
  have hm : firstMass ((sieveCarrier N d M z).filter E)
      (fun ell => (N-ell)/d) (primeWindow M z w) =
      ∑ q∈primeWindow M z w,quotientCount N (d*q) M E (q:ℝ) := by
    unfold firstMass
    apply sum_congr rfl
    intro q hq
    have hf : ((sieveCarrier N d M z).filter E).filter
        (fun ell => FirstDivisor (primeWindow M z w) ((N-ell)/d) q) =
        ((sieveCarrier N d M z).filter
          (fun ell => FirstDivisor (primeWindow M z w) ((N-ell)/d) q)).filter E := by
      ext ell
      simp only [mem_filter]
      tauto
    rw [hf,firstCarrier_eq N d M hq]
    rfl
  rw [hs,hm] at h
  exact h

/-- At a selected child prime, only the proved strict-cutoff mask change
is made. The receiver predicate E stays literally the parent's E. -/
theorem frozen_selected_buchstab (N d : ℕ) (E : ℕ → Prop)
    {z w : ℝ} (hzw : z≤w) :
    frozenCount N d E z = frozenCount N d E w+
      ∑ q∈primeWindow (d*N) z w,frozenCount N (d*q) E (q:ℝ) := by
  have h := frozen_quotient_buchstab N d (d*N) E hzw
  have hd (x : ℝ) : quotientCount N d (d*N) E x=frozenCount N d E x := by
    unfold quotientCount frozenCount frozenCarrier
    rw [(source_double_sieve_carriers N d x).1]
  rw [hd z,hd w] at h
  have hsum : (∑ q∈primeWindow (d*N) z w,quotientCount N (d*q) (d*N) E (q:ℝ)) =
      ∑ q∈primeWindow (d*N) z w,frozenCount N (d*q) E (q:ℝ) := by
    apply sum_congr rfl
    intro q hq
    unfold quotientCount frozenCount frozenCarrier
    rw [buchstab_next_source_carrier N d (mem_primeWindow.mp hq).1]
  rw [hsum] at h
  linarith

/-- Labels remain distinct when two marked histories have equal product.
Their receiver tests and multiplicities are retained separately. -/
def markedPhi {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) (s : ℝ) : ℝ :=
  ∑ a∈L,sigma a*(frozenCount N (B a) (E a) (cutoff Q (B a) s):ℝ)

def markedChildren {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) (s t : ℝ) : ℝ :=
  ∑ a∈L,sigma a*∑ q∈childWindow N (B a) Q s t,
    (frozenCount N (B a*q) (E a) (q:ℝ):ℝ)

theorem markedPhi_buchstab {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) {s t : ℝ}
    (hR : ∀a∈L,1≤Q/(B a:ℝ)) (hs : 0<s) (hst : s≤t) :
    markedPhi N Q L B sigma E t =
      markedPhi N Q L B sigma E s+markedChildren N Q L B sigma E s t := by
  unfold markedPhi markedChildren
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have hc : cutoff Q (B a) t≤cutoff Q (B a) s :=
    Real.rpow_le_rpow_of_exponent_le (hR a ha) (one_div_le_one_div_of_le hs hst)
  have hb := frozen_selected_buchstab N (B a) (E a) hc
  have hbR : (frozenCount N (B a) (E a) (cutoff Q (B a) t):ℝ) =
      (frozenCount N (B a) (E a) (cutoff Q (B a) s):ℝ)+
        ∑ q∈childWindow N (B a) Q s t,(frozenCount N (B a*q) (E a) (q:ℝ):ℝ) := by
    exact_mod_cast hb
  rw [hbR,mul_add]

/-- The independently defined divisible prime population at full d*r,
with precisely the old receiver E. It includes unit/zero conventions. -/
def frozenSequenceCount (N d : ℕ) (E : ℕ → Prop) (r : ℕ) : ℕ :=
  (((goldbachDivisible N d).filter E).filter (fun ell => r∣N-ell)).card

theorem frozenCount_eq_gcd_indicator (N d : ℕ) (E : ℕ → Prop) (z : ℝ) :
    (frozenCount N d E z:ℝ) =
      ∑ ell∈(goldbachDivisible N d).filter E,
        if Nat.gcd (ordinarySievePrimeProduct (d*N) z) (N-ell)=1 then 1 else 0 := by
  rw [sum_boole]
  have hc : frozenCarrier N d E z =
      ((goldbachDivisible N d).filter E).filter
        (fun ell => Nat.gcd (ordinarySievePrimeProduct (d*N) z) (N-ell)=1) := by
    ext ell
    simp only [frozenCarrier,sourceSieveCarrier,goldbachDivisible,mem_filter,
      sifted_iff_product_coprime,Nat.coprime_iff_gcd_eq_one]
    tauto
  simp only [frozenCount,hc,Int.cast_natCast]

theorem frozen_weighted_count_eq_gcd_sum (N d P : ℕ) (hP : P≠0)
    (E : ℕ → Prop) (coeff : ℕ → ℝ) :
    (∑ r∈P.divisors,coeff r*(frozenSequenceCount N d E r:ℝ)) =
      ∑ ell∈(goldbachDivisible N d).filter E,
        ∑ r∈(Nat.gcd P (N-ell)).divisors,coeff r := by
  unfold frozenSequenceCount
  simp_rw [←sum_boole,mul_sum,mul_ite,mul_one,mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro ell _
  rw [←sum_filter]
  have hf : P.divisors.filter (fun r => r∣N-ell)=(Nat.gcd P (N-ell)).divisors := by
    rw [←Nat.divisors_filter_dvd_of_dvd hP (Nat.gcd_dvd_left P (N-ell))]
    ext r
    simp only [mem_filter,Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨hr,hn⟩
      exact ⟨hr,(Nat.mem_divisors.mp hr).1,hn⟩
    · tauto
  rw [hf]

def frozenPolynomial (side : Bool) (N d D : ℕ) (E : ℕ → Prop) (z : ℝ) : ℝ :=
  ∑ r∈(ordinarySievePrimeProduct (d*N) z).divisors,
    ordinaryRosserWeight side N d D z r*(frozenSequenceCount N d E r:ℝ)

/-- The li/phi model is kept with its exact same-coefficient signed
discrepancy. No uniform distribution for an arbitrary E is inferred. -/
def frozenRemainder (side : Bool) (N d D : ℕ) (E : ℕ → Prop) (z : ℝ) : ℝ :=
  ∑ r∈(ordinarySievePrimeProduct (d*N) z).divisors,
    ordinaryRosserWeight side N d D z r*
      ((frozenSequenceCount N d E r:ℝ)-logarithmicIntegral N/(Nat.totient (d*r):ℝ))

theorem frozenPolynomial_eq_model_add_remainder (side : Bool) (N d D : ℕ)
    (E : ℕ → Prop) (z : ℝ) :
    frozenPolynomial side N d D E z =
      (logarithmicIntegral N/(Nat.totient d:ℝ))*ordinaryRosserMainSum side N d D z+
        frozenRemainder side N d D E z := by
  unfold frozenPolynomial ordinaryRosserMainSum frozenRemainder
  rw [mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  have hc : d.Coprime r :=
    ((ordinarySievePrimeProduct_coprime (d*N) z).of_dvd_left
      (Nat.mem_divisors.mp hr).1 |>.of_dvd_right (dvd_mul_right d N)).symm
  rw [Nat.totient_mul hc,Nat.cast_mul,←div_div]
  ring

theorem frozenRosser_upper_finite {N d D : ℕ} (E : ℕ → Prop) {z : ℝ}
    (hD : 1<D) (hz : z≤(D:ℝ)) :
    (frozenCount N d E z:ℝ)≤frozenPolynomial true N d D E z := by
  unfold frozenPolynomial
  rw [frozenCount_eq_gcd_indicator,
    frozen_weighted_count_eq_gcd_sum N d _ (ordinarySievePrimeProduct_pos _ _).ne']
  have hprime : ∀p∈(ordinarySievePrimeProduct (d*N) z).primeFactors,p<D := by
    intro p hp
    rw [ordinarySievePrimeProduct,Nat.primeFactors_prod
      (fun q hq => (mem_primeWindow.mp hq).1)] at hp
    exact_mod_cast (mem_primeWindow.mp hp).2.2.2.trans_le hz
  have hc := upperRosserWeight_certificate (ordinarySievePrimeProduct_squarefree _ _)
    (ordinarySievePrimeProduct_pos _ _).ne' hD hprime
  apply sum_le_sum
  intro ell _
  exact upperRosserWeight_divisor_sum hc (Nat.gcd_dvd_left _ _)

theorem frozenRosser_lower_finite {N d D : ℕ} (E : ℕ → Prop) {z : ℝ}
    (hz : z≤(D:ℝ)) :
    frozenPolynomial false N d D E z≤(frozenCount N d E z:ℝ) := by
  unfold frozenPolynomial
  rw [frozenCount_eq_gcd_indicator,
    frozen_weighted_count_eq_gcd_sum N d _ (ordinarySievePrimeProduct_pos _ _).ne']
  have hprime : ∀p∈(ordinarySievePrimeProduct (d*N) z).primeFactors,p<D := by
    intro p hp
    rw [ordinarySievePrimeProduct,Nat.primeFactors_prod
      (fun q hq => (mem_primeWindow.mp hq).1)] at hp
    exact_mod_cast (mem_primeWindow.mp hp).2.2.2.trans_le hz
  have hc := lowerRosserWeight_certificate (ordinarySievePrimeProduct_squarefree _ _)
    (ordinarySievePrimeProduct_pos _ _).ne' hprime
  apply sum_le_sum
  intro ell _
  exact lowerRosserWeight_divisor_sum hc (Nat.gcd_dvd_left _ _)

def markedChildPolynomial {ι : Type*} (side : Bool) (N : ℕ) (Q : ℝ)
    (L : Finset ι) (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) (s t : ℝ) : ℝ :=
  ∑ a∈L,sigma a*∑ q∈childWindow N (B a) Q s t,
    frozenPolynomial side N (B a*q) (childLevel Q (B a) q) (E a) (q:ℝ)

theorem markedChildren_sandwich {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) {s t : ℝ}
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) (hs : 2≤s) :
    markedChildPolynomial false N Q L B sigma E s t≤markedChildren N Q L B sigma E s t ∧
    markedChildren N Q L B sigma E s t≤markedChildPolynomial true N Q L B sigma E s t := by
  constructor
  · unfold markedChildPolynomial markedChildren
    apply sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left _ (hsigma a ha)
    apply sum_le_sum
    intro q hq
    exact frozenRosser_lower_finite (E a)
      (child_level_geometry (hB a ha) (hR a ha) hs hq).2
  · unfold markedChildPolynomial markedChildren
    apply sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left _ (hsigma a ha)
    apply sum_le_sum
    intro q hq
    exact frozenRosser_upper_finite (E a)
      (child_level_geometry (hB a ha) (hR a ha) hs hq).1
      (child_level_geometry (hB a ha) (hR a ha) hs hq).2

theorem marked_actual_upper_transfer {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) {s t : ℝ}
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) (hs : 2≤s) (hst : s≤t) :
    markedPhi N Q L B sigma E s≤markedPhi N Q L B sigma E t-
      markedChildPolynomial false N Q L B sigma E s t := by
  have hb := markedPhi_buchstab N Q L B sigma E (fun a ha => (hR a ha).le)
    (by linarith : 0<s) hst
  have hc := (markedChildren_sandwich N Q L B sigma E hB hsigma hR hs).1
  linarith

theorem marked_actual_lower_transfer {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop) {s t : ℝ}
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) (hs : 2≤s) (hst : s≤t) :
    markedPhi N Q L B sigma E t-markedChildPolynomial true N Q L B sigma E s t≤
      markedPhi N Q L B sigma E s := by
  have hb := markedPhi_buchstab N Q L B sigma E (fun a ha => (hR a ha).le)
    (by linarith : 0<s) hst
  have hc := (markedChildren_sandwich N Q L B sigma E hB hsigma hR hs).2
  linarith

end
end ImbalancedChen.P2FrozenReceiverCountActions
