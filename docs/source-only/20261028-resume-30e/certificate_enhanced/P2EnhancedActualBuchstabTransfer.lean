import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted
import MathlibNt.Wu2008DoubleSieve.PhiBuchstab
import MathlibNt.Wu2008DoubleSieve.RosserSieveConsumer

/-!
SOURCE ONLY; UNCOMPILED; ZERO FORMAL CREDIT.
Actual arbitrary-positive-sigma Buchstab count transfers at one original Q.
The source Phi and every child are existing prime-label sifted counts. The
child selected modulus is enlarged only by the proved strict-cutoff identity.
A deterministic floor(Q/(d*q))+1 gives the child Rosser level. Genuine finite
Rosser source inequalities, including their signed remainder, produce upper
and lower count transfers. No H/h endpoint or generic Sound invariant occurs
among their premises. The W1/W2 switched-count stages remain separate.
-/
namespace ImbalancedChen.P2EnhancedActualBuchstabTransfer

noncomputable section
open Set Finset Real Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted
open MathlibNt.SieveTheory.LinearSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped BigOperators Classical

/-- Original child window at the SAME Q/d. It retains [low,high) ends. -/
def childWindow (N d : ℕ) (Q s t : ℝ) : Finset ℕ :=
  primeWindow (d*N) (cutoff Q d t) (cutoff Q d s)

def childCount (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (s t : ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * ∑ q ∈ childWindow N d Q s t,
    (sourceSieveCount N (d*q) ((d*q)*N) (q:ℝ):ℝ)

/-- Generalizes the existing convolution-only source Buchstab theorem to
exactly the original arbitrary finite nonnegative marked sigma. In fact
the finite equality itself does not need a sign assumption on sigma. -/
theorem actual_Phi_buchstab (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) {s t : ℝ}
    (hR : ∀ d∈D,1≤Q/(d:ℝ)) (hs : 0<s) (hst : s≤t) :
    Phi N Q D sigma t = Phi N Q D sigma s + childCount N Q D sigma s t := by
  unfold Phi childCount
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hcut : cutoff Q d t ≤ cutoff Q d s :=
    Real.rpow_le_rpow_of_exponent_le (hR d hd) (one_div_le_one_div_of_le hs hst)
  rw [source_buchstab_selected_modulus N d hcut,mul_add]

/-- The original physical square gate at an actual child prime, derived
from the actual cutoffs and s>=2, not a reoptimized descendant level. -/
theorem child_squared_prefix {N d q : ℕ} {Q s t : ℝ}
    (hd : 0<d) (hR : 1<Q/(d:ℝ)) (hs : 2≤s)
    (hq : q∈childWindow N d Q s t) : (d:ℝ)*(q:ℝ)^2<Q := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hs0 : 0<s := by linarith
  have hq0 : (0:ℝ)<q := by exact_mod_cast (mem_primeWindow.mp hq).1.pos
  have hnonneg : (0:ℝ)≤Q/(d:ℝ) := by linarith
  have he : (1/s)*2≤1 := by
    have hh := (div_le_one hs0).mpr hs
    simpa [div_eq_mul_inv,mul_comm] using hh
  have hcutsq : (cutoff Q d s)^2≤Q/(d:ℝ) := by
    unfold cutoff
    rw [←Real.rpow_two,←Real.rpow_mul hnonneg]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR.le he
  have hqcut := (mem_primeWindow.mp hq).2.2.2
  have hz0 : 0≤cutoff Q d s := Real.rpow_nonneg hnonneg _
  have hqsq : (q:ℝ)^2<Q/(d:ℝ) := by nlinarith
  have hh := (lt_div_iff₀ hdR).mp hqsq
  nlinarith

/-- The child argument uses its actual Q/(d*q), with both inherited ends. -/
theorem child_actual_argument {N d q : ℕ} {Q s t : ℝ}
    (hd : 0<d) (hR : 1<Q/(d:ℝ)) (hs : 0<s) (hst : s≤t)
    (hq : q∈childWindow N d Q s t) :
    s-1<Real.log (Q/((d*q:ℕ):ℝ))/Real.log (q:ℝ) ∧
    Real.log (Q/((d*q:ℕ):ℝ))/Real.log (q:ℝ)≤t-1 := by
  have hp := (mem_primeWindow.mp hq).1
  have hqR : (1:ℝ)<q := by exact_mod_cast hp.one_lt
  have hh := buchstab_shifted_parameter hR hqR hs (hs.trans_le hst)
    (mem_primeWindow.mp hq).2.2.1 (mem_primeWindow.mp hq).2.2.2
  simpa only [Nat.cast_mul,div_mul_eq_div_div] using hh

/-- Integer level fixed by the true complete child prefix. -/
def childLevel (Q : ℝ) (d q : ℕ) : ℕ := ⌊Q/((d*q:ℕ):ℝ)⌋₊+1

theorem child_level_geometry {N d q : ℕ} {Q s t : ℝ}
    (hd : 0<d) (hR : 1<Q/(d:ℝ)) (hs : 2≤s)
    (hq : q∈childWindow N d Q s t) :
    1<childLevel Q d q ∧ (q:ℝ)≤(childLevel Q d q:ℝ) := by
  have hp := (mem_primeWindow.mp hq).1
  have hdp : (0:ℝ)<(d*q:ℕ) := by exact_mod_cast Nat.mul_pos hd hp.pos
  have hsq := child_squared_prefix hd hR hs hq
  have hres : (q:ℝ)≤Q/((d*q:ℕ):ℝ) := by
    apply (le_div_iff₀ hdp).mpr
    rw [Nat.cast_mul]
    nlinarith
  have hfloor : q≤⌊Q/((d*q:ℕ):ℝ)⌋₊ := Nat.le_floor hres
  constructor
  · dsimp [childLevel]
    have hp2 := hp.two_le
    omega
  · exact_mod_cast (hfloor.trans (Nat.le_succ _))

/-- Every active residual coefficient stays under the ORIGINAL full Q;
its coprimality mask contains the actual child prefix and N. -/
theorem child_coefficient_full_support {side : Bool} {N d q r : ℕ} {Q s t : ℝ}
    (hd : 0<d) (hR : 1<Q/(d:ℝ)) (hs : 2≤s)
    (hq : q∈childWindow N d Q s t)
    (hr : ordinaryRosserWeight side N (d*q) (childLevel Q d q) (q:ℝ) r≠0) :
    ((d*q*r:ℕ):ℝ)≤Q ∧ r.Coprime ((d*q)*N) := by
  have hp := (mem_primeWindow.mp hq).1
  have hqR : (0:ℝ)<q := by exact_mod_cast hp.pos
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hdp : (0:ℝ)<(d*q:ℕ) := by exact_mod_cast Nat.mul_pos hd hp.pos
  have hR0 : (0:ℝ)≤Q/((d*q:ℕ):ℝ) := by
    have hl := child_squared_prefix hd hR hs hq
    have hQ0 : (0:ℝ)<Q := lt_trans (by positivity) hl
    exact div_nonneg hQ0.le hdp.le
  have hrD : r<childLevel Q d q := by
    cases side
    · exact lowerRosserWeight_lt_level hr
    · exact upperRosserWeight_lt_level hr
  have hdiv : r∣ordinarySievePrimeProduct ((d*q)*N) (q:ℝ) := by
    cases side
    · exact lowerRosserWeight_dvd hr
    · exact upperRosserWeight_dvd hr
  have hrfloor : r≤⌊Q/((d*q:ℕ):ℝ)⌋₊ := by
    dsimp [childLevel] at hrD
    omega
  have hrres : (r:ℝ)≤Q/((d*q:ℕ):ℝ) := (Nat.le_floor_iff hR0).mp hrfloor
  have hcap := (le_div_iff₀ hdp).mp hrres
  refine ⟨?_,(ordinarySievePrimeProduct_coprime ((d*q)*N) (q:ℝ)).of_dvd_left hdiv⟩
  simpa only [Nat.cast_mul,mul_comm] using hcap

/-- Actual signed main term of the child finite Rosser polynomial. -/
def childMain (side : Bool) (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (s t : ℝ) : ℝ :=
  ∑ d∈D,sigma d*∑ q∈childWindow N d Q s t,
    (logarithmicIntegral N/(Nat.totient (d*q):ℝ))*
      ordinaryRosserMainSum side N (d*q) (childLevel Q d q) (q:ℝ)

/-- The original signed remainder of precisely the same child coefficient;
it is neither discarded nor replaced by an independent beta. -/
def childError (side : Bool) (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (s t : ℝ) : ℝ :=
  ∑ d∈D,sigma d*∑ q∈childWindow N d Q s t,
    ordinaryRosserRemainder side N (d*q) (childLevel Q d q) (q:ℝ)

/-- The independently defined arithmetic polynomial of the SAME active
child coefficients on the original divisible prime sequence. -/
def childPolynomial (side : Bool) (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (s t : ℝ) : ℝ :=
  ∑ d∈D,sigma d*∑ q∈childWindow N d Q s t,
    ∑ r∈(ordinarySievePrimeProduct ((d*q)*N) (q:ℝ)).divisors,
      ordinaryRosserWeight side N (d*q) (childLevel Q d q) (q:ℝ) r *
        (sourceSequenceCount N (d*q) r:ℝ)

/-- Its li/phi AP model and its signed remainder are an exact algebraic
split of one arithmetic coefficient. This is not an enhanced density
claim or a finite exact-coprime population formula. -/
theorem childPolynomial_eq_main_add_error (side : Bool) (N : ℕ) (Q : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) (s t : ℝ) :
    childPolynomial side N Q D sigma s t =
      childMain side N Q D sigma s t+childError side N Q D sigma s t := by
  simp only [childPolynomial,ordinaryRosser_density_identity,childMain,childError,
    mul_add,sum_add_distrib]

theorem actual_child_signed_sandwich (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) {s t : ℝ}
    (hd : ∀d∈D,0<d) (hsigma : ∀d∈D,0≤sigma d)
    (hR : ∀d∈D,1<Q/(d:ℝ)) (hs : 2≤s) :
    childMain false N Q D sigma s t+childError false N Q D sigma s t≤
        childCount N Q D sigma s t ∧
    childCount N Q D sigma s t≤
        childMain true N Q D sigma s t+childError true N Q D sigma s t := by
  constructor
  · unfold childMain childError childCount
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro d hmem
    rw [←mul_add,←sum_add_distrib]
    apply mul_le_mul_of_nonneg_left _ (hsigma d hmem)
    apply sum_le_sum
    intro q hq
    exact ordinaryRosser_lower_finite
      (child_level_geometry (hd d hmem) (hR d hmem) hs hq).2
  · unfold childMain childError childCount
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro d hmem
    rw [←mul_add,←sum_add_distrib]
    apply mul_le_mul_of_nonneg_left _ (hsigma d hmem)
    apply sum_le_sum
    intro q hq
    exact ordinaryRosser_upper_finite
      (child_level_geometry (hd d hmem) (hR d hmem) hs hq).1
      (child_level_geometry (hd d hmem) (hR d hmem) hs hq).2

/-- Genuine upper count transfer: lower-sieving the removed children
subtracts their real signed main+remainder from the actual anchor Phi. -/
theorem actual_upper_Buchstab_transfer (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) {s t : ℝ}
    (hd : ∀d∈D,0<d) (hsigma : ∀d∈D,0≤sigma d)
    (hR : ∀d∈D,1<Q/(d:ℝ)) (hs : 2≤s) (hst : s≤t) :
    Phi N Q D sigma s≤Phi N Q D sigma t-
      childMain false N Q D sigma s t-childError false N Q D sigma s t := by
  have hi := actual_Phi_buchstab N Q D sigma (fun d hd=>(hR d hd).le)
    (by linarith : 0<s) hst
  have hc := (actual_child_signed_sandwich N Q D sigma hd hsigma hR hs).1
  linarith

/-- Genuine lower count transfer: upper-sieving the same children gives
the opposite signed bound. Both sides keep the identical original Q. -/
theorem actual_lower_Buchstab_transfer (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) {s t : ℝ}
    (hd : ∀d∈D,0<d) (hsigma : ∀d∈D,0≤sigma d)
    (hR : ∀d∈D,1<Q/(d:ℝ)) (hs : 2≤s) (hst : s≤t) :
    Phi N Q D sigma t-childMain true N Q D sigma s t-
      childError true N Q D sigma s t≤Phi N Q D sigma s := by
  have hi := actual_Phi_buchstab N Q D sigma (fun d hd=>(hR d hd).le)
    (by linarith : 0<s) hst
  have hc := (actual_child_signed_sandwich N Q D sigma hd hsigma hR hs).2
  linarith

/-- Exact same-Theta child gain normalization. The denominator is the
proved original positive normalization, not a new independent measure. -/
theorem normalized_actual_Buchstab_gain {N : ℕ} (hN : 4≤N)
    (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) {s t : ℝ}
    (hd : ∀d∈D,0<d) (hsigma : ∀d∈D,0≤sigma d)
    (hR : ∀d∈D,1<Q/(d:ℝ)) (hpositive : ∃d∈D,0<sigma d)
    (hs : 2≤s) (hst : s≤t) :
    (childMain false N Q D sigma s t+childError false N Q D sigma s t)/
        Theta N Q D sigma≤
      (Phi N Q D sigma t-Phi N Q D sigma s)/Theta N Q D sigma ∧
    (Phi N Q D sigma t-Phi N Q D sigma s)/Theta N Q D sigma≤
      (childMain true N Q D sigma s t+childError true N Q D sigma s t)/
        Theta N Q D sigma := by
  have ht := (Theta_pos hN Q D sigma hd hsigma hR hpositive).le
  have hi := actual_Phi_buchstab N Q D sigma (fun d hd=>(hR d hd).le)
    (by linarith : 0<s) hst
  have hc := actual_child_signed_sandwich N Q D sigma hd hsigma hR hs
  constructor <;> apply div_le_div_of_nonneg_right _ ht <;> linarith

end
end ImbalancedChen.P2EnhancedActualBuchstabTransfer
