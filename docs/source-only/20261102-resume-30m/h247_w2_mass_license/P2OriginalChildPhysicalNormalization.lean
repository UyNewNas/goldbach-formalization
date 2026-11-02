import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted
import MathlibNt.Wu2008DoubleSieve.ReboxingNormalization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact physical identities for the same-Q child mass. The arithmetic
multiplier is 1/p on the repeated-prefix lane and 1/(p-2) on the fresh
lane. Neither lane is silently replaced by 1/(p-1). The accompanying
mass file treats genuine prime sums; the complete marked-family analytic
licence and H247 are deliberately not asserted here.
-/
namespace ImbalancedChen.P2OriginalChildPhysicalNormalization

noncomputable section
open Wu2008DoubleSieve Real
open scoped Classical BigOperators

def localPrimeFactor (d p : ℕ) : ℝ :=
  if p ∣ d then 1/(p:ℝ) else 1/((p:ℝ)-2)

def thetaAtom (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  4*AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N*
    (wuSingularSeries (d*N)/((Nat.totient d:ℝ)*log (Q/d)))

theorem Theta_eq_sum_atoms (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    P2EnhancedTwentyOneSameQWeighted.Theta N Q D sigma =
      ∑ d∈D,sigma d*thetaAtom N Q d := by
  unfold P2EnhancedTwentyOneSameQWeighted.Theta thetaAtom
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem thetaAtom_single {N d p : ℕ} {Q : ℝ}
    (hN : 0<N) (hd : 0<d) (hp : p.Prime) (hp2 : 2<p)
    (hpN : p.Coprime N) (hQ : 1<Q/d) :
    thetaAtom N Q (d*p) = thetaAtom N Q d*
      (localPrimeFactor d p/(1-log (p:ℝ)/log (Q/d))) := by
  unfold thetaAtom localPrimeFactor
  rw [wu_inserted_theta_weight hN hd hp hp2 hpN hQ]
  ring

/-- The pair arithmetic factor still includes repeated primes. In the
ordered domains p<q, repetition against d remains possible. -/
theorem pair_arithmetic_weight {N d p q : ℕ}
    (hN : 0<N) (hd : 0<d) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2<p) (hq2 : 2<q) (hpN : p.Coprime N) (hqN : q.Coprime N) :
    wuSingularSeries ((d*p*q)*N)/(Nat.totient (d*p*q):ℝ) =
      (wuSingularSeries (d*N)/(Nat.totient d:ℝ))*
        (localPrimeFactor d p*localPrimeFactor (d*p) q) := by
  rw [wu_inserted_arithmetic_weight hN (Nat.mul_pos hd hp.pos) hq hq2 hqN,
    wu_inserted_arithmetic_weight hN hd hp hp2 hpN]
  unfold localPrimeFactor
  ring

theorem pair_log_denominator {Q : ℝ} {d p q : ℕ}
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hQ : 1<Q/d) :
    log (Q/(d*p*q:ℕ)) = log (Q/d)*
      (1-log (p:ℝ)/log (Q/d)-log (q:ℝ)/log (Q/d)) := by
  have hdR : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hpR : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hqR : (0:ℝ)<q := Nat.cast_pos.mpr hq
  have hR : 0<Q/(d:ℝ) := zero_lt_one.trans hQ
  have he : Q/(d*p*q:ℕ)=(Q/(d:ℝ))/((p:ℝ)*(q:ℝ)) := by
    push_cast
    ring
  rw [he, log_div hR.ne' (mul_pos hpR hqR).ne', log_mul hpR.ne' hqR.ne']
  field_simp [(log_pos hQ).ne']
  ring

theorem thetaAtom_pair {N d p q : ℕ} {Q : ℝ}
    (hN : 0<N) (hd : 0<d) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2<p) (hq2 : 2<q) (hpN : p.Coprime N) (hqN : q.Coprime N)
    (hQ : 1<Q/d) :
    thetaAtom N Q (d*p*q) = thetaAtom N Q d*
      (localPrimeFactor d p*localPrimeFactor (d*p) q/
        (1-log (p:ℝ)/log (Q/d)-log (q:ℝ)/log (Q/d))) := by
  unfold thetaAtom
  rw [← div_div, pair_arithmetic_weight hN hd hp hq hp2 hq2 hpN hqN,
    pair_log_denominator hd hp.pos hq.pos hQ]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- No alpha=2 substitution: this is the true residual quotient. -/
def alpha (beta L : ℝ) : ℝ := (1-beta)/L
def childAlpha (beta L w : ℝ) : ℝ := (1-beta-L*w)/(L*(1-w))

theorem childAlpha_eq {beta L w : ℝ} (hL : L≠0) (hw : 1-w≠0) :
    childAlpha beta L w=1+(alpha beta L-1)/(1-w) := by
  unfold childAlpha alpha
  field_simp [hL,hw]
  ring

theorem childAlpha_ge_parent {beta L w : ℝ}
    (hL : 0<L) (ha : 2≤alpha beta L) (hw : 0≤w) (hw1 : w<1) :
    alpha beta L≤childAlpha beta L w := by
  rw [childAlpha_eq hL.ne' (by linarith)]
  have hr : alpha beta L-1≤(alpha beta L-1)/(1-w) := by
    apply (le_div_iff₀ (by linarith : 0<1-w)).mpr
    nlinarith [mul_nonneg (show 0≤alpha beta L-1 by linarith) hw]
  linarith

theorem pair_childAlpha {beta L u v : ℝ} (hL : L≠0) (huv : 1-u-v≠0) :
    childAlpha beta L (u+v)=1+(alpha beta L-1)/(1-u-v) := by
  simpa only [sub_add_eq_sub_sub] using childAlpha_eq (beta:=beta) hL
    (show 1-(u+v)≠0 by simpa only [sub_add_eq_sub_sub] using huv)

theorem singleton_inherited_argument {L s0 u : ℝ} (hL : L≠0) (hs : s0≠0) :
    (L-L*u)/(L/s0)=s0*(1-u) := by
  field_simp [hL,hs]
  ring

theorem pair_inherited_argument {L s0 u v : ℝ} (hL : L≠0) (hs : s0≠0) :
    (L-L*u-L*v)/(L/s0)=s0*(1-u-v) := by
  field_simp [hL,hs]
  ring

theorem pair_first_prime_argument {L u v : ℝ} (hL : L≠0) (hu : u≠0) :
    (L-L*u-L*v)/(L*u)=(1-u-v)/u := by
  field_simp [hL,hu]
  ring

/-- The physical cutoff is inherited; its comparison with the first
new prime is derived from the actual lower endpoint. -/
theorem inherited_cutoff_below_first {L s0 u : ℝ}
    (hL : 0<L) (hu : 1/s0<u) : L/s0<L*u := by
  simpa only [mul_one_div] using mul_lt_mul_of_pos_left hu hL

theorem appended_prime_below_ceiling {L u b chi : ℝ}
    (hL : 0<L) (hu : u<b) (hceil : L*b≤chi) : L*u<chi :=
  (mul_lt_mul_of_pos_left hu hL).trans_le hceil

/-- The full square inequalities are retained before normalization. -/
theorem physical_pair_squares {N : ℝ} (hN : 1<N) (beta L u v : ℝ) (hL : 0<L) :
    (N^beta*(N^(L*v))^2<N^(beta+L) ∧
      N^beta*(N^(L*u))^2*N^(L*v)<N^(beta+L)) ↔
      2*v<1 ∧ 2*u+v<1 := by
  have hN0 : 0<N := zero_lt_one.trans hN
  have hsq (w : ℝ) : (N^(L*w))^2=N^(2*(L*w)) := by
    rw [mul_comm (2:ℝ), Real.rpow_mul hN0.le]
    norm_num
  rw [hsq v, hsq u, ← Real.rpow_add hN0, ← Real.rpow_add hN0,
    ← Real.rpow_add hN0, Real.rpow_lt_rpow_left_iff hN,
    Real.rpow_lt_rpow_left_iff hN]
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · apply (mul_lt_mul_left hL).mp
      nlinarith only [h1]
    · apply (mul_lt_mul_left hL).mp
      nlinarith only [h2]
  · rintro ⟨h1,h2⟩
    constructor
    · nlinarith only [mul_lt_mul_of_pos_left h1 hL]
    · nlinarith only [mul_lt_mul_of_pos_left h2 hL]

/-- The old selected-square tests can be conjoined without altering
their truth; these are separate physical conditions, not consequences
of an ordinary integral limit. -/
theorem retain_selected_tests {P : Prop} {N : ℝ} (hN : 1<N)
    (beta L u v : ℝ) (hL : 0<L) :
    (P ∧ N^beta*(N^(L*v))^2<N^(beta+L) ∧
      N^beta*(N^(L*u))^2*N^(L*v)<N^(beta+L)) ↔
      P ∧ 2*v<1 ∧ 2*u+v<1 := by
  exact and_congr_right (fun _ => physical_pair_squares hN beta L u v hL)

theorem localPrimeFactor_pos {d p : ℕ} (hp : (2:ℝ)<p) :
    0<localPrimeFactor d p := by
  unfold localPrimeFactor
  split_ifs <;> exact one_div_pos.mpr (by linarith)

/-- A uniform comparison, including every repeated-prefix lane. The
small parameter depends on the selected prime floor, never on d. -/
theorem localPrimeFactor_relative_error {A : ℝ} {d p : ℕ}
    (hA : 4≤A) (hp : A≤(p:ℝ)) :
    |localPrimeFactor d p*((p:ℝ)-1)-1|≤2/A := by
  have hA0 : 0<A := by linarith
  have hp0 : (0:ℝ)<p := by linarith
  have hp2 : (0:ℝ)<(p:ℝ)-2 := by linarith
  unfold localPrimeFactor
  split_ifs
  · have he : 1/(p:ℝ)*((p:ℝ)-1)-1= -(1/(p:ℝ)) := by field_simp [hp0.ne']; ring
    rw [he,abs_neg,abs_of_pos (one_div_pos.mpr hp0)]
    apply (div_le_div_iff₀ hp0 hA0).mpr
    linarith
  · have he : 1/((p:ℝ)-2)*((p:ℝ)-1)-1=1/((p:ℝ)-2) := by field_simp [hp2.ne']; ring
    rw [he,abs_of_pos (one_div_pos.mpr hp2)]
    apply (div_le_div_iff₀ hp2 hA0).mpr
    linarith

end
end ImbalancedChen.P2OriginalChildPhysicalNormalization
