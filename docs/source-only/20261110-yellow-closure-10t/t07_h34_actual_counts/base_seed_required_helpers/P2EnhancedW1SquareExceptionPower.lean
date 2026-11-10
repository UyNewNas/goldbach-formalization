import ImbalancedChen.P2EnhancedW1TripleActualCarrierBranch
import ImbalancedChen.RoughSquareException
import ImbalancedChen.PowerErrorBudget
import ImbalancedChen.P2EnhancedThetaReciprocalMass
import MathlibNt.Wu2008DoubleSieve.NinthErrorPaymentAsymptotic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The Phase8 repeated-first-prime exception is counted inside the true
old-mask historyCarrier.  A receiver is admitted only when its actual
complement is positive and a prime at or above the fixed power cutoff
squares into the quotient (N-ell)/B.  Complement division injects this
finite family into the existing exact rough-square integer carrier at
level floor(N/B).  This proves a uniform 1/B power bound, with no +1
per prime and no appeal to real measure-zero boundaries.

The finite bound is negligible relative to the genuine singularNormalization
H(N) for every fixed positive exponent.  With the original nonnegative
sigma and a fixed finite marked support, its 1/B factor also pays the
weighted exception relative to the SAME Theta_Q.  This still does not
identify this broad square-event superset with every original labelled
W1 exceptional term; that finite ownership is a separate interface.

Source: manuscript-body.tex 790--865; same-new-level-double-sieve-route.tex
92--105 and 147--165, repeated-prime power-saving sentence.
-/

namespace ImbalancedChen.P2EnhancedW1SquareExceptionPower

noncomputable section
open Finset Filter Wu2008DoubleSieve
open scoped Classical Topology BigOperators
open P2EnhancedW1R2ActualCarrierBranch (eligiblePrimes eligiblePrime_data)
open P2LargerSActualPositiveCounts (historyCarrier)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2EnhancedThetaReciprocalMass (Theta_lower)
open P5OriginalActionMassBound (W1Anchor)
open MathlibNt.SieveTheory.SingularSeries

/-- The physical old-mask receiver family at one marked B.  The prime
square lies in the actual old quotient, not in a surrogate real set. -/
def squareEvent (N B : ℕ) (E : ℕ → ℕ → Prop) (y z : ℝ) : Finset ℕ :=
  (historyCarrier N B E y).filter (fun ell =>
    ell < N ∧ ∃ p : ℕ, p.Prime ∧ z ≤ (p : ℝ) ∧ p^2 ∣ (N-ell)/B)

/-- Phase8's first-prime square exception is a member of this larger
physical family when the W1 anchor cutoff exceeds the fixed power. -/
theorem phase8_exception_mem {N ell : ℕ} {Q z : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a : ℕ}
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (hcomp : 0 < N-ell)
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hcut : z ≤ cutoff Q old.prod (W1Anchor j))
    (hsq : a^2 ∣ (N-ell)/old.prod) :
    ell ∈ squareEvent N old.prod E
      (cutoff Q old.prod (W1Anchor j)) z := by
  have hlt : ell < N := by omega
  refine Finset.mem_filter.mpr ⟨hell,hlt,a,(eligiblePrime_data ha).1,?_,hsq⟩
  exact hcut.trans (eligiblePrime_data ha).2.2.1

/-- The old quotient map has no multiplicity: the physical B divisibility
inside historyCarrier recovers N-ell exactly from the quotient. -/
theorem squareEvent_card_le_rough (N B : ℕ) (E : ℕ → ℕ → Prop)
    (y z : ℝ) (hB : 0 < B) :
    (squareEvent N B E y z).card ≤
      (roughSquareExceptions (N/B) z).card := by
  apply Finset.card_le_card_of_injOn (fun ell => (N-ell)/B)
  · intro ell hmem
    obtain ⟨hell,hlt,p,hp,hzp,hsq⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hsource,_⟩ := Finset.mem_filter.mp hell
    have hdiv := (Finset.mem_filter.mp hsource).2.2.1
    have hcomp : 0 < N-ell := Nat.sub_pos_of_lt hlt
    have hn : 0 < (N-ell)/B :=
      Nat.div_pos (Nat.le_of_dvd hcomp hdiv) hB
    exact mem_roughSquareExceptions.mpr
      ⟨hn, Nat.div_le_div_right (Nat.sub_le N ell), p,hp,hzp,hsq⟩
  · intro ell hmem ell' hmem' heq
    have hell := (Finset.mem_filter.mp hmem).1
    have hell' := (Finset.mem_filter.mp hmem').1
    have hlt := (Finset.mem_filter.mp hmem).2.1
    have hlt' := (Finset.mem_filter.mp hmem').2.1
    have hdiv := (Finset.mem_filter.mp (Finset.mem_filter.mp hell).1).2.2.1
    have hdiv' := (Finset.mem_filter.mp (Finset.mem_filter.mp hell').1).2.2.1
    have hsub : N-ell = N-ell' := by
      calc
        N-ell = ((N-ell)/B)*B := (Nat.div_mul_cancel hdiv).symm
        _ = ((N-ell')/B)*B := by rw [heq]
        _ = N-ell' := Nat.div_mul_cancel hdiv'
    omega

/-- Genuine finite fixed-cutoff power saving, including the complete
physical B denominator. -/
theorem squareEvent_card_le_power (N B : ℕ) (E : ℕ → ℕ → Prop)
    (y z : ℝ) (hB : 0 < B) (hz : 2 ≤ z) :
    ((squareEvent N B E y z).card : ℝ) ≤
      2 * (N : ℝ) / ((B : ℝ) * z) := by
  have hcard := squareEvent_card_le_rough N B E y z hB
  have hzpos : 0 < z := by linarith
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  calc
    ((squareEvent N B E y z).card : ℝ) ≤
        ((roughSquareExceptions (N/B) z).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ 2 * ((N/B : ℕ) : ℝ) / z :=
      roughSquareExceptions_card_le_two_mul_div (N/B) hz
    _ ≤ 2 * ((N : ℝ)/(B : ℝ)) / z := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)) hzpos.le
    _ = 2 * (N : ℝ) / ((B : ℝ) * z) := by ring

/-- A one-branch form independent of B, still retaining B in the
stronger preceding theorem. -/
theorem squareEvent_card_le_sublinear {N B : ℕ} {eta : ℝ}
    (E : ℕ → ℕ → Prop) (y : ℝ) (hB : 0 < B)
    (hN : 1 < N) (hcut : 2 ≤ (N : ℝ)^eta) :
    ((squareEvent N B E y ((N : ℝ)^eta)).card : ℝ) ≤
      2 * (N : ℝ)^(1-eta) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hzpos : 0 < (N : ℝ)^eta := by linarith
  have hBone : (1 : ℝ) ≤ B := by exact_mod_cast hB
  calc
    _ ≤ 2 * (N : ℝ) / ((B : ℝ) * (N : ℝ)^eta) :=
      squareEvent_card_le_power N B E y hB hcut
    _ ≤ 2 * (N : ℝ) / (N : ℝ)^eta := by
      apply div_le_div_of_nonneg_left (by positivity)
        hzpos (by nlinarith [mul_nonneg (sub_nonneg.mpr hBone) hzpos.le])
    _ = 2 * (N : ℝ)^(1-eta) := by
      rw [Real.rpow_sub hNpos, Real.rpow_one]
      field_simp [ne_of_gt hzpos]

/-- The actual square exception is uniformly o(H(N)) over all positive
B, all frozen predicates and all physical cutoffs. -/
theorem eventually_squareEvent_le_normalization {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, ∀ E : ℕ → ℕ → Prop, ∀ y : ℝ,
      0 < B →
      ((squareEvent N B E y ((N : ℝ)^eta)).card : ℝ) ≤
        epsilon * singularNormalization N := by
  have hcut : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ)^eta :=
    ((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  have hpower := eventually_powerLog_le_singularNormalization
    2 (1-eta) 0 (by linarith : 1-eta < 1) epsilon hepsilon
  filter_upwards [hcut,hpower,eventually_ge_atTop (2 : ℕ)] with
    N hcutN hpowerN hN
  intro B E y hB
  exact (squareEvent_card_le_sublinear E y hB (by omega) hcutN).trans
    (by simpa using hpowerN)

/-- The actual nonnegative marked weights retain their original 1/B
reciprocal mass, with arbitrary finite support and frozen E. -/
def weightedSquareEvent (N : ℕ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (E : ℕ → ℕ → Prop) (y : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ B ∈ D, sigma B * ((squareEvent N B E (y B) z).card : ℝ)

theorem weightedSquareEvent_le_reciprocal_mass (N : ℕ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (E : ℕ → ℕ → Prop) (y : ℕ → ℝ) {z : ℝ}
    (hz : 2 ≤ z)
    (hd : ∀ B ∈ D, 0 < B) (hsigma : ∀ B ∈ D, 0 ≤ sigma B) :
    weightedSquareEvent N D sigma E y z ≤
      (2 * (N : ℝ) / z) * (∑ B ∈ D, sigma B / (B : ℝ)) := by
  unfold weightedSquareEvent
  rw [mul_sum]
  apply Finset.sum_le_sum
  intro B hmem
  have hb := squareEvent_card_le_power N B E (y B) z
    (hd B hmem) hz
  have hw := mul_le_mul_of_nonneg_left hb (hsigma B hmem)
  convert hw using 1 <;> ring

/-- Genuine same-Q weighted power saving for the broad physical square
event. The threshold precedes N, Q, the support, weights, and histories.
Any actual Phase8 exceptional term maps into this event when its W1
anchor y dominates the fixed N^eta cutoff. -/
theorem weightedSquareEvent_theta_payment {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
        (E : ℕ → ℕ → Prop) (y : ℕ → ℝ),
      (∀ B ∈ D, 0 < B) → (∀ B ∈ D, 0 ≤ sigma B) →
      (∀ B ∈ D, 1 < Q / (B : ℝ) ∧ Q / (B : ℝ) ≤ (N : ℝ)) →
      weightedSquareEvent N D sigma E y ((N : ℝ)^eta) ≤
        epsilon * Theta N Q D sigma := by
  obtain ⟨T1,hT1,hpay⟩ := ninth_power_log_error_budget 0
    (C := 2) (α := eta) (ε := 2 * liuUniversalProduct * epsilon)
    (by norm_num) heta (by positivity)
  have hcut : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ)^eta :=
    ((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp hcut
  refine ⟨max T1 T2, by omega, ?_⟩
  intro N hNT Q D sigma E y hd hsigma hR
  have hN1 := (le_max_left T1 T2).trans hNT
  have hN4 : 4 ≤ N := by omega
  have hz := hT2 N ((le_max_right T1 T2).trans hNT)
  have hmass : 0 ≤ ∑ B ∈ D, sigma B / (B : ℝ) :=
    sum_nonneg (fun B hmem => div_nonneg (hsigma B hmem) (Nat.cast_nonneg B))
  have htheta := Theta_lower hN4 Q D sigma hd hsigma hR
  have hpayN : 2 * (N : ℝ) / (N : ℝ)^eta ≤
      (2 * liuUniversalProduct * epsilon) * (N : ℝ) /
        Real.log N ^ 2 := by
    simpa using hpay N hN1
  calc
    weightedSquareEvent N D sigma E y ((N : ℝ)^eta) ≤
        (2 * (N : ℝ) / (N : ℝ)^eta) *
          (∑ B ∈ D, sigma B / (B : ℝ)) :=
      weightedSquareEvent_le_reciprocal_mass N D sigma E y hz hd hsigma
    _ ≤ ((2 * liuUniversalProduct * epsilon) * (N : ℝ) /
          Real.log N ^ 2) *
          (∑ B ∈ D, sigma B / (B : ℝ)) :=
      mul_le_mul_of_nonneg_right hpayN hmass
    _ = epsilon * ((2 * liuUniversalProduct * (N : ℝ) /
          Real.log N ^ 2) *
          (∑ B ∈ D, sigma B / (B : ℝ))) := by ring
    _ ≤ epsilon * Theta N Q D sigma :=
      mul_le_mul_of_nonneg_left htheta hepsilon.le

end
end ImbalancedChen.P2EnhancedW1SquareExceptionPower
