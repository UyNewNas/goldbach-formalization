import ImbalancedChen.P4AOriginalFull87EighthCutoff
import ImbalancedChen.P4AOriginalFull87EighthKernelIntegration
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED / ZERO KERNEL CREDIT.

The manuscript uses full-square tests at each ODD Rosser rank.  A later
ordinary exit can have a last prime smaller than the OWN eighth prefix
prime; the rank-eight cutoff cannot be reused for this.

This packet proves the finite fixed-rank inequality using the actual
sequence of full-square tests at ONE frozen ordinary level beta.  The
potential controls every preceding even-prefix sum, and the first failed
odd test bounds the actual exit coordinate.  This obtains a stronger
beta/3^(m+1) bound at rank j=2*m+1 than the manuscript's conservative
beta/(3*2^(j-1)) estimate.  It also certifies the integer power exponent
and plugs it into the existing target-prime deletion factor.

The original87 owned eighth source separately supplies a uniform POSITIVE
floor for both its own-sixth dynamic parent and its new rounded cap.
The precise obligation that remains is to extract all prior odd square
tests at the SAME frozen ordinary level for actual descendants, including
the inherited tests across the eighth splice.  We do not assume that this
follows merely from membership at rank eight.  No ordinary density
asymptotic, prime distribution input, numerical archive or reserve is
claimed.
-/

namespace ImbalancedChen.P4AOriginalFull87FixedRankExit
noncomputable section

open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87EighthKernelControl
  (cutoff total source_coordinate_lower)
open P4AOriginalFull87EighthKernelIntegration
  (actualParent actual_eighth_kernel_transport)
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87TargetPrimeDeletion
  (targetDeletionFactor target_deletion_power_gap_sandwich)

/-- Sum of the first 2*k processing-order logarithmic coordinates. -/
def evenPrefixMass (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * k), t i

/-- Exact adjoining of a PAIR, with no measure or ordering assumption. -/
theorem evenPrefixMass_succ (t : ℕ → ℝ) (k : ℕ) :
    evenPrefixMass t (k + 1) =
      evenPrefixMass t k + t (2 * k) + t (2 * k + 1) := by
  unfold evenPrefixMass
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  ring

/-- A positive potential survives every prior successful odd full-square
test.  The test at rank 2*k+1 is S_(2*k) + 3*t_(2*k) < beta, exactly the
logarithm of (prefix product)*p_last^2 < N^beta.  Only pairwise
nonincrease t_(2*k+1) <= t_(2*k) is needed; no global volume estimate. -/
theorem odd_square_gap_potential
    (t : ℕ → ℝ) (beta : ℝ) (m : ℕ)
    (hprior : ∀ k < m, evenPrefixMass t k + 3 * t (2 * k) < beta)
    (hpair : ∀ k < m, t (2 * k + 1) ≤ t (2 * k)) :
    ∀ k ≤ m, beta ≤ (3 : ℝ) ^ k * (beta - evenPrefixMass t k) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [evenPrefixMass]
  | succ k ih =>
      intro hk
      have hkm : k < m := by omega
      have hih := ih (by omega : k ≤ m)
      have htest := hprior k hkm
      have hsort := hpair k hkm
      have hsum := evenPrefixMass_succ t k
      have hgap :
          beta - evenPrefixMass t k ≤
            3 * (beta - evenPrefixMass t (k + 1)) := by
        rw [hsum]
        linarith
      have hmul :
          (3 : ℝ) ^ k * (beta - evenPrefixMass t k) ≤
            (3 : ℝ) ^ (k + 1) * (beta - evenPrefixMass t (k + 1)) := by
        calc
          _ ≤ (3 : ℝ) ^ k *
              (3 * (beta - evenPrefixMass t (k + 1))) :=
                mul_le_mul_of_nonneg_left hgap (pow_nonneg (by norm_num) k)
          _ = (3 : ℝ) ^ (k + 1) *
              (beta - evenPrefixMass t (k + 1)) := by
                rw [pow_succ]
                ring
      exact hih.trans hmul

/-- At the FIRST failing odd full-square test, the real exit coordinate
has a quantitative positive floor. The rank is 2*m+1. -/
theorem odd_first_exit_last_log_lower
    (t : ℕ → ℝ) (beta : ℝ) (m : ℕ)
    (hprior : ∀ k < m, evenPrefixMass t k + 3 * t (2 * k) < beta)
    (hpair : ∀ k < m, t (2 * k + 1) ≤ t (2 * k))
    (hexit : beta ≤ evenPrefixMass t m + 3 * t (2 * m)) :
    beta ≤ (3 : ℝ) ^ (m + 1) * t (2 * m) := by
  have hp := odd_square_gap_potential t beta m hprior hpair m le_rfl
  have hh : beta - evenPrefixMass t m ≤ 3 * t (2 * m) := by linarith
  calc
    beta ≤ (3 : ℝ) ^ m * (beta - evenPrefixMass t m) := hp
    _ ≤ (3 : ℝ) ^ m * (3 * t (2 * m)) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg (by norm_num) m)
    _ = (3 : ℝ) ^ (m + 1) * t (2 * m) := by
      rw [pow_succ]
      ring

/-- Real-log exit gap to an INTEGER power gap for the actual last prime.
The only analytic operation is increasing base^exponent at N>1.
The power exponent K is fixed before N, rather than chosen from N. -/
theorem fixed_odd_exit_integer_power_gap
    (N p K m : ℕ) (hN : 1 < (N : ℝ))
    (t : ℕ → ℝ) (betaFloor beta : ℝ)
    (hfloor : 0 < betaFloor) (hbeta : betaFloor ≤ beta)
    (hprior : ∀ k < m, evenPrefixMass t k + 3 * t (2 * k) < beta)
    (hpair : ∀ k < m, t (2 * k + 1) ≤ t (2 * k))
    (hexit : beta ≤ evenPrefixMass t m + 3 * t (2 * m))
    (hreconstruct : (N : ℝ) ^ t (2 * m) = (p : ℝ))
    (hK : (3 : ℝ) ^ (m + 1) < betaFloor * (K : ℝ)) :
    N < p ^ K := by
  have hpow : 0 < (3 : ℝ) ^ (m + 1) := pow_pos (by norm_num) _
  have hlast := odd_first_exit_last_log_lower t beta m hprior hpair hexit
  have hlow : betaFloor ≤ t (2 * m) * (3 : ℝ) ^ (m + 1) := by
    calc
      betaFloor ≤ beta := hbeta
      _ ≤ (3 : ℝ) ^ (m + 1) * t (2 * m) := hlast
      _ = _ := mul_comm _ _
  have hdiv : betaFloor / (3 : ℝ) ^ (m + 1) ≤ t (2 * m) :=
    (div_le_iff₀ hpow).mpr hlow
  have h1 : (1 : ℝ) <
      betaFloor / (3 : ℝ) ^ (m + 1) * (K : ℝ) := by
    have hs := div_lt_div_of_pos_right hK hpow
    rw [div_self hpow.ne'] at hs
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hs
  have h2 := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  have hscale : (1 : ℝ) < t (2 * m) * (K : ℝ) := lt_of_lt_of_le h1 h2
  have hreal : (N : ℝ) < (p : ℝ) ^ K := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < (N : ℝ) ^ (t (2 * m) * (K : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hN hscale
      _ = ((N : ℝ) ^ t (2 * m)) ^ K :=
        Real.rpow_mul_natCast (le_of_lt (zero_lt_one.trans hN)) _ _
      _ = (p : ℝ) ^ K := by rw [hreconstruct]
  exact_mod_cast hreal

/-- Direct finite-rank target-factor payment, using the SAME actual
omitted-prime factor from the previous packet. This is a finite product
inequality, not an assertion of asymptotic density. -/
theorem fixed_odd_exit_deletion_sandwich
    (N p hi k m : ℕ) (hN : 1 < (N : ℝ)) (hp : 3 ≤ p)
    (t : ℕ → ℝ) (betaFloor beta : ℝ)
    (hfloor : 0 < betaFloor) (hbeta : betaFloor ≤ beta)
    (hprior : ∀ i < m, evenPrefixMass t i + 3 * t (2 * i) < beta)
    (hpair : ∀ i < m, t (2 * i + 1) ≤ t (2 * i))
    (hexit : beta ≤ evenPrefixMass t m + 3 * t (2 * m))
    (hreconstruct : (N : ℝ) ^ t (2 * m) = (p : ℝ))
    (hK : (3 : ℝ) ^ (m + 1) < betaFloor * ((k + 1 : ℕ) : ℝ)) :
    0 ≤ targetDeletionFactor N p hi ∧
      targetDeletionFactor N p hi ≤ 1 ∧
      1 - (k : ℝ) / ((p : ℝ) - 1) ≤ targetDeletionFactor N p hi := by
  have hgap := fixed_odd_exit_integer_power_gap N p (k + 1) m hN
    t betaFloor beta hfloor hbeta hprior hpair hexit hreconstruct hK
  have hpos : 0 < N := by
    have hreal : (0 : ℝ) < N := (by norm_num : (0 : ℝ) < 1).trans hN
    exact_mod_cast hreal
  exact target_deletion_power_gap_sandwich N p hi k hpos hp hgap

/-- Actual original87 source geometry supplies a uniform POSITIVE lower
level, independently of the fixed rank of a later ordinary exit. -/
theorem source_comparison_level_floor {c : Cell} {t : Point}
    (hs : Source c t) : 9 * cutoff < comparison c t := by
  have hsum0 :
      (∑ _i : Fin 8, cutoff) ≤ ∑ i : Fin 8, t i :=
    Finset.sum_le_sum (fun i _ => (source_coordinate_lower hs i).le)
  have hconst : (∑ _i : Fin 8, cutoff) = 8 * cutoff := by
    norm_num
  have hsum : 8 * cutoff ≤ total t := by
    simpa only [total, hconst] using hsum0
  have hlast := source_coordinate_lower hs (7 : Fin 8)
  have hres := source_residual_range hs
  linarith [hres.2.1]

/-- The two ACTUAL levels of the owned rank-eight source (licensed own-sixth
parent, and finite rounded new cap) both exceed the same fixed 9*cutoff.
This does not pretend that subsequent first exits are still rank eight. -/
theorem owned_eighth_actual_levels_floor
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om N : ℝ) (history : List ℕ)
    (hlen : history.length = 8) (c : Cell)
    (ht : primeHistoryLogCoordinates N 8 history ∈ trim c (width r))
    (hr : RealizedHistory e q om N history c) :
    9 * cutoff < actualParent n e q om N history ∧
      9 * cutoff <
        (finiteCap n c (primeHistoryLogCoordinates N 8 history) : ℝ) := by
  let t := primeHistoryLogCoordinates N 8 history
  have hs : Source c t := trim_subset_source c (width_pos r) ht
  have hsum0 : (∑ _i : Fin 8, cutoff) ≤ ∑ i : Fin 8, t i :=
    Finset.sum_le_sum (fun i _ => (source_coordinate_lower hs i).le)
  have hconst : (∑ _i : Fin 8, cutoff) = 8 * cutoff := by norm_num
  have hsum : 8 * cutoff ≤ total t := by
    simpa only [total, hconst] using hsum0
  have hlast := source_coordinate_lower hs (7 : Fin 8)
  have htrans := actual_eighth_kernel_transport r n hn e q om N history hlen c ht hr
  dsimp only at htrans
  obtain ⟨_, hparent, _, hnew, _, _⟩ := htrans
  have hp : 9 * cutoff < actualParent n e q om N history := by
    dsimp only [t] at *
    linarith
  have hcomparison := source_comparison_level_floor hs
  exact ⟨hp, hcomparison.trans hnew⟩

/-- A uniform INTEGER schedule for finite-rank odd exits at both actual
levels. Because 30*(9*53/13824)>1, the power is 30*3^(m+1), fixed
before the target N. -/
theorem fixed_rank_uniform87_integer_factor (m : ℕ) :
    (3 : ℝ) ^ (m + 1) <
      (9 * cutoff) * ((30 * 3 ^ (m + 1) : ℕ) : ℝ) := by
  have hb : (1 : ℝ) < (9 * cutoff) * 30 := by norm_num [cutoff]
  have hp : (0 : ℝ) < 3 ^ (m + 1) := pow_pos (by norm_num) _
  have hh := mul_lt_mul_of_pos_right hb hp
  push_cast
  convert hh using 1 <;> ring


/-- Concrete ORIGINAL87 adapter for either actual frozen level. The only
unpaid hypothesis is that the actual deeper ordinary exit's successive odd
square tests, in processing order, agree with hprior/hexit at THIS SAME
level. Merely knowing rank-eight membership is not used as such a test. -/
theorem owned_eighth_ordinary_fixed_rank_deletion
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ)
    (hN : 1 < (N : ℝ)) (history : List ℕ)
    (hlen : history.length = 8) (c : Cell)
    (ht : primeHistoryLogCoordinates (N : ℝ) 8 history ∈ trim c (width r))
    (hr : RealizedHistory e q om (N : ℝ) history c)
    (t : ℕ → ℝ) (m p hi : ℕ) (hp : 3 ≤ p)
    (beta : ℝ)
    (hlevel : beta = actualParent n e q om (N : ℝ) history ∨
      beta = (finiteCap n c
        (primeHistoryLogCoordinates (N : ℝ) 8 history) : ℝ))
    (hprior : ∀ i < m, evenPrefixMass t i + 3 * t (2 * i) < beta)
    (hpair : ∀ i < m, t (2 * i + 1) ≤ t (2 * i))
    (hexit : beta ≤ evenPrefixMass t m + 3 * t (2 * m))
    (hreconstruct : (N : ℝ) ^ t (2 * m) = (p : ℝ)) :
    0 ≤ targetDeletionFactor N p hi ∧
      targetDeletionFactor N p hi ≤ 1 ∧
      1 - ((30 * 3 ^ (m + 1) : ℕ) : ℝ) / ((p : ℝ) - 1) ≤
        targetDeletionFactor N p hi := by
  have hlevels := owned_eighth_actual_levels_floor
    r n hn e q om (N : ℝ) history hlen c ht hr
  have hbeta : 9 * cutoff ≤ beta := by
    rcases hlevel with he | he
    · rw [he]
      exact hlevels.1.le
    · rw [he]
      exact hlevels.2.le
  have hfloor : 0 < 9 * cutoff := mul_pos (by norm_num) cutoff_pos
  have hK : (3 : ℝ) ^ (m + 1) <
      (9 * cutoff) * (((30 * 3 ^ (m + 1) : ℕ) + 1 : ℕ) : ℝ) := by
    have hfixed := fixed_rank_uniform87_integer_factor m
    have hn : ((30 * 3 ^ (m + 1) : ℕ) : ℝ) ≤
        (((30 * 3 ^ (m + 1) : ℕ) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ (30 * 3 ^ (m + 1))
    exact hfixed.trans_le (mul_le_mul_of_nonneg_left hn hfloor.le)
  exact fixed_odd_exit_deletion_sandwich N p hi
    (30 * 3 ^ (m + 1)) m hN hp t (9 * cutoff) beta
    hfloor hbeta hprior hpair hexit hreconstruct hK

end
end ImbalancedChen.P4AOriginalFull87FixedRankExit
