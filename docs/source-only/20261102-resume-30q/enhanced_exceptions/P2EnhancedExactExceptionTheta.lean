import ImbalancedChen.P2EnhancedExactExceptionFinite
import ImbalancedChen.P2EnhancedCollisionThetaPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The twenty original switched occurrences and the separate bad Gamma5
receive one uniform same-Theta error budget. Primitive old/new cutoff
conditions are instantiated from marked prime boxes in the next file.
No receiver primality is removed before paying the center error.
-/

namespace ImbalancedChen.P2EnhancedExactExceptionTheta
noncomputable section
open Finset Filter Wu2008DoubleSieve
open P2EnhancedReceiverRoughPurification P2EnhancedSwitchedUnsiftedSource
open P2EnhancedExactExceptionFinite P2EnhancedCollisionWeightedBudget
open P2EnhancedTwentyOneSameQWeighted P2EnhancedThetaReciprocalMass
open P2EnhancedCollisionThetaPayment
open MathlibNt.SieveTheory.SingularSeries
open scoped Classical BigOperators Topology

def errorCoefficient (eta : ℝ) : ℝ :=
  64/eta + (max 1 (1/eta))^6 / Real.log 2

theorem errorCoefficient_pos {eta : ℝ} (heta : 0 < eta) :
    0 < errorCoefficient eta := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold errorCoefficient
  positivity

/-- The source's NEW cutoff supplies the factor 1/d also in the center
budget. It is incorrect to replace sum sigma/d by sum sigma without this. -/
theorem residual_saving {N d : ℕ} {Q eta : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hQ : Q ≤ (N : ℝ))
    (hR : 1 ≤ Q/(d : ℝ)) (hcut : (N : ℝ)^eta ≤ cutoff Q d (227/50)) :
    1 ≤ (N : ℝ)/((d : ℝ)*(N : ℝ)^eta) := by
  have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn : 0 < (N : ℝ)^eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
  have hc : cutoff Q d (227/50) ≤ Q/(d : ℝ) := by
    unfold cutoff
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR
      (by norm_num : 1/(227/50 : ℝ) ≤ 1)
  have hh : (N : ℝ)^eta ≤ (N : ℝ)/(d : ℝ) :=
    (hcut.trans hc).trans (div_le_div_of_nonneg_right hQ hdr.le)
  apply (one_le_div (mul_pos hdr hn)).mpr
  have hm := (le_div_iff₀ hdr).mp hh
  simpa only [mul_comm] using hm

/-- A common coefficient for all original arities, derived from the
two finite bounds. This is a scalar power-log estimate, not a mass premise. -/
theorem rank_budget {N d r : ℕ} {Q eta : ℝ}
    (hN : 0 < N) (hd : 0 < d) (heta : 0 < eta)
    (hQ : Q ≤ (N : ℝ)) (hR : 1 ≤ Q/(d : ℝ))
    (hcut : (N : ℝ)^eta ≤ cutoff Q d (227/50))
    (hlog : 1 ≤ Real.log (N : ℝ)) (hr : r ≤ 6) :
    collisionScale N d eta * (1+Real.log N)^r +
        (1/eta)^r * Real.log N / Real.log 2 ≤
      errorCoefficient eta * N * Real.log N^6 / ((d : ℝ)*(N : ℝ)^eta) := by
  let X : ℝ := (N : ℝ)/((d : ℝ)*(N : ℝ)^eta)
  let H : ℝ := max 1 (1/eta)
  have hX : 1 ≤ X := residual_saving hN hd hQ hR hcut
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hH : 1 ≤ H := le_max_left _ _
  have hlog0 : 0 ≤ Real.log (N : ℝ) := zero_le_one.trans hlog
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ha : (1+Real.log (N : ℝ))^r ≤ 64*Real.log N^6 := by
    calc
      _ ≤ (1+Real.log N)^6 := pow_le_pow_right₀ (by linarith) hr
      _ ≤ (2*Real.log N)^6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      _ = _ := by ring
  have hb : (1/eta)^r ≤ H^6 :=
    (pow_le_pow_left₀ (by positivity) (le_max_right 1 (1/eta)) r).trans
      (pow_le_pow_right₀ hH hr)
  have hl : Real.log (N : ℝ) ≤ Real.log N^6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hlog (by norm_num : (1 : ℕ) ≤ 6)
  have hrepeat : collisionScale N d eta * (1+Real.log N)^r ≤
      (64/eta)*X*Real.log N^6 := by
    calc
      _ ≤ collisionScale N d eta * (64*Real.log N^6) :=
        mul_le_mul_of_nonneg_left ha (collisionScale_nonneg N d heta)
      _ = _ := by dsimp [collisionScale, X]; ring
  have hcenter : (1/eta)^r * Real.log N / Real.log 2 ≤
      (H^6/Real.log 2)*X*Real.log N^6 := by
    calc
      _ ≤ H^6 * Real.log N^6 / Real.log 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul hb hl hlog0 (by positivity)) hlog2.le
      _ = (H^6/Real.log 2)*Real.log N^6 := by ring
      _ ≤ ((H^6/Real.log 2)*Real.log N^6)*X := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hX
          (by positivity : 0 ≤ (H^6/Real.log 2)*Real.log N^6)
      _ = _ := by ring
  calc
    _ ≤ (64/eta)*X*Real.log N^6 + (H^6/Real.log 2)*X*Real.log N^6 :=
      add_le_add hrepeat hcenter
    _ = _ := by dsimp [errorCoefficient, X, H]; ring

def localErrors (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  badPairRepeat N Q d + badPairCenter N Q d +
    ∑ j : Fin 13, ((secondFunctionalMotherGammaWords (9+j.val)).map
      (fun cs => repeatWordMass N Q d cs + centerWordMass N Q d cs)).sum

def weightedErrors (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * localErrors N Q d

theorem original_word_arity {i : ℕ} (hi : 9 ≤ i) (hi' : i ≤ 21)
    {cs : List ℕ} (hc : cs ∈ secondFunctionalMotherGammaWords i) : cs.length ≤ 6 := by
  interval_cases i <;> simp_all [secondFunctionalMotherGammaWords] <;> aesop

/-- The sum has all TWENTY occurrences, including both 112 and both 122.
The additional one is the bad Gamma5 family, not an ordinary feedback term. -/
theorem localErrors_le {N d : ℕ} {Q eta : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (heta : 0 < eta)
    (hQ : Q ≤ (N : ℝ)) (hR : 1 ≤ Q/(d : ℝ))
    (hold : ∀ p ∈ d.primeFactors, (N : ℝ)^eta ≤ (p : ℝ))
    (hcut : (N : ℝ)^eta ≤ cutoff Q d (227/50)) (hlog : 1 ≤ Real.log (N : ℝ)) :
    localErrors N Q d ≤
      21*errorCoefficient eta*N*Real.log N^6/((d : ℝ)*(N : ℝ)^eta) := by
  let B : ℝ := errorCoefficient eta*N*Real.log N^6/((d : ℝ)*(N : ℝ)^eta)
  have hword (cs : List ℕ) (hr : cs.length ≤ 6) :
      repeatWordMass N Q d cs + centerWordMass N Q d cs ≤ B :=
    (add_le_add (word_errors_le cs hN he hd heta hQ hR hold hcut).1
      (word_errors_le cs hN he hd heta hQ hR hold hcut).2).trans
      (rank_budget (by omega) hd heta hQ hR hcut hlog hr)
  have hpair : badPairRepeat N Q d + badPairCenter N Q d ≤ B :=
    (add_le_add (badPair_errors_le hN he hd heta hQ hR hold hcut).1
      (badPair_errors_le hN he hd heta hQ hR hold hcut).2).trans
      (rank_budget (by omega) hd heta hQ hR hcut hlog (by norm_num : (2 : ℕ) ≤ 6))
  have hsum : (∑ j : Fin 13, ((secondFunctionalMotherGammaWords (9+j.val)).map
      (fun cs => repeatWordMass N Q d cs + centerWordMass N Q d cs)).sum) ≤ 20*B := by
    calc
      _ ≤ ∑ j : Fin 13, ((secondFunctionalMotherGammaWords (9+j.val)).map
          (fun _ => B)).sum := by
        apply sum_le_sum
        intro j _
        exact secondFunctionalMother_list_sum_mono _ _ _
          (fun cs hcs => hword cs (original_word_arity (by omega) (by omega) hcs))
      _ = _ := by rw [all_switched_multiplicities]; ring
  change badPairRepeat N Q d + badPairCenter N Q d + _ ≤ _
  have h := add_le_add hpair hsum
  convert h using 1 <;> dsimp [B] <;> ring

/-- Threshold chosen before the moving original support, weights and Q.
Empty or zero-weight families are allowed, with no division by Theta. -/
theorem exact_errors_theta_payment {eta epsilon : ℝ} (heta : 0 < eta)
    (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q/(d : ℝ)) →
      (∀ d ∈ D, ∀ p ∈ d.primeFactors, (N : ℝ)^eta ≤ (p : ℝ)) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ cutoff Q d (227/50)) →
      weightedErrors N Q D sigma ≤ epsilon*Theta N Q D sigma := by
  have hU := liuUniversalProduct_pos
  obtain ⟨T1, hT1, hpay⟩ := ninth_power_log_error_budget 6
    (C := 21*errorCoefficient eta) (α := eta)
    (ε := 2*liuUniversalProduct*epsilon)
    (mul_pos (by norm_num) (errorCoefficient_pos heta)) heta (by positivity)
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T2, hlogT⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T1 T2, by omega, ?_⟩
  intro N hNT he Q D sigma hQ hd hsigma hR hold hcut
  have hN1 := (le_max_left T1 T2).trans hNT
  have hN4 : 4 ≤ N := by omega
  have hlog := hlogT N ((le_max_right T1 T2).trans hNT)
  have hmass : 0 ≤ ∑ d ∈ D, sigma d/(d : ℝ) :=
    sum_nonneg (fun d hd' => div_nonneg (hsigma d hd') (Nat.cast_nonneg d))
  have htheta := Theta_lower hN4 Q D sigma hd hsigma
    (fun d hmem => ⟨hR d hmem, residual_level_le_N (hd d hmem) hQ⟩)
  calc
    weightedErrors N Q D sigma ≤ ∑ d ∈ D, sigma d *
        (21*errorCoefficient eta*N*Real.log N^6/((d : ℝ)*(N : ℝ)^eta)) := by
      apply sum_le_sum
      intro d hmem
      exact mul_le_mul_of_nonneg_left
        (localErrors_le hN4 he (hd d hmem) heta hQ (hR d hmem).le
          (hold d hmem) (hcut d hmem) hlog) (hsigma d hmem)
    _ = (21*errorCoefficient eta*N*Real.log N^6/(N : ℝ)^eta) *
        ∑ d ∈ D, sigma d/(d : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ ((2*liuUniversalProduct*epsilon)*N/Real.log N^2) *
        ∑ d ∈ D, sigma d/(d : ℝ) :=
      mul_le_mul_of_nonneg_right (hpay N hN1) hmass
    _ = epsilon*((2*liuUniversalProduct*N/Real.log N^2) *
        ∑ d ∈ D, sigma d/(d : ℝ)) := by ring
    _ ≤ epsilon*Theta N Q D sigma := mul_le_mul_of_nonneg_left htheta hepsilon.le

/-- Reuse the previous selected-collision supplier verbatim. This theorem
does not identify it with either of the two new exact events. -/
theorem all_retained_errors_theta_payment {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q/(d : ℝ)) →
      (∀ d ∈ D, ∀ p ∈ d.primeFactors, (N : ℝ)^eta ≤ (p : ℝ)) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ cutoff Q d (227/50)) →
      weightedErrors N Q D sigma + weightedCollisions N Q D sigma ≤
        epsilon*Theta N Q D sigma := by
  obtain ⟨T1,hT1,h1⟩ := exact_errors_theta_payment heta (by positivity : 0 < epsilon/2)
  obtain ⟨T2,hT2,h2⟩ := collision_theta_payment heta (by positivity : 0 < epsilon/2)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hNT he Q D sigma hQ hd hsigma hR hold hcut
  have ha := h1 N ((le_max_left T1 T2).trans hNT) he Q D sigma hQ hd hsigma hR hold hcut
  have hb := h2 N ((le_max_right T1 T2).trans hNT) he Q D sigma hQ hd hsigma hR hold hcut
  linarith

end
end ImbalancedChen.P2EnhancedExactExceptionTheta
