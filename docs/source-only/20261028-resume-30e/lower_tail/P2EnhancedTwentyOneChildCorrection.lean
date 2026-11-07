import ImbalancedChen.P2EnhancedNegativeChildRosser

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
The signed correction of the ORIGINAL same-Q 21-term source comparison.
Its negative-child part is the proved ordinary lower Rosser estimator,
with the exact same coefficient in the true coprime mean and AP remainder.
The two positive pairs and the entire marked switched source remain
literal counts. No H248 endpoint or positive-K cost is a hypothesis. -/

namespace ImbalancedChen.P2EnhancedTwentyOneChildCorrection

noncomputable section
open scoped Classical BigOperators
open Wu2008DoubleSieve P2EnhancedTwentyOneSameQWeighted
open P2EnhancedTwentyOneQuotientFinite P2EnhancedNegativeChildRosser

def localNegativeEstimator (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  windowEstimator N Q d (cutoff Q d (11 / 5)) +
  windowEstimator N Q d (cutoff Q d (29 / 10)) +
  windowEstimator N Q d (cutoff Q d (61 / 25))

def localNegativeMean (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  windowMean N Q d (cutoff Q d (11 / 5)) +
  windowMean N Q d (cutoff Q d (29 / 10)) +
  windowMean N Q d (cutoff Q d (61 / 25))

def localNegativeRemainder (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  windowSignedRemainder N Q d (cutoff Q d (11 / 5)) +
  windowSignedRemainder N Q d (cutoff Q d (29 / 10)) +
  windowSignedRemainder N Q d (cutoff Q d (61 / 25))

def localPositivePairs (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  fourthRowMotherPair N d N (cutoff Q d (227 / 50)) (cutoff Q d (29 / 10))
    (cutoff Q d (227 / 50)) (cutoff Q d (29 / 10)) +
  fourthRowMotherPair N d N (cutoff Q d (227 / 50)) (cutoff Q d (353 / 100))
    (cutoff Q d (29 / 10)) (cutoff Q d (61 / 25))

/-- All original Gamma7--Gamma21 marked occurrences, including repeated
word occurrences and the unit quotient surfaces. -/
def localSwitched (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  quotientSwitched N d N (cutoff Q d (227 / 50)) (cutoff Q d (353 / 100))
    (cutoff Q d (29 / 10)) (cutoff Q d (61 / 25)) (cutoff Q d (11 / 5))

def negativeMean (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * localNegativeMean N Q d

def negativeSignedRemainder (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * localNegativeRemainder N Q d

def positivePairs (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * localPositivePairs N Q d

def switchedCount (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * localSwitched N Q d

def negativeFiniteCoprimeMean (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d *
    (windowFiniteCoprimeMean N Q d (cutoff Q d (11 / 5)) +
      windowFiniteCoprimeMean N Q d (cutoff Q d (29 / 10)) +
      windowFiniteCoprimeMean N Q d (cutoff Q d (61 / 25)))

def negativeFiniteSignedRemainder (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d *
    (windowFiniteSignedRemainder N Q d (cutoff Q d (11 / 5)) +
      windowFiniteSignedRemainder N Q d (cutoff Q d (29 / 10)) +
      windowFiniteSignedRemainder N Q d (cutoff Q d (61 / 25)))

/-- A correction to a true Phi count, not a modification of ordinary rho
or a definition forcing its density to equal an enhanced table. -/
def signedChildCorrection (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  negativeMean N Q D sigma + negativeSignedRemainder N Q D sigma -
    positivePairs N Q D sigma - switchedCount N Q D sigma

theorem localNegativeEstimator_eq (N : ℕ) (Q : ℝ) (d : ℕ) :
    localNegativeEstimator N Q d = localNegativeMean N Q d + localNegativeRemainder N Q d := by
  simp only [localNegativeEstimator, localNegativeMean, localNegativeRemainder,
    windowEstimator_eq_mean_add_signed_remainder]
  ring

/-- The signed correction also keeps the ORIGINAL exact finite coprime
population mean. Replacing that mean by li(N) changes its remainder by
the opposite signed finite amount, not by an unproved o(Theta). -/
theorem signedChildCorrection_eq_finite_coprime_split (N : ℕ) (Q : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) :
    signedChildCorrection N Q D sigma =
      negativeFiniteCoprimeMean N Q D sigma + negativeFiniteSignedRemainder N Q D sigma -
        positivePairs N Q D sigma - switchedCount N Q D sigma := by
  have hneg : negativeMean N Q D sigma + negativeSignedRemainder N Q D sigma =
      negativeFiniteCoprimeMean N Q D sigma + negativeFiniteSignedRemainder N Q D sigma := by
    unfold negativeMean negativeSignedRemainder negativeFiniteCoprimeMean negativeFiniteSignedRemainder
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    have hlocal : localNegativeMean N Q d + localNegativeRemainder N Q d =
        (windowFiniteCoprimeMean N Q d (cutoff Q d (11 / 5)) +
        windowFiniteCoprimeMean N Q d (cutoff Q d (29 / 10)) +
        windowFiniteCoprimeMean N Q d (cutoff Q d (61 / 25))) +
        (windowFiniteSignedRemainder N Q d (cutoff Q d (11 / 5)) +
        windowFiniteSignedRemainder N Q d (cutoff Q d (29 / 10)) +
        windowFiniteSignedRemainder N Q d (cutoff Q d (61 / 25))) := by
      rw [← localNegativeEstimator_eq]
      simp only [localNegativeEstimator, windowEstimator_eq_finite_mean_add_remainder]
      ring
    rw [← mul_add, ← mul_add, hlocal]
  unfold signedChildCorrection
  rw [hneg]

/-- Every negative window is controlled using its own literal endpoints;
the largest endpoint is used only to prove the inherited level gate. -/
theorem localNegativeEstimator_le {N d : ℕ} {Q : ℝ}
    (hd : 0 < d) (hR : 1 < Q / (d : ℝ)) :
    localNegativeEstimator N Q d ≤
      fourthRowMotherSingle N d N (cutoff Q d (227 / 50)) (cutoff Q d (11 / 5)) +
      fourthRowMotherSingle N d N (cutoff Q d (227 / 50)) (cutoff Q d (29 / 10)) +
      fourthRowMotherSingle N d N (cutoff Q d (227 / 50)) (cutoff Q d (61 / 25)) := by
  obtain ⟨hab, hbc, hce, hef⟩ := cutoff_order Q d hR.le
  exact add_le_add (add_le_add (windowEstimator_le_single hd hR le_rfl)
    (windowEstimator_le_single hd hR (hce.trans hef)))
    (windowEstimator_le_single hd hR hef)

/-- This finite source step changes the three genuine negative counts to
their proved lower estimators. No analytic child mean bound is assumed. -/
theorem weightedQuotient_le_baseline_sub_correction
    (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hR : ∀ d ∈ D, 1 < Q / (d : ℝ)) :
    weightedQuotient N Q D sigma ≤
      4 * Phi N Q D sigma (227 / 50) + Phi N Q D sigma (353 / 100) -
        signedChildCorrection N Q D sigma := by
  have hlocal (d : ℕ) (hmem : d ∈ D) :
      localQuotient N Q d ≤
        4 * (sourceSieveCount N d (d * N) (cutoff Q d (227 / 50)) : ℝ) +
        (sourceSieveCount N d (d * N) (cutoff Q d (353 / 100)) : ℝ) -
        localNegativeMean N Q d - localNegativeRemainder N Q d +
        localPositivePairs N Q d + localSwitched N Q d := by
    have hneg := localNegativeEstimator_le (hd d hmem) (hR d hmem)
    rw [localNegativeEstimator_eq] at hneg
    unfold localQuotient quotientLocal localPositivePairs localSwitched
    linarith
  calc
    weightedQuotient N Q D sigma ≤ ∑ d ∈ D, sigma d *
        (4 * (sourceSieveCount N d (d * N) (cutoff Q d (227 / 50)) : ℝ) +
        (sourceSieveCount N d (d * N) (cutoff Q d (353 / 100)) : ℝ) -
        localNegativeMean N Q d - localNegativeRemainder N Q d +
        localPositivePairs N Q d + localSwitched N Q d) := by
      apply Finset.sum_le_sum
      intro d hmem
      exact mul_le_mul_of_nonneg_left (hlocal d hmem) (hsigma d hmem)
    _ = _ := by
      unfold Phi signedChildCorrection negativeMean negativeSignedRemainder positivePairs switchedCount
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]
      have hfour : (∑ d ∈ D, sigma d *
          (4 * (sourceSieveCount N d (d * N) (cutoff Q d (227 / 50)) : ℝ))) =
          ∑ d ∈ D, 4 * (sigma d *
            (sourceSieveCount N d (d * N) (cutoff Q d (227 / 50)) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d _
        ring
      rw [hfour]
      ring

/-- Small N version: all original collision and bad-prime corrections are
visible, with the actual original Theta not yet used for payment. -/
theorem finite_signed_child_correction (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hR : ∀ d ∈ D, 1 < Q / (d : ℝ)) :
    5 * Phi N Q D sigma (11 / 5) + signedChildCorrection N Q D sigma ≤
      4 * Phi N Q D sigma (227 / 50) + Phi N Q D sigma (353 / 100) +
        weightedCollisions N Q D sigma + weightedBadPrimes N Q D sigma := by
  have hf := weighted_sameQ_finite N Q D sigma hsigma (fun d hmem => (hR d hmem).le)
  have hc := weightedQuotient_le_baseline_sub_correction N Q D sigma hd hsigma hR
  linarith

/-- The actual eventual signed correction at one common Q, common sigma,
common old mask, and the original Theta_Q. Thresholds are chosen before
N,Q,D,sigma. All analytical enhancement costs remain separate. -/
theorem actual_sameQ_signed_child_correction {eta epsilon : ℝ} (heta : 0 < eta)
    (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) →
      5 * Phi N Q D sigma (11 / 5) + signedChildCorrection N Q D sigma ≤
        4 * Phi N Q D sigma (227 / 50) + Phi N Q D sigma (353 / 100) +
          epsilon * Theta N Q D sigma := by
  obtain ⟨T, hT, hcompare⟩ :=
    P2EnhancedTwentyOneSourceComparison.twentyOne_source_comparison heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT he Q D sigma hQN hd hsigma hR hold hcut
  have hf := hcompare N hNT he Q D sigma hQN hd hsigma hR hold hcut
  have hc := weightedQuotient_le_baseline_sub_correction N Q D sigma hd hsigma hR
  linarith

end
end ImbalancedChen.P2EnhancedTwentyOneChildCorrection
