import ImbalancedChen.P2EnhancedNegativeChildSignedModulus
import ImbalancedChen.P2EnhancedNegativeChildLogGeometry

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Insert the actual signed physical coefficient into the true Phi source
comparison. Split only by an independently meaningful physical alpha
gate, retaining the complete original fallback Phi count. Positive pairs,
all marked switched counts and analytic errors still require payment. -/

namespace ImbalancedChen.P2EnhancedTwentyOnePhysicalReceiver

noncomputable section
open scoped Classical BigOperators
open P2EnhancedTwentyOneSameQWeighted P2EnhancedTwentyOneChildCorrection
open P2EnhancedNegativeChildRosser P2EnhancedNegativeChildSignedModulus
open P2OriginalSelectedIntegerPrefixSquares P2OriginalSelectedNativeSmallExtension

def alphaAdmitted (N : ℕ) (Q : ℝ) (D : Finset ℕ) : Finset ℕ :=
  D.filter (fun d => Q ^ 2 ≤ (N : ℝ) * d)

def alphaFallback (N : ℕ) (Q : ℝ) (D : Finset ℕ) : Finset ℕ :=
  D.filter (fun d => ¬ Q ^ 2 ≤ (N : ℝ) * d)

theorem Phi_exact_alpha_split (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (w : ℝ) :
    Phi N Q D sigma w = Phi N Q (alphaAdmitted N Q D) sigma w +
      Phi N Q (alphaFallback N Q D) sigma w := by
  unfold Phi alphaAdmitted alphaFallback
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hg : Q ^ 2 ≤ (N : ℝ) * d <;> simp [hg]

theorem admitted_actual_child_alpha {N d p : ℕ} {Q : ℝ} {D : Finset ℕ}
    (hd : ∀ d ∈ D, 0 < d) (hR : ∀ d ∈ D, 1 < Q / (d : ℝ)) (hQN : Q ≤ (N : ℝ))
    (hdA : d ∈ alphaAdmitted N Q D) (j : Fin 3)
    (hp : p ∈ P2OriginalNegativeSingleSameQSupport.negativeWindow N Q d j) :
    2 ≤ P2EnhancedNegativeChildLogGeometry.childAlpha N Q d p := by
  have hdata := Finset.mem_filter.mp hdA
  exact P2EnhancedNegativeChildLogGeometry.actual_child_alpha_ge_two
    (hd d hdata.1) (hR d hdata.1) hQN hdata.2 j hp

/-- Every actual marked coefficient in the physical pushforward inherits
the full and selected-complement gates of the independently fixed old
tagged prefix. Its j and p are the original source labels from marks. -/
theorem marked_coefficient_original_gates (N : ℕ) (cap : ℝ) (D : Finset ℕ)
    (hd : ∀ d ∈ D, 0 < d) (hR : ∀ d ∈ D, 1 < (N : ℝ)^cap / (d : ℝ))
    {m : Mark} (hm : m ∈ marks N ((N : ℝ)^cap) D)
    (old : List (ℕ × Bool)) (holdprod : (old.map Prod.fst).prod = m.1.1)
    (hfull : IntegerSquareGates N cap 1 (old.map Prod.fst))
    (hselected : IntegerSquareGates N cap (selectedPrimes old).prod (remainingPrimes old)) :
    let afterP := appendUnselected old [m.1.2.2]
    let whole := appendUnselected afterP m.2.primeFactorsList.reverse
    IntegerSquareGates N cap 1 (whole.map Prod.fst) ∧
      IntegerSquareGates N cap (selectedPrimes whole).prod (remainingPrimes whole) ∧
      selectedPrimes whole = selectedPrimes old ∧
      (whole.map Prod.fst).prod = physicalModulus m ∧
      ((physicalModulus m : ℕ) : ℝ) < (N : ℝ)^cap := by
  obtain ⟨hdm, hp, hk⟩ := mark_original_data hm
  exact P2EnhancedNegativeChildPhysicalSupport.count_coefficient_complete_gates
    N cap (hd _ hdm) (hR _ hdm) m.1.2.1 hp hk old holdprod hfull hselected

/-- Both actual means/error decompositions reconstruct this SAME signed
original prime count, not an enhanced density coefficient. -/
theorem negative_mean_add_error_eq_physical_count
    (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    negativeMean N Q D sigma + negativeSignedRemainder N Q D sigma =
      ∑ q ∈ modulusSupport N Q D, physicalCoefficient N Q D sigma q * rawPrimeAPCount N q := by
  rw [model_mean_pushforward, model_error_pushforward, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Original true Phi count with the actual full-modulus negative source.
No quantitative positive-K, AP-error or enhanced-table premise. -/
theorem actual_sameQ_physical_receiver {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) →
      5 * Phi N Q D sigma (11 / 5) +
        (∑ q ∈ modulusSupport N Q D, physicalCoefficient N Q D sigma q * rawPrimeAPCount N q) ≤
        4 * Phi N Q D sigma (227 / 50) + Phi N Q D sigma (353 / 100) +
          positivePairs N Q D sigma + switchedCount N Q D sigma + epsilon * Theta N Q D sigma := by
  obtain ⟨T, hT, hsource⟩ := actual_sameQ_signed_child_correction heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT he Q D sigma hQN hd hsigma hR hold hcut
  have h := hsource N hNT he Q D sigma hQN hd hsigma hR hold hcut
  unfold signedChildCorrection at h
  rw [negative_mean_add_error_eq_physical_count] at h
  linarith

/-- Only prefixes with the real physical alpha gate receive the child
receiver. Every other original Phi term stays as a literal fallback;
neither its mass nor its count is declared negligible. -/
theorem actual_receiver_with_alpha_fallback {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) →
      let A := alphaAdmitted N Q D
      5 * Phi N Q D sigma (11 / 5) ≤
        4 * Phi N Q A sigma (227 / 50) + Phi N Q A sigma (353 / 100) -
          (∑ q ∈ modulusSupport N Q A, physicalCoefficient N Q A sigma q * rawPrimeAPCount N q) +
          positivePairs N Q A sigma + switchedCount N Q A sigma +
          5 * Phi N Q (alphaFallback N Q D) sigma (11 / 5) + epsilon * Theta N Q A sigma := by
  obtain ⟨T, hT, hsource⟩ := actual_sameQ_physical_receiver heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT he Q D sigma hQN hd hsigma hR hold hcut
  dsimp only
  have h := hsource N hNT he Q (alphaAdmitted N Q D) sigma hQN
    (fun d hmem => hd d (Finset.mem_filter.mp hmem).1)
    (fun d hmem => hsigma d (Finset.mem_filter.mp hmem).1)
    (fun d hmem => hR d (Finset.mem_filter.mp hmem).1)
    (fun d hmem => hold d (Finset.mem_filter.mp hmem).1)
    (fun d hmem => hcut d (Finset.mem_filter.mp hmem).1)
  rw [Phi_exact_alpha_split N Q D sigma (11 / 5)]
  linarith

end
end ImbalancedChen.P2EnhancedTwentyOnePhysicalReceiver
