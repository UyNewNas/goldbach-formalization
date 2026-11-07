import ImbalancedChen.P2OriginalElevenAffineEndpointCompiler
import ImbalancedChen.P2OriginalElevenActualOmittedMeanPayment
import ImbalancedChen.P1Pair12RetainedSignedSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The concrete ELEVEN endpoint sixth maximum is installed into the actual
policy8 constructor. It retains the real original upstream seed/history
and the original eighth rules. The full marked count-minus-exact-coprime-
mean identity is proved by an independent first-disagreement recursion.
The remainder is an actual common-exit sum with sign-sensitive full-small
tails. It is NOT DEFINED as the desired source difference.

The sixth geometric decision bands are proved in the imported module.
Full policy8 disagreement containment (upstream parent, eighth choice and
later ordinary comparisons) and the analytic wall payment remain OPEN.
-/
namespace ImbalancedChen.P2OriginalElevenEndpointMarkedSource
noncomputable section
open Classical
open scoped BigOperators
open P5OriginalCommonRefinedConstructor
open P2OriginalElevenAffineEndpointCompiler
open P1Pair12RetainedSignedSource
open P2OriginalElevenCompactGatedPolicy
open P2OriginalElevenActualOmittedMeanPayment

/-- Independently defined endpoint replacement at the actual sixth node;
no equality with raw policy8 and no new source supplier are postulated. -/
def endpointPolicy8 (d : OriginalData) (N : ℝ) (tau : ℝ) : Bool → List ℕ → Bool :=
  P5OriginalAdoptedEighthPhysicalMasks.familyPolicy N
    (lambda3 d N) (endpointLambda6 d N tau) (policy5 d N)

theorem endpointPolicy8_even (d : OriginalData) (N tau : ℝ) (pre : List ℕ) :
    endpointPolicy8 d N tau true pre = true :=
  P5OriginalAdoptedEighthPhysicalMasks.family_even N (lambda3 d N)
    (endpointLambda6 d N tau) (policy5 d N) (policy5_even d N) pre

def endpointQ (d : OriginalData) (N cap : ℕ) (tau w z : ℝ) : Finset ℕ :=
  actualSmallRoughModuli ((endpointPolicy8 d (N : ℝ) tau) false) N cap w z

def endpointRho (d : OriginalData) (N cap : ℕ) (tau w z L : ℝ) : ℕ → ℝ :=
  actualSmallRoughRho ((endpointPolicy8 d (N : ℝ) tau) false) N cap w z L

def exitTest (old fresh : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (s : FirstExitDepthState ℕ) : ℝ :=
  (if fresh s.positive s.selectedPrefix = true then
    signedTest fresh (fun _ => 1) T s.selectedPrefix s.positive s.mass s.remaining else 0) -
  (if old s.positive s.selectedPrefix = true then
    signedTest old (fun _ => 1) T s.selectedPrefix s.positive s.mass s.remaining else 0)

/-- Nonmultiplicative terminal tests are carried through the actual first
disagreement, including exhausted branches and every remaining prime. -/
theorem signedTest_first_disagreement (old fresh : Bool → List ℕ → Bool)
    (T : Bool → List ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    signedTest fresh (fun _ => 1) T pre positive mass carrier -
      signedTest old (fun _ => 1) T pre positive mass carrier =
      ((p1SignedExitStates (p1CommonAdmissionPolicy old fresh)
        (fun _ => 1) pre positive mass carrier).map (exitTest old fresh T)).sum := by
  induction carrier generalizing pre positive mass with
  | nil => simp [signedTest, p1SignedExitStates]
  | cons p ps ih =>
      have hskip := ih pre positive mass
      have hselect := ih (p :: pre) (!positive) mass
      cases ho : old (!positive) (p :: pre) <;>
        cases hn : fresh (!positive) (p :: pre) <;>
        simp [signedTest, p1SignedExitStates, p1CommonAdmissionPolicy,
          exitTest, ho, hn] <;>
        rw [← hskip] <;> (try rw [← hselect]) <;> ring

/-- The remainder is independently defined on actual common first exits.
Its terminal evaluates the FULL marked modulus mark*(small*rough). -/
def wallTest (old fresh : Bool → List ℕ → Bool) (N cap mark : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ((p1SignedExitStates (p1CommonAdmissionPolicy old fresh) (fun _ => 1)
    [] true 1 (roughPrimeUniverse N cap w z)).map
      (exitTest old fresh (attachedLeafTest N cap mark w L G))).sum

theorem nonzero_wall_exit_is_disagreement (old fresh : Bool → List ℕ → Bool)
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ p1SignedExitStates (p1CommonAdmissionPolicy old fresh) (fun _ => 1)
      [] true 1 (roughPrimeUniverse N cap w z))
    (hne : exitTest old fresh (attachedLeafTest N cap mark w L G) s ≠ 0) :
    old s.positive s.selectedPrefix ≠ fresh s.positive s.selectedPrefix := by
  have hr := p1_mem_exitStates_rejected (p1CommonAdmissionPolicy old fresh)
    (fun _ => 1) [] (roughPrimeUniverse N cap w z) true 1 s hs
  intro heq
  cases ho : old s.positive s.selectedPrefix <;>
    cases hn : fresh s.positive s.selectedPrefix <;>
    simp_all [p1CommonAdmissionPolicy, exitTest]

theorem physical_difference_eq_wall (old fresh : Bool → List ℕ → Bool)
    (hold : ∀ pre, old true pre = true) (hfresh : ∀ pre, fresh true pre = true)
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ q ∈ actualSmallRoughModuli (fresh false) N cap w z,
      actualSmallRoughRho (fresh false) N cap w z L q * G (mark * q)) -
    (∑ q ∈ actualSmallRoughModuli (old false) N cap w z,
      actualSmallRoughRho (old false) N cap w z L q * G (mark * q)) =
      wallTest old fresh N cap mark w z L G := by
  rw [physical_test_eq_signedTest fresh hfresh,
    physical_test_eq_signedTest old hold]
  exact signedTest_first_disagreement old fresh _ [] _ true 1

/-- Actual original marked source equals the endpoint source MINUS the
real signed wall continuation. Count and coprime mean use the same rho,
same complete modulus, same sign choice and same marked multiplicity. -/
theorem original_marked_count_mean_identity (d : OriginalData) (N cap mark : ℕ)
    (tau w z L : ℝ) :
    (∑ q ∈ moduli d N cap w z, rho d N cap w z L q *
      (chenPrimeAPCount N N (mark * q) - exactCoprimeMean N (mark * q))) =
      (∑ q ∈ endpointQ d N cap tau w z, endpointRho d N cap tau w z L q *
        (chenPrimeAPCount N N (mark * q) - exactCoprimeMean N (mark * q))) -
      wallTest (policy8 d (N : ℝ)) (endpointPolicy8 d (N : ℝ) tau)
        N cap mark w z L (fun q => chenPrimeAPCount N N q - exactCoprimeMean N q) := by
  have h := physical_difference_eq_wall (policy8 d (N : ℝ))
    (endpointPolicy8 d (N : ℝ) tau) (policy8_even d (N : ℝ))
    (endpointPolicy8_even d (N : ℝ) tau) N cap mark w z L
    (fun q => chenPrimeAPCount N N q - exactCoprimeMean N q)
  simp only [moduli, rho, endpointQ, endpointRho]
  linarith only [h]

/-- No normalization of a marked colour is introduced in the leaf source.
In particular beta is chosen by that retained leaf's original sign. -/
theorem endpoint_marked_leaf_source (d : OriginalData) (N cap mark : ℕ)
    (tau w z L : ℝ) (G : ℕ → ℝ) :
    (∑ q ∈ endpointQ d N cap tau w z, endpointRho d N cap tau w z L q * G (mark * q)) =
      ((firstExitRootLeaves (endpointPolicy8 d (N : ℝ) tau) (fun _ => 1)
        (roughPrimeUniverse N cap w z)).map (fun leaf =>
          leaf.value * ∑ a ∈ actualSmallRosserSupport N cap w,
            (if leaf.positive then actualSmallRosserPlus N cap w L a
              else actualSmallRosserMinus N cap w L a) *
                G (mark * (a * leaf.selected.prod)))).sum := by
  rw [show endpointQ d N cap tau w z =
    actualSmallRoughModuli ((endpointPolicy8 d (N : ℝ) tau) false) N cap w z from rfl]
  change (∑ q ∈ _, actualSmallRoughRho _ N cap w z L q * G (mark * q)) = _
  rw [physical_test_eq_signedTest _ (endpointPolicy8_even d (N : ℝ) tau),
    signedTest_eq_leaves]
  rfl

def halfProductTest (b : ℝ) (N : ℕ) (T : ℝ) (q : ℕ) : ℝ :=
  realHalfProductCongruenceMass b N T q -
    realHalfProductCoprimeMass b N T q / (Nat.totient q : ℝ)

/-- The H omission is attached in its actual compact-minus-original
orientation. The new endpoint-to-compact wall is a separate genuine
first-exit source; neither is silently identified with the other. -/
theorem endpoint_original_AP_decomposition (d : OriginalData) (n N cap : ℕ)
    (tau w z L b T : ℝ) :
    realPhysicalDistributionError b N T (endpointQ d N cap tau w z)
      (endpointRho d N cap tau w z L) -
      realPhysicalDistributionError b N T (moduli d N cap w z) (rho d N cap w z L) =
    wallTest (compactPolicy8 d n (N : ℝ)) (endpointPolicy8 d (N : ℝ) tau)
      N cap 1 w z L (halfProductTest b N T) +
        actualDeltaCount d n N cap w z L b T - actualDeltaMean d n N cap w z L b T := by
  have hf := physical_difference_eq_wall (compactPolicy8 d n (N : ℝ))
    (endpointPolicy8 d (N : ℝ) tau) (compactPolicy8_even d n (N : ℝ))
    (endpointPolicy8_even d (N : ℝ) tau) N cap 1 w z L (halfProductTest b N T)
  have ho := P2OriginalElevenLocalizedFullQDifference.delta_test_eq_two_original_sources
    d n N cap w z L (halfProductTest b N T)
  have hm := actual_AP_eq_count_sub_mean d n N cap w z L b T
  simp only [one_mul] at hf
  change realPhysicalDistributionError b N T (endpointQ d N cap tau w z)
      (endpointRho d N cap tau w z L) -
      realPhysicalDistributionError b N T
        (actualSmallRoughModuli ((compactPolicy8 d n (N : ℝ)) false) N cap w z)
        (actualSmallRoughRho ((compactPolicy8 d n (N : ℝ)) false) N cap w z L) = _ at hf
  change realPhysicalDistributionError b N T
      (P2OriginalElevenLocalizedFullQDifference.commonQ d n N cap w z)
      (P2OriginalElevenLocalizedFullQDifference.deltaRho d n N cap w z L) =
      realPhysicalDistributionError b N T
        (actualSmallRoughModuli ((compactPolicy8 d n (N : ℝ)) false) N cap w z)
        (actualSmallRoughRho ((compactPolicy8 d n (N : ℝ)) false) N cap w z L) -
      realPhysicalDistributionError b N T (moduli d N cap w z) (rho d N cap w z L) at ho
  linarith

/-- Existing H analytic payment is genuinely consumed: only the exact
omission mean disappears into the reserve. Both the real fine wall source
and the original omitted congruence count stay visible and unpaid. -/
theorem exists_endpoint_original_AP_reduction (epsilon r b kappa eta : ℝ)
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (her : epsilon^2 ≤ r)
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hgap : r < (1-kappa)*(b/(1+b))) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ d : OriginalData, ∀ tau : ℝ,
        let w := (N : ℝ)^(epsilon^2)
        let z := (N : ℝ)^r
        let L := (N : ℝ)^epsilon
        let T := manuscriptHalfProductCutoff kappa N
        |realPhysicalDistributionError b N T (endpointQ d N cap tau w z)
            (endpointRho d N cap tau w z L) -
          realPhysicalDistributionError b N T (moduli d N cap w z) (rho d N cap w z L)| <
          |wallTest (compactPolicy8 d n (N : ℝ)) (endpointPolicy8 d (N : ℝ) tau)
            N cap 1 w z L (halfProductTest b N T)| +
            |actualDeltaCount d n N cap w z L b T| + eta * singularNormalization N := by
  obtain ⟨n₀, N₀, hN₀, hpay⟩ := exists_actual_omitted_mean_payment epsilon r b kappa eta
    he he8 her hb hb1 hkappa hgap heta
  refine ⟨n₀, N₀, hN₀, ?_⟩
  intro n hn N hN hEven cap hcap d tau
  dsimp only
  rw [endpoint_original_AP_decomposition]
  have hp := hpay n hn N hN hEven cap hcap d
  exact (abs_sub _ _).trans_lt ((add_lt_add_left hp _).trans_le (by
    linarith [abs_add
      (wallTest (compactPolicy8 d n (N : ℝ)) (endpointPolicy8 d (N : ℝ) tau)
        N cap 1 ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon)
          (halfProductTest b N (manuscriptHalfProductCutoff kappa N)))
      (actualDeltaCount d n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r)
        ((N : ℝ)^epsilon) b (manuscriptHalfProductCutoff kappa N))]))

end
end ImbalancedChen.P2OriginalElevenEndpointMarkedSource
