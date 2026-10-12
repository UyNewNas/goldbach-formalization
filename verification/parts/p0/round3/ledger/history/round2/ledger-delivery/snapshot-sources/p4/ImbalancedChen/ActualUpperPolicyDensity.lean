import ImbalancedChen.ActualFirstExitDensityProjection
import ImbalancedChen.ActualSelectedPrefixOwnCubeIntegral
import ImbalancedChen.FirstExitHistoricalLevels

/-!
# Exact upper-policy identification for the physical density

A globally even-retaining Boolean policy is exactly its odd test wrapped
by `oddFirstExitPolicy`. This finite identification transports the same
policy's retained support, coefficient and reciprocal-totient polynomial
to the existing small/rough physical attachment. No new coefficient is
chosen for the density calculation.

The ordinary selected-prefix policy and the historical third, fourth and
fifth policies retain every even sign. Their identifications below are
structural: neither a density limit nor a numerical estimate is assumed.
The full manuscript's compiled policy, its support exponent and its sharp
`K` bound are separate inputs still to be supplied.
-/

namespace ImbalancedChen

noncomputable section

/-- Extracting the odd test preserves an upper policy that always retains
the even sign, including on histories that are not reached by its tree. -/
theorem oddFirstExitPolicy_eq_of_even_retained {α : Type*}
    (retained : Bool → List α → Bool)
    (heven : ∀ pre, retained true pre = true) :
    oddFirstExitPolicy (retained false) = retained := by
  funext positive pre
  cases positive <;> simp [oddFirstExitPolicy, heven]

/-- The physical attachment's rough support is precisely the original
Boolean policy's retained modulus support. -/
theorem fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    fixedRoughSupport (retained false) N cap w z =
      firstExitRetainedModuli retained (roughPrimeUniverse N cap w z) := by
  unfold fixedRoughSupport oddFirstExitRetainedModuli firstExitRetainedModuli
    oddFirstExitRetainedLeaves firstExitRootLeaves
  rw [oddFirstExitPolicy_eq_of_even_retained retained heven]

/-- The rough coefficient is the original policy's literal Möbius lookup
on its retained support, with zero outside that same support. -/
theorem fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    fixedRoughCoefficient (retained false) N cap w z d =
      (firstExitRetainedCoefficient retained (roughPrimeUniverse N cap w z) d : ℝ) := by
  change ((if d ∈ fixedRoughSupport (retained false) N cap w z then
    ArithmeticFunction.moebius d else 0 : ℤ) : ℝ) = _
  rw [fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    retained heven N cap w z]
  rfl

/-- The displayed physical modulus carrier uses the small support and the
original Boolean policy's retained rough support. -/
theorem actualSmallRoughModuli_eq_firstExitAttachment
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    actualSmallRoughModuli (retained false) N cap w z =
      smallRoughModuli (actualSmallRosserSupport N cap w)
        (firstExitRetainedModuli retained (roughPrimeUniverse N cap w z)) := by
  unfold actualSmallRoughModuli
  rw [fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    retained heven N cap w z]

/-- The physical arithmetic function is exactly the sign-sensitive
attachment to the original policy's coefficient, before a test integer
or a progression source is supplied. -/
theorem actualSmallRoughRho_eq_firstExitAttachment
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z L : ℝ) :
    actualSmallRoughRho (retained false) N cap w z L =
      smallRoughRho (actualSmallRosserSupport N cap w)
        (firstExitRetainedModuli retained (roughPrimeUniverse N cap w z))
        (fun d => (firstExitRetainedCoefficient retained
          (roughPrimeUniverse N cap w z) d : ℝ))
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) := by
  unfold actualSmallRoughRho
  rw [fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    retained heven N cap w z]
  rw [funext (fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    retained heven N cap w z)]

/-- A retained upper-policy polynomial is the density of exactly the
rough coefficient used by its physical attachment. The real cutoffs,
enumeration cap and deleted target primes are unchanged. -/
theorem firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    firstExitRetainedPolynomial retained
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap w z) =
      reciprocalTotientDensity (fixedRoughSupport (retained false) N cap w z)
        (fixedRoughCoefficient (retained false) N cap w z) := by
  simpa only [oddFirstExitRetainedPolynomial,
    oddFirstExitPolicy_eq_of_even_retained retained heven] using
      oddFirstExitRetainedPolynomial_eq_fixedRoughDensity
        (retained false) N cap w z

/-- The signed rough main term is nonnegative on every actual prime
carrier. This follows from the first-exit Euler-product identity, rather
than assuming that the individual Möbius coefficients are nonnegative. -/
theorem fixedRoughDensity_nonneg
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    0 ≤ reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
      (fixedRoughCoefficient retainOdd N cap w z) := by
  rw [← oddFirstExitRetainedPolynomial_eq_fixedRoughDensity]
  have hlocal : ∀ p ∈ roughPrimeUniverse N cap w z,
      0 ≤ (1 : ℝ) / ((p : ℝ) - 1) ∧ (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 :=
    fun _ hp => reciprocalTotientPrimeWeight_mem_Icc (mem_roughPrimeUniverse_prime hp)
  exact (list_prod_nonneg_of_mem (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1))
    (roughPrimeUniverse N cap w z) (fun p hp => sub_nonneg.mpr (hlocal p hp).2)).trans
      (product_le_oddFirstExitRetainedPolynomial retainOdd
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap w z) hlocal)

/-- Splicing two even-retaining policies preserves that property at every
history, independently of the splice rank and reachability. -/
theorem firstExitDepthSplicePolicy_even_retained {α : Type*} (k : ℕ)
    (parent replacement : Bool → List α → Bool)
    (hparent : ∀ pre, parent true pre = true)
    (hreplacement : ∀ pre, replacement true pre = true) (pre : List α) :
    firstExitDepthSplicePolicy k parent replacement true pre = true := by
  simp [firstExitDepthSplicePolicy, hparent, hreplacement]

/-- The actual selected upper policy is globally even-retaining. The
selected-cell checks are not needed for this structural property. -/
@[simp] theorem actualSelectedPrefixSplicePolicy_upper_even {d : ℕ} (N : ℝ)
    (I : Finset (Fin d)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1))) (pre : List ℕ) :
    actualSelectedPrefixSplicePolicy false N I old nu a b m J true pre = true := by
  unfold actualSelectedPrefixSplicePolicy
  exact firstExitDepthSplicePolicy_even_retained (d - 1) _ _
    (ordinaryParityRosserPolicy_upper_even _)
    (frozenParityRosserPolicy_upper_even _ _) pre

/-- The third-level historical policy inherits the upper parity from its
base and preserves it after selecting the frozen third level. -/
theorem thirdCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    thirdCappedUpperPolicy base Q3 true pre = true := by
  unfold thirdCappedUpperPolicy
  exact firstExitDepthSplicePolicy_even_retained 2 _ _ hbase
    (frozenParityRosserPolicy_upper_even _ _) pre

/-- The fourth replacement remains on the same even-retaining upper tree. -/
theorem fourthCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 Q4 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    fourthCappedUpperPolicy base Q3 Q4 true pre = true := by
  unfold fourthCappedUpperPolicy
  exact firstExitDepthSplicePolicy_even_retained 4 _ _
    (thirdCappedUpperPolicy_even_retained base Q3 hbase)
    (frozenParityRosserPolicy_upper_even _ _) pre

/-- The fifth replacement retains every even sign on the inherited
third-level tree, including before its own fifth admission. -/
theorem fifthCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 Q5 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    fifthCappedUpperPolicy base Q3 Q5 true pre = true := by
  unfold fifthCappedUpperPolicy
  exact firstExitDepthSplicePolicy_even_retained 4 _ _
    (thirdCappedUpperPolicy_even_retained base Q3 hbase)
    (frozenParityRosserPolicy_upper_even _ _) pre

/-- The existing selected-prefix density limit concerns the literal full
rough coefficient to which the physical attachment applies. This is an
exact identification for the single selected fifth-prefix construction;
it does not identify that construction with the full manuscript policy. -/
theorem actualSelectedPrefixUpperDensity_eq_fixedRoughDensity
    (N cap : ℕ) (I : Finset (Fin 5)) (old nu a b : ℚ)
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1))) :
    actualSelectedPrefixUpperDensity N cap I old nu a b m J =
      reciprocalTotientDensity
        (fixedRoughSupport
          (actualSelectedPrefixSplicePolicy false (N : ℝ) I old nu a b m J false)
          N cap 0 ((N : ℝ) ^ (b : ℝ)))
        (fixedRoughCoefficient
          (actualSelectedPrefixSplicePolicy false (N : ℝ) I old nu a b m J false)
          N cap 0 ((N : ℝ) ^ (b : ℝ))) := by
  exact firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (actualSelectedPrefixSplicePolicy false (N : ℝ) I old nu a b m J)
    (actualSelectedPrefixSplicePolicy_upper_even (N : ℝ) I old nu a b m J)
    N cap 0 ((N : ℝ) ^ (b : ℝ))

end

end ImbalancedChen
