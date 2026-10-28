import ImbalancedChen.P2OriginalMixedThirdSignedFrontier
import ImbalancedChen.ActualLowerSmallRoughAttachment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual lower Rosser attachment for the SAME old/new third-stage policies,
on the genuinely separated small<p y and rough>=y prime supports.
The sign used to select beta is the ORIGINAL Moebius sign of b. Applying
signAttachedCoefficient to the policy difference would in general choose
the wrong beta when a positive old coefficient is removed.

The y-carrier construction is separate from the previous 0-carrier stage;
no unsupported carrier identification is asserted.
-/
namespace ImbalancedChen.P2OriginalI3ActualSmallRosserAttachment
noncomputable section
open scoped Classical BigOperators
open P2OriginalMixedThirdSignedFrontier

/-- The literal Trace predicate before the even-policy wrapper. -/
def seedRetain {mesh : ℕ} (D : ThirdStage mesh) (N : ℕ) : List ℕ → Bool :=
  P2LowerCapPlanIntegerRetention.retainEven D.seedPlan (D.start.epsilon : ℝ)
    (P2OriginalLowerCompactStartCapConstructor.startCutoff D.start.start : ℝ)
    (P2OriginalLowerCompactStartCapConstructor.baselineCap D.rho) N

def thirdRetain {mesh : ℕ} (D : ThirdStage mesh) (N : ℕ) : List ℕ → Bool :=
  P2LowerCapPlanIntegerRetention.retainEven D.thirdPlan (D.start.epsilon : ℝ)
    (P2OriginalLowerCompactStartCapConstructor.startCutoff D.start.start : ℝ)
    (P2OriginalLowerCompactStartCapConstructor.baselineCap D.rho) N

def roughUnion {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (y z : ℝ) : Finset ℕ :=
  p1PolicyUnionModuli (D.oldPolicy N) (D.newPolicy N)
    (roughPrimeUniverse N cap y z)

def roughDelta {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z : ℝ) (b : ℕ) : ℝ :=
  (p1PolicyCoefficientDifference (D.oldPolicy N) (D.newPolicy N)
    (roughPrimeUniverse N cap y z) b : ℝ)

/-- Nonnegative ORIGINAL mu uses the lower small Rosser weight; negative
ORIGINAL mu uses the upper weight. This branch is not sign(roughDelta). -/
def originalMuBeta (N cap : ℕ) (y L : ℝ) (a b : ℕ) : ℝ :=
  if 0 ≤ (ArithmeticFunction.moebius b : ℝ)
    then actualSmallRosserMinus N cap y L a
    else actualSmallRosserPlus N cap y L a

private theorem pairCoefficient_original_mu
    (policy : Bool → List ℕ → Bool) (carrier : List ℕ)
    (N cap : ℕ) (y L : ℝ) (a b : ℕ) :
    smallRoughPairCoefficient
      (fun d => (firstExitRetainedCoefficient policy carrier d : ℝ))
      (actualSmallRosserPlus N cap y L) (actualSmallRosserMinus N cap y L) (a,b) =
      (firstExitRetainedCoefficient policy carrier b : ℝ) *
        originalMuBeta N cap y L a b := by
  by_cases hb : b ∈ firstExitRetainedModuli policy carrier
  · simp [smallRoughPairCoefficient, signAttachedCoefficient,
      firstExitRetainedCoefficient, hb, originalMuBeta]
  · simp [smallRoughPairCoefficient, signAttachedCoefficient,
      firstExitRetainedCoefficient, hb]

/-- On a common rough modulus, occupied old/new coefficients have the same
original mu. The correct attachment difference factors through that sign. -/
theorem pair_difference_original_mu
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ)
    (N cap : ℕ) (y L : ℝ) (a b : ℕ) :
    smallRoughPairCoefficient
        (fun d => (firstExitRetainedCoefficient newPolicy carrier d : ℝ))
        (actualSmallRosserPlus N cap y L) (actualSmallRosserMinus N cap y L) (a,b) -
      smallRoughPairCoefficient
        (fun d => (firstExitRetainedCoefficient oldPolicy carrier d : ℝ))
        (actualSmallRosserPlus N cap y L) (actualSmallRosserMinus N cap y L) (a,b) =
      (p1PolicyCoefficientDifference oldPolicy newPolicy carrier b : ℝ) *
        originalMuBeta N cap y L a b := by
  rw [pairCoefficient_original_mu, pairCoefficient_original_mu]
  simp only [p1PolicyCoefficientDifference, Int.cast_sub]
  ring

/-- Padding a policy's support to the common union adds only zero pair
coefficients. No multiplicity or positivity assumption is needed. -/
private theorem pad_smallRoughRho_policy
    (policy : Bool → List ℕ → Bool) (carrier : List ℕ)
    (small big : Finset ℕ) (betaMinus betaPlus : ℕ → ℝ)
    (hsub : firstExitRetainedModuli policy carrier ⊆ big) (q : ℕ) :
    smallRoughRho small (firstExitRetainedModuli policy carrier)
        (fun d => (firstExitRetainedCoefficient policy carrier d : ℝ))
        betaMinus betaPlus q =
      smallRoughRho small big
        (fun d => (firstExitRetainedCoefficient policy carrier d : ℝ))
        betaMinus betaPlus q := by
  unfold smallRoughRho
  apply Finset.sum_subset
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hpair,hprod⟩
    rcases Finset.mem_product.mp hpair with ⟨ha,hb⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hsub hb⟩,hprod⟩
  · intro x hx hnot
    rcases Finset.mem_filter.mp hx with ⟨hpair,hprod⟩
    have hsmall := (Finset.mem_product.mp hpair).1
    have hb : x.2 ∉ firstExitRetainedModuli policy carrier := by
      intro hb
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hsmall,hb⟩,hprod⟩)
    simp [smallRoughPairCoefficient, firstExitRetainedCoefficient, hb,
      signAttachedCoefficient]

def attachedSupport {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap y) (roughUnion D N cap y z)

private theorem smallRoughModuli_union (small left right : Finset ℕ) :
    smallRoughModuli small (left ∪ right) =
      smallRoughModuli small left ∪ smallRoughModuli small right := by
  ext q
  constructor
  · intro hq
    obtain ⟨x,hx,hprod⟩ := Finset.mem_image.mp hq
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hx
    rcases Finset.mem_union.mp hb with hl | hr
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨x,Finset.mem_product.mpr ⟨ha,hl⟩,hprod⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨x,Finset.mem_product.mpr ⟨ha,hr⟩,hprod⟩)
  · intro hq
    rcases Finset.mem_union.mp hq with hl | hr
    · obtain ⟨x,hx,hprod⟩ := Finset.mem_image.mp hl
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hx
      exact Finset.mem_image.mpr
        ⟨x,Finset.mem_product.mpr ⟨ha,Finset.mem_union_left _ hb⟩,hprod⟩
    · obtain ⟨x,hx,hprod⟩ := Finset.mem_image.mp hr
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hx
      exact Finset.mem_image.mpr
        ⟨x,Finset.mem_product.mpr ⟨ha,Finset.mem_union_right _ hb⟩,hprod⟩

/-- The displayed support is exactly the union of the TWO actual attached
supports; no physical modulus is lost by moving to a common coefficient. -/
theorem attachedSupport_eq_actual_union {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z : ℝ) :
    attachedSupport D N cap y z =
      actualLowerSmallRoughModuli (thirdRetain D N) N cap y z ∪
        actualLowerSmallRoughModuli (seedRetain D N) N cap y z := by
  exact smallRoughModuli_union (actualSmallRosserSupport N cap y)
    (fixedEvenRoughSupport (thirdRetain D N) N cap y z)
    (fixedEvenRoughSupport (seedRetain D N) N cap y z)

/-- Difference of the two actual LOWER physical coefficients, not an
attachment constructed by inspecting the sign of their difference. -/
def attachedRho {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) (q : ℕ) : ℝ :=
  actualLowerSmallRoughRho (thirdRetain D N) N cap y z L q -
    actualLowerSmallRoughRho (seedRetain D N) N cap y z L q

theorem attachedRho_zero_outside {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) (q : ℕ)
    (hq : q ∉ attachedSupport D N cap y z) :
    attachedRho D N cap y z L q = 0 := by
  rw [attachedSupport_eq_actual_union] at hq
  have hn : q ∉ actualLowerSmallRoughModuli (thirdRetain D N) N cap y z :=
    fun h => hq (Finset.mem_union_left _ h)
  have ho : q ∉ actualLowerSmallRoughModuli (seedRetain D N) N cap y z :=
    fun h => hq (Finset.mem_union_right _ h)
  unfold attachedRho actualLowerSmallRoughRho
  rw [smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hn,
    smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ ho]
  ring

private theorem roughUnion_supported {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z : ℝ) (b : ℕ) (hb : b ∈ roughUnion D N cap y z) :
    RoughPrimeSupportedAt y b := by
  rcases Finset.mem_union.mp hb with hn | ho
  · exact fixedEvenRoughSupport_roughPrimeSupportedAt (thirdRetain D N) N cap y z hn
  · exact fixedEvenRoughSupport_roughPrimeSupportedAt (seedRetain D N) N cap y z ho

private theorem actual_policy_padded
    (retain : List ℕ → Bool) (N cap : ℕ) (y z L : ℝ)
    (big : Finset ℕ) (hsub : fixedEvenRoughSupport retain N cap y z ⊆ big)
    (q : ℕ) :
    actualLowerSmallRoughRho retain N cap y z L q =
      smallRoughRho (actualSmallRosserSupport N cap y) big
        (fixedEvenRoughCoefficient retain N cap y z)
        (actualSmallRosserPlus N cap y L) (actualSmallRosserMinus N cap y L) q := by
  exact pad_smallRoughRho_policy (evenFirstExitPolicy retain)
    (roughPrimeUniverse N cap y z) (actualSmallRosserSupport N cap y) big
    (actualSmallRosserPlus N cap y L) (actualSmallRosserMinus N cap y L) hsub q

/-- Exact actual attached coefficient at its unique small/rough product.
Original-mu beta selection survives removal as well as addition. -/
theorem attachedRho_mul {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) (a b : ℕ)
    (ha : a ∈ actualSmallRosserSupport N cap y)
    (hb : b ∈ roughUnion D N cap y z) :
    attachedRho D N cap y z L (a*b) =
      roughDelta D N cap y z b * originalMuBeta N cap y L a b := by
  unfold attachedRho
  rw [actual_policy_padded (thirdRetain D N) N cap y z L
    (roughUnion D N cap y z) Finset.subset_union_left]
  rw [actual_policy_padded (seedRetain D N) N cap y z L
    (roughUnion D N cap y z) Finset.subset_union_right]
  have hs : ∀ d ∈ actualSmallRosserSupport N cap y, SmallPrimeSupportedAt y d :=
    fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap y hd
  have hr : ∀ d ∈ roughUnion D N cap y z, RoughPrimeSupportedAt y d :=
    fun _ hd => roughUnion_supported D N cap y z _ hd
  rw [smallRoughRho_mul hs hr _ _ _ ha hb,
    smallRoughRho_mul hs hr _ _ _ ha hb]
  exact pair_difference_original_mu (D.oldPolicy N) (D.newPolicy N)
    (roughPrimeUniverse N cap y z) N cap y L a b

/-- Common occupied products cancel their identical original-mu beta.
Consequently the actual attached difference keeps the one-bound. -/
theorem attachedRho_abs_le_one {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) (q : ℕ) :
    |attachedRho D N cap y z L q| ≤ 1 := by
  by_cases hq : q ∈ attachedSupport D N cap y z
  · obtain ⟨⟨a,b⟩,hab,hprod⟩ := Finset.mem_image.mp hq
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    rw [← hprod, attachedRho_mul D N cap y z L a b ha hb, abs_mul]
    have hr : |roughDelta D N cap y z b| ≤ 1 :=
      p1_policyCoefficientDifference_real_abs_le_one (D.oldPolicy N)
        (D.newPolicy N) (roughPrimeUniverse N cap y z) b
    have hbeta : |originalMuBeta N cap y L a b| ≤ 1 := by
      unfold originalMuBeta
      split
      · exact actualSmallRosserMinus_abs_le_one N cap y L a
      · exact actualSmallRosserPlus_abs_le_one N cap y L a
    calc
      |roughDelta D N cap y z b| * |originalMuBeta N cap y L a b| ≤ 1 * 1 :=
        mul_le_mul hr hbeta (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · rw [attachedRho_zero_outside D N cap y z L q hq]
    norm_num

/-- The unique cutoff-separated product gives a multiplicity-free exact
sum with the same attached physical rho for any signed modulus test F. -/
theorem attachedRho_sum_eq_original_mu_pairs {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ attachedSupport D N cap y z, attachedRho D N cap y z L q * F q) =
      ∑ a ∈ actualSmallRosserSupport N cap y,
        ∑ b ∈ roughUnion D N cap y z,
          roughDelta D N cap y z b * originalMuBeta N cap y L a b * F (a*b) := by
  rw [attachedSupport, sum_smallRoughModuli
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap y hd)
    (fun _ hd => roughUnion_supported D N cap y z _ hd)]
  rw [smallRoughPairs, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [attachedRho_mul D N cap y z L a b ha hb]

/-- Actual y-separated rough frontier. It is not identified with the old
zero-lower-cutoff frontier by renaming a carrier. -/
def yTaggedFrontier {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z : ℝ) (h : ℕ → ℝ) :
    List (FirstExitDepthState ℕ × Option
      P2OriginalLowerWholeBoxBranchSelect.SelectedBranchData) :=
  (firstExitDepthFrontier 3 (D.oldPolicy N) h [] true 1
    (roughPrimeUniverse N cap y z)).map
      (fun state => (state,D.sourceLabel N state.selectedPrefix))

theorem y_rough_same_rho_eq_actual_frontier {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z : ℝ) (h : ℕ → ℝ) :
    (∑ b ∈ roughUnion D N cap y z,
      roughDelta D N cap y z b * b.primeFactors.prod h) =
      ((yTaggedFrontier D N cap y z h).map (D.frontierTerm N h)).sum := by
  change (∑ b ∈ p1PolicyUnionModuli _ _ _,
    (p1PolicyCoefficientDifference _ _ _ b : ℝ) * b.primeFactors.prod h) = _
  rw [← p1_retainedPolynomial_sub_eq_union_coefficient_sum
    (D.oldPolicy N) (D.newPolicy N) h (roughPrimeUniverse N cap y z)
    (roughPrimeUniverse_nodup N cap y z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp)]
  rw [← D.newPolicy_eq_actual_depthSplice N,
    firstExitRetainedPolynomial_depthSplice_root_sub_eq_frontier_sum]
  simp only [yTaggedFrontier, ThirdStage.frontierTerm, List.map_map, Function.comp_apply]

/-- Finite source count with the actual attached physical coefficient. -/
def attachedCount {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (y z L : ℝ)
    (A : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ m ∈ A, weight m * physicalDivisorSum
    (attachedSupport D N cap y z) (attachedRho D N cap y z L) (N-m)

def attachedExactMean {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (y z L : ℝ)
    (A : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ q ∈ attachedSupport D N cap y z, attachedRho D N cap y z L q *
    ((∑ m ∈ A, if Nat.Coprime m q then weight m else 0) / (Nat.totient q : ℝ))

def attachedDiscrepancy {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (y z L : ℝ)
    (A : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ q ∈ attachedSupport D N cap y z, attachedRho D N cap y z L q *
    ((∑ m ∈ A, if q ∣ N-m then weight m else 0) -
      (∑ m ∈ A, if Nat.Coprime m q then weight m else 0) / (Nat.totient q : ℝ))

/-- Count and exact coprime mean use the identical ACTUAL attached rho. -/
theorem attachedDiscrepancy_eq_actual_count_sub_exact_mean {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (y z L : ℝ)
    (A : Finset ℕ) (weight : ℕ → ℝ) :
    attachedDiscrepancy D N cap y z L A weight =
      attachedCount D N cap y z L A weight -
        attachedExactMean D N cap y z L A weight := by
  have hcount : attachedCount D N cap y z L A weight =
      ∑ q ∈ attachedSupport D N cap y z, attachedRho D N cap y z L q *
        (∑ m ∈ A, if q ∣ N-m then weight m else 0) := by
    unfold attachedCount physicalDivisorSum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hqm : q ∣ N-m <;> simp [hqm, mul_comm]
  rw [hcount]
  unfold attachedDiscrepancy attachedExactMean
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- The same exact signed error pulls back to the original-mu small/rough
pairs. Neither the beta branch nor the coprime mean is replaced. -/
theorem attachedDiscrepancy_eq_original_mu_pairs {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (y z L : ℝ)
    (A : Finset ℕ) (weight : ℕ → ℝ) :
    attachedDiscrepancy D N cap y z L A weight =
      ∑ a ∈ actualSmallRosserSupport N cap y,
        ∑ b ∈ roughUnion D N cap y z,
          roughDelta D N cap y z b * originalMuBeta N cap y L a b *
          ((∑ m ∈ A, if a*b ∣ N-m then weight m else 0) -
            (∑ m ∈ A, if Nat.Coprime m (a*b) then weight m else 0) /
              (Nat.totient (a*b) : ℝ)) := by
  exact attachedRho_sum_eq_original_mu_pairs D N cap y z L _

end
end ImbalancedChen.P2OriginalI3ActualSmallRosserAttachment
