import ImbalancedChen.Part5OriginalH430QFibreWeightedTrueLookup
import ImbalancedChen.Part5OriginalH430UpperOverlapCommonQ
import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted

/-!
P5.6 / h34 — one-sided POSITIVE original-to-frozen arithmetic source
comparison, retaining q weights, the literal original U3/U4 tags,
and the genuine finite marked-family Theta normalizer at each PHYSICAL Q.

The original selected q source is contained in its real frozen root
receiver. Nonnegative q-dependent weights can therefore be transferred
in the upper direction. Chen's negative quarter reverses that inequality.
For a fixed original root, division by the actual positive Theta is
legitimate only after its primitive support and positive-mark gates.

The marked product index d and its sigma(d) are deliberately NOT
identified with the arithmetic quotient-prime q. Matching the original
marked prefixes, the full/selected/inherited owner, the averaged
source-to-Theta count estimate, and H430 is still OPEN. In particular
no equality between the original integer count and Theta is asserted.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430PositiveFibreThetaDirection
noncomputable section

open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430UpperOverlapCommonQ
open P2EnhancedTwentyOneSameQWeighted (Theta)

/-- The genuinely selected original q fibre has a nonnegative weighted
upper bound in its SAME rooted frozen receiver. No q position is dropped,
and the weight can depend arbitrarily on q. -/
theorem original_positive_q_fibre_le_frozen
    (N n p : ℕ) (root : Root) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384)
    (hp : p ∈ originalBand N root)
    (w : ℕ → ℝ)
    (hw : ∀ q ∈ frozenReceiver N n tau root p, 0 ≤ w q) :
    (∑ q ∈ originalReceiver N p, w q) ≤
      ∑ q ∈ frozenReceiver N n tau root p, w q := by
  have hs := original_receiver_subset_frozen N n root tau p
    hN htau htauhi hn hp
  exact Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun q hq _ => hw q hq)

/-- There is also a single one-sided majorization of the true complete
ORIGINAL tagged arithmetic source, retaining both U4 labels and all q.
This is not a history-Fin injection. -/
theorem original_positive_tagged_le_frozen
    (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384)
    (w : TaggedReceiver → ℝ)
    (hw : ∀ z ∈ frozenTagged N n tau, 0 ≤ w z) :
    (∑ z ∈ originalTagged N, w z) ≤
      ∑ z ∈ frozenTagged N n tau, w z := by
  have hs := original_tagged_subset_frozen N n tau
    hN htau htauhi hn
  exact Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun z hz _ => hw z hz)

/-- The literal negative Chen quarter must reverse the direction of
the POSITIVE source upper bound. A frozen count upper is thus a lower
bound after the negative quarter. It is not a signed Euler payment. -/
theorem chen_negative_quarter_reverses_positive_source
    (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384)
    (w : TaggedReceiver → ℝ)
    (hw : ∀ z ∈ frozenTagged N n tau, 0 ≤ w z) :
    -(1/4 : ℝ) * (∑ z ∈ frozenTagged N n tau, w z) ≤
      -(1/4 : ℝ) * (∑ z ∈ originalTagged N, w z) := by
  have hs := original_positive_tagged_le_frozen
    N n tau hN htau htauhi hn w hw
  linarith only [hs]

/-- A positive marked family has the EXACT installed Theta N Q D sigma,
where its mark d is NOT replaced by the arithmetic receiver q. At this
root, Q is the real frozen physical Q. The existing primitive gates
produce positivity; no count/Theta comparison is an input. -/
theorem original_q_fibre_normalized_upper
    (N n p : ℕ) (root : Root) (tau : ℝ)
    (hN : 4 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384)
    (hp : p ∈ originalBand N root)
    (w : ℕ → ℝ)
    (hw : ∀ q ∈ frozenReceiver N n tau root p, 0 ≤ w q)
    (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hdpos : ∀ d ∈ D, 0 < d)
    (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hlevel : ∀ d ∈ D, 1 < rootQ N n root tau p / (d : ℝ))
    (hpositive : ∃ d ∈ D, 0 < sigma d) :
    (∑ q ∈ originalReceiver N p, w q) /
      Theta N (rootQ N n root tau p) D sigma ≤
    (∑ q ∈ frozenReceiver N n tau root p, w q) /
      Theta N (rootQ N n root tau p) D sigma := by
  have hsource := original_positive_q_fibre_le_frozen
    N n p root tau (by omega : 2 ≤ N)
    htau htauhi hn hp w hw
  have hTheta := P2EnhancedTwentyOneSameQWeighted.Theta_pos
    hN (rootQ N n root tau p) D sigma hdpos hsigma hlevel hpositive
  exact div_le_div_of_nonneg_right hsource hTheta.le

/-- The true U4 original overlap supplies equality of the complete
marked-family normalizer AT THE SAME physical Q. This is a specialization
of the real root-Q equality, not an assertion that unrelated p roots
have one common Q or one marked family. -/
theorem original_u4_overlap_same_literal_Theta
    (N n : ℕ) (tau : ℝ) (hN : 2 ≤ N)
    (x : TaggedPair) (hx : x ∈ originalPairs N .U4)
    (D : Finset ℕ) (sigma : ℕ → ℝ) :
    Theta N (rootQ N n .U3 tau x.1) D sigma =
      Theta N (rootQ N n .U4 tau x.1) D sigma := by
  rw [original_u4_overlap_real_Q_equal N n tau hN x hx]

/-- Both original U4 arithmetic tags keep distinct q-dependent weights
even after normalization. This is a single upper comparison on the SAME
real physical Q; its outer marks D/sigma remain independent of q and
must be matched to the manuscript before the final count estimate. -/
theorem original_u4_two_tag_normalized_upper
    (N n : ℕ) (tau : ℝ) (hN : 4 ≤ N)
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384)
    (x : TaggedPair) (hx : x ∈ originalPairs N .U4)
    (w3 w4 : TaggedPair → ℝ)
    (hw : ∀ q ∈ frozenReceiver N n tau .U4 x.1,
      0 ≤ w3 ⟨x.1,q⟩ + w4 ⟨x.1,q⟩)
    (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hdpos : ∀ d ∈ D, 0 < d)
    (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hlevel : ∀ d ∈ D, 1 < rootQ N n .U4 tau x.1 / (d : ℝ))
    (hpositive : ∃ d ∈ D, 0 < sigma d) :
    (∑ q ∈ originalReceiver N x.1,
       (w3 ⟨x.1,q⟩ + w4 ⟨x.1,q⟩)) /
         Theta N (rootQ N n .U4 tau x.1) D sigma ≤
    (∑ q ∈ frozenReceiver N n tau .U4 x.1,
       (w3 ⟨x.1,q⟩ + w4 ⟨x.1,q⟩)) /
         Theta N (rootQ N n .U4 tau x.1) D sigma := by
  have hp : x.1 ∈ originalBand N .U4 := (Finset.mem_sigma.mp hx).1
  exact original_q_fibre_normalized_upper N n x.1 .U4 tau
    hN htau htauhi hn hp
    (fun q => w3 ⟨x.1,q⟩ + w4 ⟨x.1,q⟩) hw
    D sigma hdpos hsigma hlevel hpositive

end
end ImbalancedChen.Part5OriginalH430PositiveFibreThetaDirection
