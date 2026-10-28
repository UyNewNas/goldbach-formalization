import ImbalancedChen.Part3OriginalS2FixedDMixedTail
import ImbalancedChen.Part3MediumReceiverCutoffArithmetic
import ImbalancedChen.Part3MediumActualPreliminaryCauchy
import Mathlib.Tactic

/-!
Consume the exact arithmetic receiver c=floor(z)+1/2. The original
inclusive Lambda and its y-kept physical fibers become strict-receiver
canonical fibers without a no-boundary-prime assumption or an analytic
change of z. The actual existing lambdaTrim is recovered through its
ownedSlice/trimmedChoices theorem, not through a newly assumed binder.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2ReceiverLambdaBinding

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2SmoothYRankinStart
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumOwnedCanonicalReindex20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open Classical Finset
open scoped BigOperators

noncomputable section

def receiverKeptSlice (d : MediumAtom) (x z : ℝ) (small rough : ℕ) : Finset (ℕ × ℕ) :=
  (retainedModuli d (strictReceiverCutoff z) (roughY x)).filter
    (fun q => actualD (strictReceiverCutoff z) q = small ∧
      actualW (strictReceiverCutoff z) q = rough)

theorem receiverKeptSlice_eq_original
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (hz : 0 ≤ z) (small rough : ℕ) :
    receiverKeptSlice d x z small rough =
      (factorCarrier d.Q2 ×ˢ factorCarrier d.Q3).filter
        (fun q => labelDW z q = (small, rough) ∧ individualSmoothWithinY x z q) := by
  ext q
  have hlabel := originalLabelDW_eq_receiver z hz q
  have hpair : labelDW z q = (small, rough) ↔
      actualD (strictReceiverCutoff z) q = small ∧
      actualW (strictReceiverCutoff z) q = rough := by
    rw [hlabel]
    simp only [Prod.mk.injEq]
  have htrim : individualSmoothWithinY x z q ↔
      (smoothPart (strictReceiverCutoff z) q.1 : ℝ) ≤ roughY x ∧
      (smoothPart (strictReceiverCutoff z) q.2 : ℝ) ≤ roughY x := by
    simp only [individualSmoothWithinY, originalSmooth_eq_receiver z hz]
  constructor
  · intro hq
    obtain ⟨hr, hl⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp, hret⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hp, hpair.mpr hl, htrim.mpr hret.2.2⟩
  · intro hq
    obtain ⟨hp, hl, ht⟩ := Finset.mem_filter.mp hq
    have h2 : q.1 ≠ 0 := (factorCarrier_pos hd.2.2.2.1 (Finset.mem_product.mp hp).1).ne'
    have h3 : q.2 ≠ 0 := (factorCarrier_pos hd.2.2.2.2.1 (Finset.mem_product.mp hp).2).ne'
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hp, h2, h3, htrim.mp ht⟩, hpair.mp hl⟩

theorem lambdaSmoothKept_eq_receiverKeptSlice
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (hz : 0 ≤ z) (small rough : ℕ) :
    lambdaSmoothKept d x z small rough =
      ∑ q ∈ receiverKeptSlice d x z small rough, d.gamma2 q.1 * d.gamma3 q.2 := by
  rw [receiverKeptSlice_eq_original hd x z hz small rough]
  rfl

/-- The independently built actual lambdaTrim equals its original
physical gamma fiber. This uses the established choice reindexing. -/
theorem lambdaTrim_eq_ownedSlice (d : MediumAtom) (z y : ℝ) (k : Key)
    (small rough : ℕ) (hsmall : small ∈ dyadicWindow k.d) :
    lambdaTrim d z y k small rough =
      ∑ q ∈ ownedSlice d z y k small rough, d.gamma2 q.1 * d.gamma3 q.2 := by
  rw [sum_ownedSlice_eq_trimmedChoices d z y k small rough hsmall]
  rfl

theorem ownedSlice_empty_of_wrong_d (d : MediumAtom) (z y : ℝ) (k : Key)
    (small rough : ℕ) (hsmall : small ∉ dyadicWindow k.d) :
    ownedSlice d z y k small rough = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro q hq
  exact hsmall ((mem_ownedSlice_iff_selected d z y k small rough q).mp hq).2.1

theorem receiverKeptSlice_eq_key_fibers (d : MediumAtom) (x z : ℝ)
    (small rough : ℕ) :
    (∑ q ∈ receiverKeptSlice d x z small rough, d.gamma2 q.1 * d.gamma3 q.2) =
      ∑ k ∈ keyBank d (strictReceiverCutoff z) (roughY x),
        ∑ q ∈ ownedSlice d (strictReceiverCutoff z) (roughY x) k small rough,
          d.gamma2 q.1 * d.gamma3 q.2 := by
  let c := strictReceiverCutoff z
  let S := receiverKeptSlice d x z small rough
  have hmap : ∀ q ∈ S, owner c q ∈ keyBank d c (roughY x) := by
    intro q hq
    exact owner_mem_keyBank (Finset.mem_filter.mp hq).1
  have h := Finset.sum_fiberwise_of_maps_to'
    (s := S) (t := keyBank d c (roughY x)) (g := owner c) hmap
    (fun q => d.gamma2 q.1 * d.gamma3 q.2)
  rw [← h]
  apply Finset.sum_congr rfl
  intro k hk
  have hcarrier : S.filter (fun q => owner c q = k) =
      ownedSlice d c (roughY x) k small rough := by
    ext q
    simp only [S, c, receiverKeptSlice, ownedSlice, ownedModuli,
      Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  rw [hcarrier]

/-- The original inclusive kept Lambda is the sum of the ACTUAL
canonical lambdaTrim key fibers at the translated arithmetic receiver.
The y cutoff remains roughY(x), and the analytic z is unchanged. -/
theorem lambdaSmoothKept_eq_actual_receiver_keySum
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (hz : 0 ≤ z) (small rough : ℕ) :
    lambdaSmoothKept d x z small rough =
      ∑ k ∈ (keyBank d (strictReceiverCutoff z) (roughY x)).filter
          (fun k => small ∈ dyadicWindow k.d),
        lambdaTrim d (strictReceiverCutoff z) (roughY x) k small rough := by
  rw [lambdaSmoothKept_eq_receiverKeptSlice hd x z hz small rough,
    receiverKeptSlice_eq_key_fibers]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hs : small ∈ dyadicWindow k.d
  · simp only [if_pos hs]
    exact (lambdaTrim_eq_ownedSlice d (strictReceiverCutoff z) (roughY x)
      k small rough hs).symm
  · simp only [if_neg hs,
      ownedSlice_empty_of_wrong_d d (strictReceiverCutoff z) (roughY x) k small rough hs,
      Finset.sum_empty]

end
end ImbalancedChen.Part3OriginalS2ReceiverLambdaBinding
