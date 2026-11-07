import Mathlib

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / NOT ROOT ACCEPTED.
-- Original lower joint approximation, lines 97-124: once rational boxes
-- and their strict branch gaps have been obtained, one rational buffer
-- works on the finite active family. Inherit cells retain the exact parent.
-- Apply at one rank after freezing its incoming parents. This does not
-- choose compact chambers, prove their coverage, or estimate any integral.

namespace ImbalancedChen.P2FiniteActiveBranchBuffer

private theorem exists_common_positive_rational_buffer
    {ι : Type*} [DecidableEq ι] (A : Finset ι) (gap : ι → ℚ)
    (eta : ℚ) (heta : 0 < eta) :
    (∀ i ∈ A, 0 < gap i) →
      ∃ delta : ℚ, 0 < delta ∧ delta < eta ∧ ∀ i ∈ A, delta < gap i := by
  induction A using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨eta / 2, by positivity, by linarith, ?_⟩
      simp
  | @insert i A hi ih =>
      intro hgap
      have hgi : 0 < gap i := hgap i (Finset.mem_insert_self i A)
      obtain ⟨delta, hd, hde, hds⟩ := ih
        (fun j hj => hgap j (Finset.mem_insert_of_mem hj))
      refine ⟨min delta (gap i / 2), lt_min hd (by positivity),
        (min_le_left _ _).trans_lt hde, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_right _ _).trans_lt (by linarith)
      · exact (min_le_left _ _).trans_lt (hds j hj)

-- `gate` is the rational maximum of the actual frozen parent and all
-- complete/selected support-gate upper bounds on that particular box.
-- `endpoint` is the chosen labelled affine branch's whole-box infimum.
def bufferedCap {ι : Type*} [DecidableEq ι] (active : Finset ι)
    (parent endpoint : ι → ℚ) (delta : ℚ) (i : ι) : ℚ :=
  if i ∈ active then endpoint i - delta else parent i

theorem exists_buffered_caps_preserving_inherit
    {ι : Type*} [DecidableEq ι] (active : Finset ι)
    (parent gate endpoint : ι → ℚ)
    (hparent : ∀ i ∈ active, parent i ≤ gate i)
    (hstrict : ∀ i ∈ active, gate i < endpoint i)
    (eta : ℚ) (heta : 0 < eta) :
    ∃ delta : ℚ, 0 < delta ∧ delta < eta ∧
      (∀ i, i ∉ active → bufferedCap active parent endpoint delta i = parent i) ∧
      (∀ i ∈ active,
        parent i < bufferedCap active parent endpoint delta i ∧
        gate i < bufferedCap active parent endpoint delta i ∧
        bufferedCap active parent endpoint delta i < endpoint i ∧
        endpoint i - bufferedCap active parent endpoint delta i = delta) := by
  obtain ⟨delta, hd, hde, hgap⟩ :=
    exists_common_positive_rational_buffer active
      (fun i => endpoint i - gate i) eta heta
      (fun i hi => sub_pos.mpr (hstrict i hi))
  refine ⟨delta, hd, hde, ?_, ?_⟩
  · intro i hi
    simp [bufferedCap, hi]
  · intro i hi
    have hp := hparent i hi
    have hg := hgap i hi
    simp only [bufferedCap, if_pos hi]
    exact ⟨by linarith, by linarith, by linarith, by ring⟩

end ImbalancedChen.P2FiniteActiveBranchBuffer
