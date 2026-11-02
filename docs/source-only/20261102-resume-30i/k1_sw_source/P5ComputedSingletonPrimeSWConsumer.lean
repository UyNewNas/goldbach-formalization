import ImbalancedChen.P5OriginalSingletonPrimeSW

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Consumer for the literal H computed ALL16 marked tensor. The class gate
is the syntactic singleton shape of one of its first two computed words;
it is not an assumed source equality or a coefficient-distribution bound.
The original WholeCell supplies the prime exponent, including marked
slots, so the SW threshold precedes all cells, assignments and moduli.
Longer words and the beta-attached third word retain their obligations.
-/

namespace ImbalancedChen.P5Z.ComputedSingletonPrimeSWConsumer
noncomputable section
open Classical Finset Filter Set
open scoped BigOperators Topology
open ImbalancedChen ImbalancedChen.Part3
open All16MarkedCommonFineSource All16MarkedFineScalarBudget
open All16ComputedWholeWordAssignment All16ComputedMarkedTensorBudget
open ActualInnerPerLabelGamma SameWholeAssignmentPerLabel
open OriginalSingletonPrimeSource OriginalSingletonPrimeSW

/-- Only the first two factors are bare gamma; the third includes beta. -/
def bareWord {n m r : ℕ} (N : ℕ) (eta : ℚ) (A : ℝ)
    (k : Key n m r) (second : Bool) : List (Fin (m+1)) :=
  if second then (labelGroups n N m r eta A k).2.1
  else (labelGroups n N m r eta A k).1

theorem bareWord_mem_fullWord {n N m r : ℕ} (eta : ℚ) (A : ℝ)
    (k : Key n m r) (second : Bool) {i : Fin (m+1)}
    (hi : i ∈ bareWord N eta A k second) : i ∈ fullWord k.2.1 k.2.2 := by
  have hp := labelGroups_partition n N m r eta A k
  apply hp.mem_iff.mp
  cases second
  · exact List.mem_append_left _ hi
  · exact List.mem_append_right _ (List.mem_append_left _ hi)

/-- The marked prefix is actually in the same common word. Its original
cutoff, followed by rho≤cellZeta, supplies exactly the residual lower bound. -/
theorem wholeWord_lower {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} {rho : ℝ} {M : Set (ℝ × ℝ)} {k : Key n m r}
    (h : WholeCell eta rho M k.1 k.2.1 k.2.2)
    (hcut : rho ≤ cellZeta n eta k.1) {i : Fin (m+1)}
    (hi : i ∈ fullWord k.2.1 k.2.2) : (N : ℝ)^rho ≤ lower N m i := by
  have hlabel : rho ≤ logPrimeMeshPoint 0 1 m i.val := by
    rcases List.mem_append.mp hi with hm | hr
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm
      exact hcut.trans (h.markedLower j)
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
      exact h.residualLower j
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) hlabel

/-- Every occupied dyadic singleton block derives its power lower bound
from the ORIGINAL whole cell. It is not supplied as an analytic premise. -/
theorem occupied_computed_block_power {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} {rho : ℝ} {M : Set (ℝ × ℝ)} {k : Key n m r}
    (h : WholeCell eta rho M k.1 k.2.1 k.2.2)
    (hcut : rho ≤ cellZeta n eta k.1) (A : ℝ) (second : Bool)
    {i : Fin (m+1)} (hi : bareWord N eta A k second = [i])
    {U : ℝ} (hs : (source N m i U).Nonempty) : (N : ℝ)^rho ≤ 2*U := by
  obtain ⟨p,hp⟩ := hs
  obtain ⟨hp,hu,hv⟩ := Finset.mem_filter.mp hp
  have himem : i ∈ bareWord N eta A k second := by rw [hi]; simp
  have hlower := wholeWord_lower hN h hcut
    (bareWord_mem_fullWord eta A k second himem)
  exact (hlower.trans ((mem_commonAlphabet_iff hN i).mp hp).2.2.1).trans hv

/-- Genuine original-N k=1 SW for each singleton first/second computed
factor. The same theorem covers W and selected assignments. No W endpoint
or whole-source completion is inferred from the singleton class gate. -/
theorem actual_computed_singleton_SW (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    {rho : ℝ} (hrho : 0 < rho) (J L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ n m r : ℕ, ∀ eta : ℚ, ∀ M : Set (ℝ × ℝ), ∀ k : Key n m r,
      WholeCell eta rho M k.1 k.2.1 k.2.2 → rho ≤ cellZeta n eta k.1 →
      ∀ A : ℝ, ∀ second : Bool, ∀ i : Fin (m+1),
      bareWord N eta A k second = [i] → ∀ U : ℝ, 1 ≤ U →
      ∀ t : ℝ, |t| ≤ Real.log (N : ℝ)^L → ∀ q b : ℕ,
      0 < q → b.Coprime q →
      ‖auxiliarySWError (source N m i U)
        (coefficient N m (bareWord N eta A k second) Phi t U) 1 q b‖ ≤
          C*U/Real.log (N : ℝ)^J := by
  obtain ⟨C,hC,hSW⟩ := singleton_profile_SW Phi hPhi hrho J L
  refine ⟨C,hC,?_⟩
  filter_upwards [hSW,eventually_ge_atTop (2 : ℕ)] with N hSW hN
  intro n m r eta M k h hcut A second i hi U hU t ht q b hq hb
  rw [hi]
  by_cases hs : (source N m i U).Nonempty
  · exact hSW m i U hU (occupied_computed_block_power (by omega) h hcut A second hi hs)
      t ht q b hq hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [auxiliarySWError,Finset.sum_empty,zero_div,sub_zero,norm_zero]
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hl := Real.log_nonneg hn
    positivity

theorem singleton_support {ι : Type*} (B : ι → Finset ℕ) (i : ι) :
    support B [i] = B i := by
  ext p
  constructor
  · intro hp
    obtain ⟨ps,hps,hprod⟩ := Finset.mem_image.mp hp
    obtain ⟨⟨q,qs⟩,hq,rfl⟩ := Finset.mem_image.mp hps
    obtain ⟨hq,hqs⟩ := Finset.mem_product.mp hq
    have hqs' : qs = [] := Finset.mem_singleton.mp hqs
    subst qs
    have hqp : q = p := by simpa using hprod
    exact hqp ▸ hq
  · intro hp
    exact Finset.mem_image.mpr ⟨[p],Finset.mem_image.mpr
      ⟨(p,[]),Finset.mem_product.mpr ⟨hp,Finset.mem_singleton_self _⟩,rfl⟩,by simp⟩

/-- Independent physical consumer, not merely a renamed coefficient:
the H tensor literally becomes the prime sum licensed above when its
first computed word is singleton. All four marks, the entire original
beta and the complete product x*y*q3 remain in this equality. -/
theorem actual_tensor_first_singleton {n N m r : ℕ} (eta : ℚ)
    (rho B A : ℝ) (k : Key n m r) (i : Fin (m+1))
    (hi : (labelGroups n N m r eta A k).1 = [i]) (F : ℕ → ℝ) :
    tensor n N m r eta rho B A k F =
      ∑ x ∈ commonAlphabet N m i,
        ∑ y ∈ support (commonAlphabet N m) (labelGroups n N m r eta A k).2.1,
          ∑ q3 ∈ attachedSupport (commonAlphabet N m)
            (labelGroups n N m r eta A k).2.2 N (cellCap n N eta k.1) ((N : ℝ)^rho),
            gamma (commonAlphabet N m) (labelGroups n N m r eta A k).2.1 y *
              SameWholeAssignmentPerLabel.attachedGamma (commonAlphabet N m)
                (labelGroups n N m r eta A k).2.2 N (cellCap n N eta k.1) r
                ((N : ℝ)^rho) B q3 * F (x*y*q3) := by
  unfold tensor
  dsimp only
  rw [hi,singleton_support]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [gamma_singleton,if_pos hx,one_mul]

/-- Attachment to the independently defined marked Cartesian raw atom.
The equality is simultaneous in the count/mean test F and retains the
original signed restoring scalar; no source equality is a premise. -/
theorem actual_raw_first_singleton {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} (heta : 0 < eta) (rho B : ℝ) (M : Set (ℝ × ℝ))
    {k : Key n m r} (hk : k ∈ certifiedKeys n m r eta rho M)
    (A : ℝ) (i : Fin (m+1)) (hi : (labelGroups n N m r eta A k).1 = [i])
    (F : ℕ → ℝ) :
    All16MarkedCommonFineAssembly.rawAtomLinear n N m r eta rho B k F =
      scalar n N m r eta 1 A k *
        (∑ x ∈ commonAlphabet N m i,
          ∑ y ∈ support (commonAlphabet N m) (labelGroups n N m r eta A k).2.1,
            ∑ q3 ∈ attachedSupport (commonAlphabet N m)
              (labelGroups n N m r eta A k).2.2 N (cellCap n N eta k.1) ((N : ℝ)^rho),
              gamma (commonAlphabet N m) (labelGroups n N m r eta A k).2.1 y *
                SameWholeAssignmentPerLabel.attachedGamma (commonAlphabet N m)
                  (labelGroups n N m r eta A k).2.2 N (cellCap n N eta k.1) r
                  ((N : ℝ)^rho) B q3 * F (x*y*q3)) := by
  rw [raw_atom_eq_computed_tensor hN heta rho B M hk A F,
    actual_tensor_first_singleton eta rho B A k i hi F]

end
end ImbalancedChen.P5Z.ComputedSingletonPrimeSWConsumer
