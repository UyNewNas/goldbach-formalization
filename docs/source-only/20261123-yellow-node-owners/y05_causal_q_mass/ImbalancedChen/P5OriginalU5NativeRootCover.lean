import ImbalancedChen.P5OriginalU5PlateauPrimeBV

/-! All original U5 root levels group the actual native policy.  The
receiver evaluates each word on its original ordered marks, including
fresh cap decisions. No constancy of the subsequent trace is required. -/
namespace ImbalancedChen.P5OriginalU5NativeRootCover

noncomputable section
open Classical
open scoped BigOperators
open P5OriginalU5CausalFinite
open P2OriginalPairSourceReceiver (PairRange pairPlan ceiling)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (rootLevel rootSeed selectedPolicy)
open P2OriginalPairRootRoughProducer (pairPolicy)
open P2OriginalSelectedIntegerPrefixSquares (IntegerSquareGates selectedPrimes remainingPrimes)
open P2OriginalU5SmallPartnerRootPayment (rootQ)

def levels (N : ℕ) : Finset ℝ := (pairSupport N).image (rootLevel false N)

def marks (N : ℕ) (v : ℝ) : Finset (ℕ × ℕ) :=
  (pairSupport N).filter (fun t => rootLevel false N t = v)

def policyAt (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (v : ℝ) (N : ℕ) (t : ℕ × ℕ) : List ℕ → Bool :=
  pairPolicy (pairPlan R bank (2*b) (v-2*(b : ℝ)))
    (R.epsilon : ℝ) (ceiling : ℝ) (v-2*(b : ℝ)) N t

theorem native_policy_at (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} {v : ℝ} {t : ℕ × ℕ} (ht : t ∈ marks N v) :
    selectedPolicy R bank b false N t = policyAt R bank b v N t := by
  have hv := (Finset.mem_filter.mp ht).2
  simp only [selectedPolicy, policyAt, rootSeed, hv]

theorem actual_root_gates {N : ℕ} (hN : 2 ≤ N) {v : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ marks N v) {b : ℚ} (hb : 0 ≤ b) (hb' : b ≤ 1/1000) :
    let slots := [(t.2, true), (t.1, true)]
    rootQ N t = (N : ℝ)^v ∧
    IntegerSquareGates N (v-2*(b : ℝ)) 1 (slots.map Prod.fst) ∧
    IntegerSquareGates N (v-2*(b : ℝ)) (selectedPrimes slots).prod (remainingPrimes slots) := by
  obtain ⟨hp, hv⟩ := Finset.mem_filter.mp ht
  have hs := P2OriginalPairBufferedRootProvenance.fifth_selector_root_gates b hb hb' hN hp
  dsimp only
  refine ⟨?_, ?_⟩
  · change (N : ℝ)^(rootLevel false N t) = _
    rw [hv]
  · simpa only [rootSeed, hv] using hs

theorem signed_native_cover (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (e : ℝ) :
    signedPrimitiveSum N e (selectedPolicy R bank b false N) =
      ∑ v ∈ levels N, ∑ t ∈ marks N v,
        ∑ k ∈ (support N e (policyAt R bank b v N t)).filter
          (fun k => rho N e (policyAt R bank b v N t) k ≠ 0),
          rho N e (policyAt R bank b v N t) k *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N ((t.1*t.2)*k) := by
  let P := selectedPolicy R bank b false N
  calc
    _ = ∑ v ∈ levels N, ∑ t ∈ marks N v, rowSignedPrimitive N e (P t) t :=
      (Finset.sum_fiberwise_of_maps_to (s := pairSupport N) (t := levels N)
        (g := rootLevel false N) (fun t ht => Finset.mem_image_of_mem _ ht)
        (fun t => rowSignedPrimitive N e (P t) t)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro t ht
      change rowSignedPrimitive N e (selectedPolicy R bank b false N t) t = _
      rw [native_policy_at R bank b ht]
      unfold rowSignedPrimitive
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hz : rho N e (policyAt R bank b v N t) k = 0 <;> simp [hz]

end
end ImbalancedChen.P5OriginalU5NativeRootCover
