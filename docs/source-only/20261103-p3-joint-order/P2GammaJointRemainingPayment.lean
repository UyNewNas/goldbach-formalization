import ImbalancedChen.P2GammaJointOrderPayment

/-!
Source-only / UNCOMPILED / KERNEL-UNVERIFIED.
One common logarithmic mesh and one threshold pay the exact Q17
upper-plus-order expression AFTER the full marked-pair sum.
Original mother occurrences are kept as a list, not deduplicated.
This does not pay the lower rejected expression or prove a Theta-relative
bound, common physical-Q selected-policy identity, or hUniformPP.
-/

namespace ImbalancedChen.P2GammaJointRemainingPayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2OriginalGammaUpperLowRankConsumer
open P2GammaCompleteProductTrimPayment P2GammaLowerRejectedPayment
open P2GammaUpperStripPayment P2GammaOrderingStripPayment
open P2GammaJointUpperPayment P2GammaJointOrderPayment
open P5OriginalU5CausalFinite (pairSupport)

def originalJointOrderError (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  (originalMotherOccurrences.map
    (fun cs => jointOrderWordError N cs Q rho sigma T H δ K)).sum

theorem originalJointOrderError_eq_outer (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) :
    originalJointOrderError N Q rho sigma T H δ K =
      ∑ t ∈ pairSupport N,sigma t*originalOrderRejectedError N t Q rho T H δ K := by
  have hlist (L : List (List ℕ)) :
      (L.map (fun cs => jointOrderWordError N cs Q rho sigma T H δ K)).sum =
        ∑ t ∈ pairSupport N,sigma t*(L.map (fun cs =>
          P2GammaCompleteProductTrimPayment.wordError N t cs Q rho
            (wordOrderRejectedWeight N t cs T H δ K))).sum := by
    induction L with
    | nil => simp
    | cons cs L ih =>
        simp only [List.map_cons,List.sum_cons,jointOrderWordError_eq_outer,ih,
          mul_add,Finset.sum_add_distrib]
  exact hlist originalMotherOccurrences

/-- The same threshold covers every later positive selector. -/
theorem eventually_originalJointOrderError (A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ → ℝ)
      (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ 1) → 0 < δ →
      δ ≤ boundaryLogMesh (orderMeshExponent (jointListMomentOrder originalMotherOccurrences) A) N →
      |originalJointOrderError N Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let L := originalMotherOccurrences
  let J := jointListMomentOrder L
  let eta0 := eta/((L.length : ℝ)+1)
  have heta0 : 0 < eta0 := by dsimp [eta0]; positivity
  filter_upwards [eventually_jointOrderWordError J A eta0 heta0,
    eventually_one_le_nat_log] with N hword hlog
  intro Q rho sigma T H δ K hQ hrho hsigma hδ hmesh
  let f := fun cs => jointOrderWordError N cs Q rho sigma T H δ K
  let E := eta0*(N : ℝ)/(Real.log (N : ℝ))^A
  have heach : ∀ cs ∈ L,|f cs| ≤ E := by
    intro cs hcs
    exact hword cs (le_jointListMomentOrder hcs) Q rho sigma T H δ K hQ hrho hsigma hδ hmesh
  have hsum : ∀ W : List (List ℕ),(∀ cs ∈ W,|f cs| ≤ E) →
      |(W.map f).sum| ≤ (W.length : ℝ)*E := by
    intro W
    induction W with
    | nil => intro _; simp
    | cons cs W ih =>
        intro hW
        have hc := hW cs (List.mem_cons_self cs W)
        have hw := ih (fun ds hds => hW ds (List.mem_cons_of_mem cs hds))
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        exact (abs_add _ _).trans ((add_le_add hc hw).trans_eq (by ring))
  have hcoefficient : (L.length : ℝ)*eta0 ≤ eta := by
    dsimp [eta0]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (L.length : ℝ)+1)).mpr
    nlinarith
  calc
    _ ≤ (L.length : ℝ)*E := hsum L heach
    _ = ((L.length : ℝ)*eta0)*((N : ℝ)/(Real.log (N : ℝ))^A) := by dsimp [E]; ring
    _ ≤ eta*((N : ℝ)/(Real.log (N : ℝ))^A) :=
      mul_le_mul_of_nonneg_right hcoefficient
        (div_nonneg (Nat.cast_nonneg N) (pow_nonneg (by linarith) A))
    _ = _ := by ring

/-- This is Q17's unchanged remaining-rejection expression, with the
actual original outside pair sum. It is not defined by subtracting a
claimed main term from an unrelated quantity. -/
def originalJointRemainingError (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  ∑ t ∈ pairSupport N,sigma t*originalRemainingRejectedError N t Q rho T H δ K

theorem originalJointRemainingError_eq_upper_add_order
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) :
    originalJointRemainingError N Q rho sigma T H δ K =
      originalJointUpperError N Q rho sigma T H δ K+
        originalJointOrderError N Q rho sigma T H δ K := by
  rw [originalJointUpperError_eq_outer,originalJointOrderError_eq_outer]
  simp only [originalJointRemainingError,originalRemainingRejectedError_eq_upper_add_order,
    mul_add,Finset.sum_add_distrib]

/-- Full joint upper/order payment at ONE mesh, without pair cardinality
or a normalized-mass premise. All later source parameters share rho. -/
theorem eventually_originalJointRemainingError (A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ → ℝ)
      (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ 1) → 0 < δ →
      δ ≤ boundaryLogMesh (orderMeshExponent (jointListMomentOrder originalMotherOccurrences) A) N →
      |originalJointRemainingError N Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_originalJointUpperError A (eta/2) (half_pos heta),
    eventually_originalJointOrderError A (eta/2) (half_pos heta),
    eventually_one_le_nat_log] with N hupper horder hlog
  intro Q rho sigma T H δ K hQ hrho hsigma hδ hmesh
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hmeshupper : δ ≤ boundaryLogMesh
      (upperMeshExponent (jointListMomentOrder originalMotherOccurrences) A) N := by
    apply hmesh.trans
    unfold boundaryLogMesh
    exact one_div_le_one_div_of_le (pow_pos hlogpos _)
      (pow_le_pow_right₀ hlog (upperMeshExponent_le_orderMeshExponent _ _))
  rw [originalJointRemainingError_eq_upper_add_order]
  exact (abs_add _ _).trans ((add_le_add
    (hupper Q rho sigma T H δ K hQ hrho hsigma hmeshupper)
    (horder Q rho sigma T H δ K hQ hrho hsigma hδ hmesh)).trans_eq (by ring))

theorem originalJointRemainingError_smul (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ c : ℝ) (K : ℕ) :
    originalJointRemainingError N Q rho (fun t => c*sigma t) T H δ K =
      c*originalJointRemainingError N Q rho sigma T H δ K := by
  simp only [originalJointRemainingError,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Any fixed scalar height C is allowed BEFORE the common threshold.
No hypothesis about the cardinality or total mass of the family. -/
theorem eventually_originalJointRemainingError_height (C : ℝ) (hC : 0 < C)
    (A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ → ℝ)
      (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ C) → 0 < δ →
      δ ≤ boundaryLogMesh (orderMeshExponent (jointListMomentOrder originalMotherOccurrences) A) N →
      |originalJointRemainingError N Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_originalJointRemainingError A (eta/C) (div_pos heta hC)] with N hN
  intro Q rho sigma T H δ K hQ hrho hsigma hδ hmesh
  have hscaled : ∀ t ∈ pairSupport N,0 ≤ sigma t/C ∧ sigma t/C ≤ 1 := by
    intro t ht
    exact ⟨div_nonneg (hsigma t ht).1 hC.le,(div_le_one hC).mpr (hsigma t ht).2⟩
  have h := hN Q rho (fun t => sigma t/C) T H δ K hQ hrho hscaled hδ hmesh
  have heq : originalJointRemainingError N Q rho sigma T H δ K =
      C*originalJointRemainingError N Q rho (fun t => sigma t/C) T H δ K := by
    rw [← originalJointRemainingError_smul]
    congr 1
    funext t
    field_simp [hC.ne'] <;> ring
  rw [heq,abs_mul,abs_of_pos hC]
  calc
    _ ≤ C*((eta/C)*(N : ℝ)/(Real.log (N : ℝ))^A) :=
      mul_le_mul_of_nonneg_left h hC.le
    _ = (C*(eta/C))*(N : ℝ)/(Real.log (N : ℝ))^A := by ring
    _ = _ := by
      have hc : C*(eta/C)=eta := by field_simp [hC.ne']; ring
      rw [hc]

end
end ImbalancedChen.P2GammaJointRemainingPayment
