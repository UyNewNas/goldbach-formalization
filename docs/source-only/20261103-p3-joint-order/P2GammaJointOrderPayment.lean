import ImbalancedChen.P2GammaJointOrderGeometry
import ImbalancedChen.P2GammaJointUpperPayment

/-!
Source-only P3.6 continuation. UNCOMPILED / KERNEL-UNVERIFIED.
The actual outer old-pair sum is taken before the error is bounded.
This file pays the original strict-order rejection and assembles it with
R17's upper rejection on the unchanged Q17 source and mother LIST.
The conclusion is absolute logarithmic accuracy, NOT relative Theta.
The lower rejection and causal common-Q identification remain separate.
-/

namespace ImbalancedChen.P2GammaJointOrderPayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2OriginalGammaUpperLowRankConsumer
open P2GammaCompleteProductTrimPayment P2GammaRetainedInteriorGeometry
open P2GammaLowerRejectedPayment P2GammaUpperStripPayment
open P2GammaOrderingStripPayment P2GammaJointLabels
open P2GammaJointOrderGeometry P2GammaJointUpperPayment
open P5OriginalU5CausalFinite (pairSupport)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem cast_card_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ)^2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith

/-- Q17's unshifted-moment argument, attached to the ACTUAL JOINT
multiplicity from R17. No energy hypothesis or pair-cardinality loss. -/
theorem joint_label_kernel_energy_le {N : ℕ} (hN : 1 ≤ N)
    (cs : List ℕ) (J : ℕ) (hJ : (cs.length+3)^2-1 ≤ J) :
    (∑ z ∈ jointLabels N cs,
      (((N-jointProduct z).divisors.card : ℝ)+
        4*(1+Real.log (N : ℝ)))^2) ≤
      34*(N : ℝ)*(1+Real.log (N : ℝ))^(kernelMomentExponent J) := by
  let S := upperProducts N (N : ℝ)
  let L := 1+Real.log (N : ℝ)
  let a := fun m => ((jointProductFiber N cs m).card : ℝ)
  let b := fun m => ((N-m).divisors.card : ℝ)+4*L
  let E := kernelMomentExponent J
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hNr]
  have hS : S ⊆ Finset.Ioc 0 N := Finset.filter_subset _ _
  have hS' : S ⊆ Finset.Ioc 0 ⌊(N : ℝ)⌋₊ := by
    simpa only [Nat.floor_natCast] using hS
  have ha : (∑ m ∈ S,a m^2) ≤ (N : ℝ)*L^J :=
    (joint_multiplicity_square_sum_le N cs hNr S hS').trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hJ) (Nat.cast_nonneg N))
  have h4 : (∑ m ∈ S,((N-m).divisors.card : ℝ)^4) ≤ (N : ℝ)*L^15 := by
    let T := S.image (fun m => N-m)
    have hT : T ⊆ Finset.Ioc 0 N := by
      intro n hn
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
      simpa only [Nat.floor_natCast] using
        upperProducts_difference_maps (Nat.cast_nonneg N) m hm
    calc
      _ = ∑ n ∈ T,(n.divisors.card : ℝ)^4 :=
        (Finset.sum_image (upperProducts_difference_inj N (N : ℝ))).symm
      _ ≤ ∑ n ∈ Finset.Ioc 0 N,(n.divisors.card : ℝ)^4 :=
        Finset.sum_le_sum_of_subset_of_nonneg hT (fun n hn hnot => by positivity)
      _ ≤ _ := by
        simpa only [Nat.floor_natCast,fouvryTau_two] using
          sum_fouvryTau_pow_le_real (k := 2) (by norm_num) 4 hNr
  have hproducts : jointProducts N cs ⊆ S := by
    intro m hm
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(jointProduct_bounds hz).1,(jointProduct_bounds hz).2.le⟩,
        (jointProduct_bounds hz).2,by exact_mod_cast Nat.sub_le N (jointProduct z)⟩
  have hpoint (m : ℕ) : a m*b m^2 ≤
      a m^2+((N-m).divisors.card : ℝ)^4+32*L^2*a m^2 := by
    have ha0 : 0 ≤ a m := Nat.cast_nonneg _
    have hnat : a m ≤ a m^2 := cast_card_le_sq _
    have hb : b m^2 ≤ 2*((N-m).divisors.card : ℝ)^2+32*L^2 := by
      dsimp [b]
      nlinarith [sq_nonneg (((N-m).divisors.card : ℝ)-4*L)]
    have hmul := mul_le_mul_of_nonneg_left hb ha0
    have hyoung := sq_nonneg (a m-((N-m).divisors.card : ℝ)^2)
    have hmean := mul_le_mul_of_nonneg_left hnat (show 0 ≤ 32*L^2 by positivity)
    nlinarith
  have hJE : J ≤ E := (show J ≤ J+2 by omega).trans (le_max_left _ _)
  have hJ2E : J+2 ≤ E := le_max_left _ _
  have h15E : 15 ≤ E := le_max_right _ _
  have hpa : (N : ℝ)*L^J ≤ (N : ℝ)*L^E :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hJE) (Nat.cast_nonneg N)
  have hp4 : (N : ℝ)*L^15 ≤ (N : ℝ)*L^E :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL h15E) (Nat.cast_nonneg N)
  have hpmean : 32*L^2*((N : ℝ)*L^J) ≤ 32*(N : ℝ)*L^E := by
    calc
      _ = 32*(N : ℝ)*L^(J+2) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hJ2E) (by positivity)
  calc
    _ = ∑ m ∈ jointProducts N cs,a m*b m^2 :=
      joint_real_test_eq_grouped N cs (fun m => b m^2)
    _ ≤ ∑ m ∈ S,a m*b m^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hproducts (fun m hm hnot => by dsimp [a]; positivity)
    _ ≤ ∑ m ∈ S,a m^2+((N-m).divisors.card : ℝ)^4+32*L^2*a m^2 :=
      Finset.sum_le_sum (fun m hm => hpoint m)
    _ = (∑ m ∈ S,a m^2)+(∑ m ∈ S,((N-m).divisors.card : ℝ)^4)+
        32*L^2*(∑ m ∈ S,a m^2) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ (N : ℝ)*L^J+(N : ℝ)*L^15+32*L^2*((N : ℝ)*L^J) := by gcongr
    _ ≤ 34*(N : ℝ)*L^E := by nlinarith

/-- Finite joint strict-order payment, before asymptotics or a selector
choice. The thin count and the full kernel moment are supplied above. -/
theorem jointError_order_strip_le {N : ℕ} (hN : 1 ≤ N)
    (cs : List ℕ) (hlen : 2 ≤ cs.length) (J : ℕ)
    (hJ : (cs.length+3)^2-1 ≤ J) {e u : ℝ} (he : 0 ≤ e) (hu : 0 < u)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (w : JointLabel → ℝ)
    (hQ : Q ⊆ Finset.Icc 1 N) (hrho : ∀ q ∈ Q,|rho q| ≤ 1)
    (hw : ∀ z ∈ jointLabels N cs,|w z| ≤ 1)
    (hzero : ∀ z ∈ jointLabels N cs,z ∉ jointOrderLabels N cs e → w z=0) :
    |jointError N cs Q rho w| ≤
      u*e*(N : ℝ)*(1+Real.log (N : ℝ))^(cs.length+1)+
        34*(N : ℝ)*(1+Real.log (N : ℝ))^(kernelMomentExponent J)/u := by
  let S := jointOrderLabels N cs e
  let L := 1+Real.log (N : ℝ)
  let b := fun z : JointLabel => ((N-jointProduct z).divisors.card : ℝ)+4*L
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsub : S ⊆ jointLabels N cs := Finset.filter_subset _ _
  have hlabel : |jointError N cs Q rho w| ≤ ∑ z ∈ S,b z := by
    have heq : jointError N cs Q rho w =
        ∑ z ∈ jointLabels N cs,w z*∑ q ∈ Q,rho q*gammaKernel N q (jointProduct z) := by
      simp only [jointError,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro q hq
      ring
    rw [heq]
    calc
      _ ≤ ∑ z ∈ jointLabels N cs,
          |w z*∑ q ∈ Q,rho q*gammaKernel N q (jointProduct z)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z ∈ jointLabels N cs,if z ∈ S then b z else 0 := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hs : z ∈ S
        · rw [if_pos hs,abs_mul]
          have hk := kernel_absolute_modulus_sum_le (jointProduct_bounds hz).2 Q rho hQ hrho
          rw [max_eq_right hNr] at hk
          exact (mul_le_mul (hw z hz) (Finset.abs_sum_le_sum_abs _ _)
            (abs_nonneg _) zero_le_one).trans (by simpa only [one_mul] using hk)
        · simp only [if_neg hs,hzero z hz hs,zero_mul,abs_zero]
      _ = ∑ z ∈ S,b z := by
        rw [← Finset.sum_filter]
        congr 1
        ext z
        simp [S,jointOrderLabels]
  have henergy : (∑ z ∈ S,b z^2) ≤
      34*(N : ℝ)*L^(kernelMomentExponent J) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z hz hnot => sq_nonneg _)).trans
      (joint_label_kernel_energy_le hN cs J hJ)
  have hcard := jointOrderLabels_card_le N cs hlen he
  calc
    _ ≤ ∑ z ∈ S,b z := hlabel
    _ ≤ ∑ z ∈ S,u+b z^2/u :=
      Finset.sum_le_sum (fun z hz => by simpa using young_scaled 1 (b z) u hu)
    _ = u*(S.card : ℝ)+(∑ z ∈ S,b z^2)/u := by
      rw [Finset.sum_add_distrib,Finset.sum_div]
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ u*(e*(N : ℝ)*L^(cs.length+1))+
        (34*(N : ℝ)*L^(kernelMomentExponent J))/u := by gcongr
    _ = _ := by ring

def jointOrderWordError (N : ℕ) (cs : List ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  jointError N cs Q rho (fun z => sigma z.1*wordOrderRejectedWeight N z.1 cs T H δ K z.2)

theorem jointOrderWordError_eq_outer (N : ℕ) (cs : List ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) :
    jointOrderWordError N cs Q rho sigma T H δ K =
      ∑ t ∈ pairSupport N,sigma t*wordError N t cs Q rho
        (wordOrderRejectedWeight N t cs T H δ K) := by
  exact jointError_eq_outer_wordError N cs Q rho sigma _

/-- Elementary balance reused from Q17's private scalar calculation.
It is not a new analytic estimate. -/
private theorem joint_order_log_budget {N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ))
    (J A : ℕ) :
    (Real.log (N : ℝ))^(kernelMomentExponent J+(A+2))*
      (4*boundaryLogMesh (orderMeshExponent J A) N)*(N : ℝ)*
        (1+Real.log (N : ℝ))^J+
      34*(N : ℝ)*(1+Real.log (N : ℝ))^(kernelMomentExponent J)/
        (Real.log (N : ℝ))^(kernelMomentExponent J+(A+2)) ≤
      (4*(2 : ℝ)^J+34*(2 : ℝ)^(kernelMomentExponent J))*(N : ℝ)/
        (Real.log (N : ℝ))^(A+2) := by
  let l := Real.log (N : ℝ)
  let E := kernelMomentExponent J
  have hl : 0 < l := by dsimp [l]; linarith
  have hL : 1+l ≤ 2*l := by dsimp [l]; linarith
  have hJ : (1+l)^J ≤ (2*l)^J := pow_le_pow_left₀ (by linarith) hL J
  have hE : (1+l)^E ≤ (2*l)^E := pow_le_pow_left₀ (by linarith) hL E
  calc
    _ ≤ l^(E+(A+2))*(4*boundaryLogMesh (orderMeshExponent J A) N)*
          (N : ℝ)*(2*l)^J+34*(N : ℝ)*(2*l)^E/l^(E+(A+2)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hJ (by unfold boundaryLogMesh; positivity)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity)
    _ = _ := by
      change l^(E+(A+2))*(4*(1/l^(E+(A+2)+J+(A+2))))*(N : ℝ)*(2*l)^J+
        34*(N : ℝ)*(2*l)^E/l^(E+(A+2)) =
          (4*(2 : ℝ)^J+34*(2 : ℝ)^E)*(N : ℝ)/l^(A+2)
      simp only [pow_add,mul_pow]
      field_simp [hl.ne']
      ring

/-- All positive pair selectors of height at most one are quantified
AFTER one N threshold. The original word/trim/quotient and rho persist. -/
theorem eventually_jointOrderWordError (J A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (cs : List ℕ),(cs.length+3)^2-1 ≤ J →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ)
        (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ 1) →
      0 < δ → δ ≤ boundaryLogMesh (orderMeshExponent J A) N →
      |jointOrderWordError N cs Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let B := orderMeshExponent J A
  let E := kernelMomentExponent J
  let C : ℝ := 4*(2 : ℝ)^J+34*(2 : ℝ)^E
  have hB : 0 < B := by dsimp [B,orderMeshExponent]; omega
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmesh : ∀ᶠ N : ℕ in atTop,2*boundaryLogMesh B N ≤ Real.log 2 := by
    have h := (tendsto_boundaryLogMesh hB).eventually (gt_mem_nhds (half_pos hlog2))
    filter_upwards [h] with N hN
    linarith
  have hcost := eventually_boundaryLogMesh_main_le_logAccuracy C A
    (k := A+4) (by omega) eta heta
  filter_upwards [hmesh,hcost,eventually_one_le_nat_log,eventually_ge_atTop (1 : ℕ)]
    with N hmeshN hcostN hlog hN
  intro cs hJ Q rho sigma T H δ K hQ hrho hsigma hδ hδmesh
  let l := Real.log (N : ℝ)
  let L := 1+l
  let u := l^(E+(A+2))
  let e := Real.exp (2*δ)-1
  let w : JointLabel → ℝ := fun z => sigma z.1*wordOrderRejectedWeight N z.1 cs T H δ K z.2
  have hl : 0 < l := by dsimp [l]; linarith
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have he := exp_order_width_le hδ.le (by linarith)
  have hewidth : e ≤ 4*boundaryLogMesh B N := he.2.trans (by linarith)
  have hw : ∀ z ∈ jointLabels N cs,|w z| ≤ 1 := by
    intro z hz
    have ht := (mem_jointLabels N cs z).mp hz
    have hs : |sigma z.1| ≤ 1 := by rw [abs_of_nonneg (hsigma z.1 ht.1).1]; exact (hsigma z.1 ht.1).2
    dsimp [w]
    rw [abs_mul]
    exact (mul_le_mul hs (wordOrderRejectedWeight_abs_le_one N z.1 cs T H δ K z.2)
      (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hzero : ∀ z ∈ jointLabels N cs,z ∉ jointOrderLabels N cs e → w z=0 := by
    intro z hz hnot
    by_contra hnonzero
    have ht := (mem_jointLabels N cs z).mp hz
    have hword : wordOrderRejectedWeight N z.1 cs T H δ K z.2 ≠ 0 := by
      intro h
      exact hnonzero (by simp [w,h])
    exact hnot (Finset.mem_filter.mpr ⟨hz,wordOrderRejectedWeight_mem ht.1 hδ ht.2 hword⟩)
  by_cases hlen : 2 ≤ cs.length
  · have hfinite := jointError_order_strip_le hN cs hlen J hJ he.1 hu Q rho w hQ hrho hw hzero
    have hkJ : cs.length+1 ≤ J := by
      have hs : cs.length+2 ≤ (cs.length+3)^2 := by nlinarith
      omega
    have hpow : L^(cs.length+1) ≤ L^J := pow_le_pow_right₀ hL hkJ
    have hcoef : u*e*(N : ℝ) ≤ u*(4*boundaryLogMesh B N)*(N : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hewidth hu.le) (Nat.cast_nonneg N)
    have hcoef0 : 0 ≤ u*(4*boundaryLogMesh B N)*(N : ℝ) := by
      have hb0 : 0 ≤ boundaryLogMesh B N := (hδ.trans_le hδmesh).le
      positivity
    have hfirst := mul_le_mul hcoef hpow (pow_nonneg (by linarith : 0 ≤ L) _) hcoef0
    have hcost' : C*(N : ℝ)/l^(A+2) ≤ eta*(N : ℝ)/l^A := by
      have heq : C*(N : ℝ)/l^(A+2)=C*boundaryLogMesh (A+4) N*(N : ℝ)*l^2 := by
        unfold boundaryLogMesh
        change C*(N : ℝ)/l^(A+2)=C*(1/l^(A+4))*(N : ℝ)*l^2
        rw [show A+4=(A+2)+2 by omega,pow_add]
        field_simp [hl.ne']
        ring
      rw [heq]
      exact hcostN
    exact hfinite.trans ((add_le_add_right hfirst _).trans
      ((joint_order_log_budget hlog J A).trans hcost'))
  · have hshort := jointOrderLabels_empty_of_short (N := N) (show cs.length ≤ 1 by omega) e
    have hz : ∀ z ∈ jointLabels N cs,w z=0 := by
      intro z hz
      apply hzero z hz
      rw [hshort]
      exact Finset.not_mem_empty z
    have herr : jointError N cs Q rho w=0 := by
      unfold jointError
      apply Finset.sum_eq_zero
      intro q hq
      have hs : (∑ z ∈ jointLabels N cs,w z*gammaKernel N q (jointProduct z))=0 :=
        Finset.sum_eq_zero (fun z hz' => by rw [hz z hz',zero_mul])
      rw [hs,mul_zero]
    change |jointError N cs Q rho w| ≤ _
    rw [herr,abs_zero]
    exact div_nonneg (mul_nonneg heta.le (Nat.cast_nonneg N)) (pow_nonneg hl.le A)

end
end ImbalancedChen.P2GammaJointOrderPayment
