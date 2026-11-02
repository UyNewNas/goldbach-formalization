import ImbalancedChen.P2GammaJointLabels

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An absolute arbitrary-log upper-rejection payment for the complete joint
pair/word/quotient source and the literal mother OCCURRENCE LIST. The
threshold precedes the one-bounded outer selector, moduli, signed rho
and all trim/grid parameters. No cardinality of pairSupport is charged.

The scalar log balancing below repeats Q's numerical calculation because
Q's logMesh_budget is private. It is reuse, not a new analytic estimate.
The new arithmetic input is P2GammaJointLabels.jointError_upper_strip_le.
This is not a relative-Theta payment for positive-mass marked families.
-/

namespace ImbalancedChen.P2GammaJointUpperPayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2GammaCompleteProductTrimPayment P2GammaUpperStripPayment
open P2GammaJointLabels
open P5OriginalU5CausalFinite (pairSupport)

private theorem joint_log_budget {N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ))
    (J A : ℕ) :
    (1/(Real.log (N : ℝ))^(J+(A+2)))*(N : ℝ)*(1+Real.log (N : ℝ))^J+
      34*(4*boundaryLogMesh (upperMeshExponent J A) N*(N : ℝ))*
        (1+Real.log (N : ℝ))^3/(1/(Real.log (N : ℝ))^(J+(A+2))) ≤
      ((2 : ℝ)^J+1088)*(N : ℝ)/(Real.log (N : ℝ))^(A+2) := by
  let l := Real.log (N : ℝ)
  have hl : 0 < l := by dsimp [l]; linarith
  have hL : 1+l ≤ 2*l := by dsimp [l]; linarith
  have hJ := pow_le_pow_left₀ (by linarith : 0 ≤ 1+l) hL J
  have h3 := pow_le_pow_left₀ (by linarith : 0 ≤ 1+l) hL 3
  calc
    _ ≤ (1/l^(J+(A+2)))*(N : ℝ)*(2*l)^J+
        34*(4*boundaryLogMesh (upperMeshExponent J A) N*(N : ℝ))*
          (2*l)^3/(1/l^(J+(A+2))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hJ (by positivity)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h3 (by unfold boundaryLogMesh; positivity)) (by positivity)
    _ = _ := by
      change (1/l^(J+(A+2)))*(N : ℝ)*(2*l)^J+
        34*(4*(1/l^(J+(A+2)+(A+2)+3))*(N : ℝ))*(2*l)^3/
          (1/l^(J+(A+2))) = ((2 : ℝ)^J+1088)*(N : ℝ)/l^(A+2)
      simp only [pow_add,mul_pow]
      field_simp [hl.ne']
      ring

/-- Every bounded weight on the ACTUAL joint source is covered, provided
its support lies on the literal upper wall. No error estimate is an input. -/
theorem eventually_joint_upper_wall_logAccuracy (J A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (cs : List ℕ),(cs.length+3)^2-1 ≤ J →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (w : JointLabel → ℝ) (δ : ℝ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      δ ≤ boundaryLogMesh (upperMeshExponent J A) N →
      (∀ z ∈ jointLabels N cs,|w z| ≤ 1) →
      (∀ z ∈ jointLabels N cs,w z ≠ 0 →
        (N : ℝ) < (jointProduct z : ℝ)*Real.exp (4*δ)) →
      |jointError N cs Q rho w| ≤ eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let B := upperMeshExponent J A
  let C : ℝ := (2 : ℝ)^J+1088
  have hB : 0 < B := by dsimp [B,upperMeshExponent]; omega
  have hmesh : ∀ᶠ N : ℕ in atTop,4*boundaryLogMesh B N ≤ 1 := by
    have h := (tendsto_boundaryLogMesh hB).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))
    filter_upwards [h] with N hN
    linarith
  have hgrowth : ∀ᶠ N : ℕ in atTop,(Real.log (N : ℝ))^B ≤ N := by
    simpa only [Real.rpow_zero,one_mul,pow_zero,div_one] using
      eventually_powerLog_le_logAccuracy 1 0 B 0 (by norm_num) 1 (by norm_num)
  have hcost := eventually_boundaryLogMesh_main_le_logAccuracy C A
    (k := A+4) (by omega) eta heta
  filter_upwards [hmesh,hgrowth,hcost,eventually_one_le_nat_log,
    eventually_ge_atTop (1 : ℕ)] with N hmeshN hgrowthN hcostN hlog hN
  intro cs hJ Q rho w δ hQ hrho hδ hw hwall
  let l := Real.log (N : ℝ)
  let Y := 4*boundaryLogMesh B N*(N : ℝ)
  let u := 1/l^(J+(A+2))
  have hl : 0 < l := by dsimp [l]; linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hYN : Y ≤ N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hmeshN (Nat.cast_nonneg N)
  have hY : 1 ≤ Y := by
    have hratio : 1 ≤ (N : ℝ)/l^B :=
      (le_div_iff₀ (pow_pos hl B)).mpr (by simpa only [one_mul] using hgrowthN)
    have hYeq : Y=4*((N : ℝ)/l^B) := by dsimp [Y,boundaryLogMesh,l]; ring
    rw [hYeq]
    linarith
  have hzero : ∀ z ∈ jointLabels N cs,Y < ((N-jointProduct z : ℕ) : ℝ) → w z=0 := by
    intro z hz hlarge
    by_contra hwz
    have hd := upper_wall_difference_le (jointProduct_bounds hz).2 (hwall z hz hwz)
    have hwidth : 4*δ*(N : ℝ) ≤ Y := by dsimp [Y]; gcongr
    exact (not_lt_of_ge (hd.trans hwidth)) hlarge
  have hfinite := jointError_upper_strip_le hN cs J hJ hY hYN hu Q rho w hQ hrho hw hzero
  have hcost' : C*(N : ℝ)/l^(A+2) ≤ eta*(N : ℝ)/l^A := by
    have heq : C*(N : ℝ)/l^(A+2)=C*boundaryLogMesh (A+4) N*(N : ℝ)*l^2 := by
      unfold boundaryLogMesh
      change C*(N : ℝ)/l^(A+2)=C*(1/l^(A+4))*(N : ℝ)*l^2
      rw [show A+4=(A+2)+2 by omega,pow_add]
      field_simp [hl.ne']
      ring
    rw [heq]
    exact hcostN
  exact hfinite.trans ((joint_log_budget hlog J A).trans hcost')

def jointUpperWordError (N : ℕ) (cs : List ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  jointError N cs Q rho
    (fun z => sigma z.1*wordUpperRejectedWeight N z.1 cs T H δ K z.2)

theorem jointUpperWordError_eq_outer (N : ℕ) (cs : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) :
    jointUpperWordError N cs Q rho sigma T H δ K =
      ∑ t ∈ pairSupport N,sigma t*wordError N t cs Q rho
        (wordUpperRejectedWeight N t cs T H δ K) :=
  jointError_eq_outer_wordError N cs Q rho sigma
    (fun z => wordUpperRejectedWeight N z.1 cs T H δ K z.2)

/-- This attaches Q's ACTUAL aggregate upper rejection, including the
unchanged smooth trim and first-priority lower split. Grid size is free. -/
theorem eventually_jointUpperWordError (J A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (cs : List ℕ),(cs.length+3)^2-1 ≤ J →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ)
        (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ 1) →
      δ ≤ boundaryLogMesh (upperMeshExponent J A) N →
      |jointUpperWordError N cs Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_joint_upper_wall_logAccuracy J A eta heta] with N hN
  intro cs hJ Q rho sigma T H δ K hQ hrho hsigma hδ
  apply hN cs hJ Q rho
    (fun z => sigma z.1*wordUpperRejectedWeight N z.1 cs T H δ K z.2) δ hQ hrho hδ
  · intro z hz
    have ht := (mem_jointLabels N cs z).mp hz
    rw [abs_mul,abs_of_nonneg (hsigma z.1 ht.1).1]
    exact (mul_le_mul (hsigma z.1 ht.1).2
      (wordUpperRejectedWeight_abs_le_one N z.1 cs T H δ K z.2)
      (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
  · intro z hz hw
    have hweight : wordUpperRejectedWeight N z.1 cs T H δ K z.2 ≠ 0 := by
      intro heq
      exact hw (by rw [heq,mul_zero])
    exact wordUpperRejectedWeight_support hweight

def jointListMomentOrder : List (List ℕ) → ℕ
  | [] => 0
  | cs::L => max ((cs.length+3)^2-1) (jointListMomentOrder L)

theorem le_jointListMomentOrder {L : List (List ℕ)} {cs : List ℕ} (h : cs ∈ L) :
    (cs.length+3)^2-1 ≤ jointListMomentOrder L := by
  induction L with
  | nil => simp at h
  | cons ds L ih =>
      rcases List.mem_cons.mp h with rfl|h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

def originalJointUpperError (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  (originalMotherOccurrences.map
    (fun cs => jointUpperWordError N cs Q rho sigma T H δ K)).sum

/-- Literal mother occurrences are retained, including equal words.
This equality binds the new joint estimate to Q's exact outer source. -/
theorem originalJointUpperError_eq_outer (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) :
    originalJointUpperError N Q rho sigma T H δ K =
      ∑ t ∈ pairSupport N,sigma t*originalUpperRejectedError N t Q rho T H δ K := by
  have hlist (L : List (List ℕ)) :
      (L.map (fun cs => jointUpperWordError N cs Q rho sigma T H δ K)).sum =
        ∑ t ∈ pairSupport N,sigma t*(L.map (fun cs =>
          wordError N t cs Q rho (wordUpperRejectedWeight N t cs T H δ K))).sum := by
    induction L with
    | nil => simp
    | cons cs L ih =>
        simp only [List.map_cons,List.sum_cons,jointUpperWordError_eq_outer,ih,
          mul_add,Finset.sum_add_distrib]
  exact hlist originalMotherOccurrences

/-- A single threshold pays the full actual outer-pair upper rejection.
All later positive selectors of height at most one are covered uniformly.
The conclusion is absolute N/log^A N; it is NOT epsilon times Theta_Q. -/
theorem eventually_originalJointUpperError (A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ → ℝ)
      (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ 1) →
      δ ≤ boundaryLogMesh (upperMeshExponent (jointListMomentOrder originalMotherOccurrences) A) N →
      |originalJointUpperError N Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let L := originalMotherOccurrences
  let J := jointListMomentOrder L
  let eta0 := eta/((L.length : ℝ)+1)
  have heta0 : 0 < eta0 := by dsimp [eta0]; positivity
  filter_upwards [eventually_jointUpperWordError J A eta0 heta0,
    eventually_one_le_nat_log] with N hword hlog
  intro Q rho sigma T H δ K hQ hrho hsigma hδ
  let f := fun cs => jointUpperWordError N cs Q rho sigma T H δ K
  let E := eta0*(N : ℝ)/(Real.log (N : ℝ))^A
  have heach : ∀ cs ∈ L,|f cs| ≤ E := by
    intro cs hcs
    exact hword cs (le_jointListMomentOrder hcs) Q rho sigma T H δ K hQ hrho hsigma hδ
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

theorem originalJointUpperError_smul (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ c : ℝ) (K : ℕ) :
    originalJointUpperError N Q rho (fun t => c*sigma t) T H δ K =
      c*originalJointUpperError N Q rho sigma T H δ K := by
  rw [originalJointUpperError_eq_outer,originalJointUpperError_eq_outer,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- A fixed external scalar height is allowed. C is fixed before the
single threshold, which still precedes every chosen positive family.
This supplies absolute accuracy without assuming a mass/Theta comparison. -/
theorem eventually_originalJointUpperError_height (C : ℝ) (hC : 0 < C)
    (A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ → ℝ)
      (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ C) →
      δ ≤ boundaryLogMesh (upperMeshExponent (jointListMomentOrder originalMotherOccurrences) A) N →
      |originalJointUpperError N Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_originalJointUpperError A (eta/C) (div_pos heta hC)] with N hN
  intro Q rho sigma T H δ K hQ hrho hsigma hδ
  have hscaled : ∀ t ∈ pairSupport N,0 ≤ sigma t/C ∧ sigma t/C ≤ 1 := by
    intro t ht
    exact ⟨div_nonneg (hsigma t ht).1 hC.le,(div_le_one hC).mpr (hsigma t ht).2⟩
  have h := hN Q rho (fun t => sigma t/C) T H δ K hQ hrho hscaled hδ
  have heq : originalJointUpperError N Q rho sigma T H δ K =
      C*originalJointUpperError N Q rho (fun t => sigma t/C) T H δ K := by
    rw [← originalJointUpperError_smul]
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
end ImbalancedChen.P2GammaJointUpperPayment
