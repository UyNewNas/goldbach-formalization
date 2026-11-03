import ImbalancedChen.P2GammaDyadicJointLogSaving
import ImbalancedChen.P2GammaRetainedSameRhoMother

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Full chosen-grid and literal mother-list summation, with the complete
outside old-pair sum already INSIDE the joint analytic estimate. This
supersedes the selectorMass-bearing bound for this nonempty LOW-RANK lane.
The empty mother lane is not silently removed. The same upperRho is used.
-/
namespace ImbalancedChen.P2GammaJointMotherLogSaving
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaDyadicJointLogSaving P2GammaDyadicJointRowEstimate
open P2GammaRetainedSameRhoRows P2GammaRetainedSameRhoMother
open P2GammaChosenLogGridBudget P2GammaJointUpperPayment
open P2GammaCompleteProductTrimPayment P2GammaSmoothLogGrid
open P5OriginalU5CausalFinite (pairSupport)

/-- Only the already explicit nonempty-head lane; nil is exactly zero. -/
def jointHeadWord (N : ℕ) (cs : List ℕ) (H δ : ℝ) (K : ℕ)
    (nu epsilon : ℝ) (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
    (sigma : (ℕ × ℕ) → ℝ) : ℝ :=
  match cs with
  | [] => 0
  | c::ds => (∑ j ∈ Finset.range K,∑ l ∈ Finset.range K,
      jointSignedRow N c ds H δ j l nu epsilon retain cap Q
        (fun t => (sigma t : ℂ))).re

private theorem four_sum_exchange {α β γ δ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (S : Finset α) (T : Finset β) (U : Finset γ) (V : Finset δ)
    (f : α → β → γ → δ → ℝ) :
    (∑ a ∈ S,∑ b ∈ T,∑ c ∈ U,∑ d ∈ V,f a b c d) =
      ∑ d ∈ V,∑ c ∈ U,∑ a ∈ S,∑ b ∈ T,f a b c d := by
  calc
    _ = ∑ a ∈ S,∑ b ∈ T,∑ d ∈ V,∑ c ∈ U,f a b c d := by
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro b hb
      rw [Finset.sum_comm]
    _ = ∑ a ∈ S,∑ d ∈ V,∑ b ∈ T,∑ c ∈ U,f a b c d := by
      apply Finset.sum_congr rfl; intro a ha
      rw [Finset.sum_comm]
    _ = ∑ d ∈ V,∑ a ∈ S,∑ b ∈ T,∑ c ∈ U,f a b c d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro d hd
      calc
        _ = ∑ a ∈ S,∑ c ∈ U,∑ b ∈ T,f a b c d := by
          apply Finset.sum_congr rfl; intro a ha
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm

/-- Exact finite-source identification with the PREVIOUS headWordError;
no change to rho, signed mean, word multiplicity or the original pair set. -/
theorem jointHeadWord_eq_outer (N : ℕ) (cs : List ℕ) (H δ : ℝ) (K : ℕ)
    (nu epsilon : ℝ) (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
    (sigma : (ℕ × ℕ) → ℝ) :
    jointHeadWord N cs H δ K nu epsilon retain cap Q sigma =
      ∑ t ∈ pairSupport N,sigma t*headWordError N t cs Q
        (upperRho N nu epsilon retain cap) H δ K := by
  cases cs with
  | nil => simp [jointHeadWord,headWordError,headWordKernel]
  | cons c cs =>
      simp only [jointHeadWord,jointSignedRow,Complex.re_sum,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
        headWordError,headWordKernel,Finset.mul_sum]
      rw [four_sum_exchange]
      apply Finset.sum_congr rfl; intro t ht
      apply Finset.sum_congr rfl; intro q hq
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro l hl
      ring

/-- Sum over the complete original LIST, not a set of distinct words. -/
theorem headJointError_eq_joint_words (N : ℕ) (H δ : ℝ) (K : ℕ)
    (nu epsilon : ℝ) (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
    (sigma : (ℕ × ℕ) → ℝ) :
    headJointError N Q (upperRho N nu epsilon retain cap) sigma H δ K =
      (originalMotherOccurrences.map
        (fun cs => jointHeadWord N cs H δ K nu epsilon retain cap Q sigma)).sum := by
  have hlist (L : List (List ℕ)) :
      (L.map (fun cs => jointHeadWord N cs H δ K nu epsilon retain cap Q sigma)).sum =
        ∑ t ∈ pairSupport N,sigma t*
          (L.map (fun cs => headWordError N t cs Q
            (upperRho N nu epsilon retain cap) H δ K)).sum := by
    induction L with
    | nil => simp
    | cons cs L ih =>
        simp only [List.map_cons,List.sum_cons,jointHeadWord_eq_outer,ih,
          mul_add,Finset.sum_add_distrib]
  exact (hlist originalMotherOccurrences).symm

/-- Pure finite grid summation. Its row bounds are ACTUALLY supplied by
the next theorem, not left as an analytic premise of the final endpoint. -/
theorem jointHeadWord_le_grid (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (K : ℕ)
    (nu epsilon : ℝ) (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
    (sigma : (ℕ × ℕ) → ℝ) (E : ℝ)
    (hrow : ∀ j ∈ Finset.range K,∀ l ∈ Finset.range K,
      ‖jointSignedRow N c cs H δ j l nu epsilon retain cap Q
        (fun t => (sigma t : ℂ))‖ ≤ E) :
    |jointHeadWord N (c::cs) H δ K nu epsilon retain cap Q sigma| ≤ (K : ℝ)^2*E := by
  apply (Complex.abs_re_le_norm _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range K,‖∑ l ∈ Finset.range K,
        jointSignedRow N c cs H δ j l nu epsilon retain cap Q (fun t => (sigma t : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range K,∑ l ∈ Finset.range K,
        ‖jointSignedRow N c cs H δ j l nu epsilon retain cap Q (fun t => (sigma t : ℂ))‖ :=
      Finset.sum_le_sum (fun j hj => norm_sum_le _ _)
    _ ≤ ∑ j ∈ Finset.range K,∑ l ∈ Finset.range K,E :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun l hl => hrow j hj l hl))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

private theorem abs_list_sum_le {α : Type*} (L : List α) (f : α → ℝ) (E : ℝ)
    (h : ∀ a ∈ L,|f a| ≤ E) : |(L.map f).sum| ≤ (L.length : ℝ)*E := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have ha := h a (List.mem_cons_self a L)
      have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      exact (abs_add _ _).trans ((add_le_add ha ht).trans_eq (by ring))

/-- One inherited symbolic joint maximum supplies BOTH required orders
for every actual nonempty mother occurrence. No literal list is evaluated. -/
theorem mother_joint_orders {c : ℕ} {cs : List ℕ}
    (h : (c::cs) ∈ originalMotherOccurrences) :
    cs.length+2 ≤ jointListMomentOrder originalMotherOccurrences ∧
      (cs.length+3)^2-1 ≤ jointListMomentOrder originalMotherOccurrences := by
  have hh := le_jointListMomentOrder h
  simp only [List.length_cons] at hh
  have hsq : (cs.length+3)^2 ≤ (cs.length+1+3)^2 := by nlinarith
  have hlen : cs.length+3 ≤ (cs.length+1+3)^2 := by nlinarith
  constructor <;> omega

/-- Full JOINT nonempty-head source, every chart and every original mother
occurrence, with no outside L1 mass or pair/block count. The height remains
linear and all analytic constants precede every later selector and policy. -/
theorem exists_joint_head_log_saving (A B : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk : kappa ≤ 1/100) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
        (sigma : (ℕ × ℕ) → ℝ) (height : ℝ),0 ≤ height →
      (∀ t ∈ pairSupport N,|sigma t| ≤ height) →
      |headJointError N Q (upperRho N nu epsilon retain cap) sigma
        (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N) (gridLength B N)| ≤
        C*height*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let d := 2*(B+1)
  let J := jointListMomentOrder originalMotherOccurrences
  obtain ⟨C,hC,hrow⟩ := exists_joint_row_log_saving (A+d) B J hB kappa hk0 hk
  let L := originalMotherOccurrences
  refine ⟨9*(L.length : ℝ)*C+1,by positivity,?_⟩
  filter_upwards [hrow,eventually_one_le_nat_log] with N hrows hlog
  intro nu epsilon hnu hnu1 heps heps1 retain cap Q sigma height hh hs
  let E := C*height*(N : ℝ)/(Real.log (N : ℝ))^(A+d)
  have hlogp : 0 < Real.log (N : ℝ) := by linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hscomplex : ∀ t ∈ pairSupport N,‖(sigma t : ℂ)‖ ≤ height := by
    intro t ht
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hs t ht
  have hword : ∀ cs ∈ L,
      |jointHeadWord N cs (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N)
        (gridLength B N) nu epsilon retain cap Q sigma| ≤ (gridLength B N : ℝ)^2*E := by
    intro cs hcs
    cases cs with
    | nil => simp only [jointHeadWord,abs_zero]; positivity
    | cons c cs =>
        obtain ⟨hJ1,hJ2⟩ := mother_joint_orders hcs
        exact jointHeadWord_le_grid N c cs _ _ _ nu epsilon retain cap Q sigma E
          (fun j hj l hl => hrows c cs hJ1 hJ2 j l nu epsilon hnu hnu1 heps heps1
            retain cap Q (fun t => (sigma t : ℂ)) height hh hscomplex)
  rw [headJointError_eq_joint_words]
  have hcount : (gridLength B N : ℝ)^2 ≤ 9*(Real.log (N : ℝ))^d := by
    simpa only [Finset.card_product,Finset.card_range,Nat.cast_mul,pow_two,d] using
      (chosen_chart_count_le (B:=B) hlog)
  calc
    _ ≤ (L.length : ℝ)*((gridLength B N : ℝ)^2*E) :=
      abs_list_sum_le L _ _ hword
    _ ≤ (L.length : ℝ)*(9*(Real.log (N : ℝ))^d*E) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcount hE) (Nat.cast_nonneg _)
    _ = (9*(L.length : ℝ)*C)*height*(N : ℝ)/(Real.log (N : ℝ))^A := by
      dsimp [E]
      rw [pow_add]
      field_simp [hlogp.ne'] <;> ring
    _ ≤ _ := by gcongr; linarith

/-- A fixed height precedes the common threshold. The mesh exponent B is
kept unchanged when requesting stronger accuracy; this avoids a circular
choice of finer mesh after the analytic constants have been selected. -/
theorem eventually_joint_head_logAccuracy (A B : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk : kappa ≤ 1/100)
    (height : ℝ) (hh : 0 ≤ height) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ) (sigma : (ℕ × ℕ) → ℝ),
      (∀ t ∈ pairSupport N,|sigma t| ≤ height) →
      |headJointError N Q (upperRho N nu epsilon retain cap) sigma
        (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N) (gridLength B N)| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  obtain ⟨C,hC,hbound⟩ := exists_joint_head_log_saving (A+1) B hB kappa hk0 hk
  filter_upwards [hbound,eventually_one_le_nat_log,
    eventually_boundaryLogMesh_main_le_logAccuracy (C*height) A
      (k:=A+3) (by omega) eta heta] with N hN hlog hsmall
  intro nu epsilon hnu hnu1 heps heps1 retain cap Q sigma hs
  have hp : 0 < Real.log (N : ℝ) := by linarith
  have hcost : C*height*(N : ℝ)/(Real.log (N : ℝ))^(A+1) ≤
      eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
    convert hsmall using 1
    unfold boundaryLogMesh
    simp only [pow_add]
    field_simp [hp.ne'] <;> ring
  exact (hN nu epsilon hnu hnu1 heps heps1 retain cap Q sigma height hh hs).trans hcost

end
end ImbalancedChen.P2GammaJointMotherLogSaving
