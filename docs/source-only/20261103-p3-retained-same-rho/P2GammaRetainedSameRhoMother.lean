import ImbalancedChen.P2GammaRetainedSameRhoRows

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
The full literal mother occurrence list and both chosen grid indices are
summed with ONE original rho. Empty words are retained in a separate exact
lane, not assumed absent. The outer-pair estimate records its L1 cost;
it is not silently promoted to a positive-Theta or unrestricted PP bound.
-/

namespace ImbalancedChen.P2GammaRetainedSameRhoMother
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaUpperLowRankConsumer P2OriginalGammaDivisorNorm
open P2GammaCompleteProductTrimPayment P2GammaChosenLogGridBudget
open P2GammaJointRetainedReduction P2GammaRetainedSameRhoRows
open P5OriginalU5CausalFinite (pairSupport)
open Wu2008DoubleSieve

private theorem re_sum {α : Type*} (S : Finset α) (f : α → ℂ) :
    (∑ a ∈ S,f a).re = ∑ a ∈ S,(f a).re := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [Finset.sum_insert,ha,Complex.add_re,ih]

private theorem re_real_mul (r : ℝ) (z : ℂ) : ((r : ℂ)*z).re = r*z.re := by
  simp [Complex.mul_re]

/-- Only nonempty words have a prime head; the nil lane is handled below. -/
def headWordKernel (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (H δ : ℝ) (K q : ℕ) : ℂ :=
  match cs with
  | [] => 0
  | c::ds => ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
      cartesianRow N t c ds H δ j l q

def headWordError (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (H δ : ℝ) (K : ℕ) : ℝ :=
  ∑ q ∈ Q,rho q*(headWordKernel N t cs H δ K q).re

/-- The unchanged, directly defined original smooth-trimmed empty source. -/
def emptyWordError (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T : ℝ) : ℝ :=
  if cs=[] then ∑ q ∈ Q,rho q*∑ x ∈ rootLabels N t [],
    smoothTrim T (product (t.1*t.2) x)*gammaKernel N q (product (t.1*t.2) x)
  else 0

def headPairError (N : ℕ) (t : ℕ × ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (H δ : ℝ) (K : ℕ) : ℝ :=
  (originalMotherOccurrences.map (fun cs => headWordError N t cs Q rho H δ K)).sum

def emptyPairError (N : ℕ) (t : ℕ × ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (T : ℝ) : ℝ :=
  (originalMotherOccurrences.map (fun cs => emptyWordError N t cs Q rho T)).sum

theorem retainedPairError_eq_head_add_empty (N : ℕ) (t : ℕ × ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ) :
    retainedPairError N t Q rho T H δ K =
      headPairError N t Q rho H δ K+emptyPairError N t Q rho T := by
  have hw (cs : List ℕ) :
      (∑ q ∈ Q,rho q*retainedWordKernel N t cs T H δ K q) =
        headWordError N t cs Q rho H δ K+emptyWordError N t cs Q rho T := by
    cases cs with
    | nil => simp [headWordError,headWordKernel,emptyWordError,retainedWordKernel]
    | cons c cs =>
        simp [headWordError,headWordKernel,emptyWordError,retainedWordKernel,cartesianRow]
  have hl (L : List (List ℕ)) :
      (L.map (fun cs => ∑ q ∈ Q,rho q*retainedWordKernel N t cs T H δ K q)).sum =
        (L.map (fun cs => headWordError N t cs Q rho H δ K)).sum+
        (L.map (fun cs => emptyWordError N t cs Q rho T)).sum := by
    induction L with
    | nil => simp
    | cons cs L ih =>
        simp only [List.map_cons,List.sum_cons,hw,ih]
        ring
  exact hl originalMotherOccurrences

/-- Scalar algebra only: each analytic row estimate is supplied below. -/
theorem headWordError_le_rows (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (H δ : ℝ) (K : ℕ) (E : ℝ)
    (hrow : ∀ j ∈ Finset.range K,∀ l ∈ Finset.range K,
      ‖∑ q ∈ Q,(rho q : ℂ)*cartesianRow N t c cs H δ j l q‖ ≤ E) :
    |headWordError N t (c::cs) Q rho H δ K| ≤ (K : ℝ)^2*E := by
  have hre : headWordError N t (c::cs) Q rho H δ K =
      (∑ q ∈ Q,(rho q : ℂ)*headWordKernel N t (c::cs) H δ K q).re := by
    simp only [re_sum,re_real_mul,headWordError]
  have hcomm :
      (∑ q ∈ Q,(rho q : ℂ)*headWordKernel N t (c::cs) H δ K q) =
      ∑ j ∈ Finset.range K,∑ l ∈ Finset.range K,
        ∑ q ∈ Q,(rho q : ℂ)*cartesianRow N t c cs H δ j l q := by
    simp only [headWordKernel,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
  rw [hre]
  calc
    _ ≤ ‖∑ q ∈ Q,(rho q : ℂ)*headWordKernel N t (c::cs) H δ K q‖ :=
      Complex.abs_re_le_norm _
    _ = ‖∑ j ∈ Finset.range K,∑ l ∈ Finset.range K,
        ∑ q ∈ Q,(rho q : ℂ)*cartesianRow N t c cs H δ j l q‖ := congrArg norm hcomm
    _ ≤ ∑ j ∈ Finset.range K,‖∑ l ∈ Finset.range K,
        ∑ q ∈ Q,(rho q : ℂ)*cartesianRow N t c cs H δ j l q‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range K,∑ l ∈ Finset.range K,
        ‖∑ q ∈ Q,(rho q : ℂ)*cartesianRow N t c cs H δ j l q‖ :=
      Finset.sum_le_sum (fun j hj => norm_sum_le _ _)
    _ ≤ ∑ j ∈ Finset.range K,∑ l ∈ Finset.range K,E :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun l hl => hrow j hj l hl))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

private theorem list_abs_sum_le {α : Type*} (L : List α) (f : α → ℝ) (E : ℝ)
    (h : ∀ a ∈ L,|f a| ≤ E) : |(L.map f).sum| ≤ (L.length : ℝ)*E := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have ha := h a (List.mem_cons_self a L)
      have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      exact (abs_add _ _).trans ((add_le_add ha ht).trans_eq (by ring))

/-- Complete chosen-grid and literal mother sum for the actual upper rho.
The local request is strengthened by EXACTLY the two-grid counting power;
head-profile norms were already paid inside the imported local supplier. -/
theorem exists_chosen_headPair_same_rho (A B : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk : kappa ≤ 1/100) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ t ∈ pairSupport N,∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ),
      |headPairError N t Q (upperRho N nu epsilon retain cap)
        (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N) (gridLength B N)| ≤
          C*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let D := 2*(B+1)
  obtain ⟨C,hC,hrows⟩ := exists_chosen_signed_rows (A+D) B hB kappa hk0 hk
  let L := originalMotherOccurrences
  refine ⟨9*(L.length : ℝ)*C+1,by positivity,?_⟩
  filter_upwards [hrows,eventually_one_le_nat_log] with N hrow hlog
  intro t ht nu epsilon hnu hnu1 heps heps1 retain cap Q
  let E := C*(N : ℝ)/(Real.log (N : ℝ))^(A+D)
  have hlogp : 0 < Real.log (N : ℝ) := by linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hw : ∀ cs ∈ L,
      |headWordError N t cs Q (upperRho N nu epsilon retain cap)
        (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N) (gridLength B N)| ≤
          (gridLength B N : ℝ)^2*E := by
    intro cs hcs
    cases cs with
    | nil => simp only [headWordError,headWordKernel,Complex.zero_re,mul_zero,
        Finset.sum_const_zero,abs_zero]; positivity
    | cons c cs =>
        obtain ⟨i,hi,hcs⟩ := List.mem_flatMap.mp hcs
        exact headWordError_le_rows N t c cs Q _ _ _ _ E
          (fun j hj l hl => hrow t ht i hi c cs hcs j l nu epsilon
            hnu hnu1 heps heps1 retain cap Q)
  have hsum := list_abs_sum_le L
    (fun cs => headWordError N t cs Q (upperRho N nu epsilon retain cap)
      (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N) (gridLength B N))
    ((gridLength B N : ℝ)^2*E) hw
  have hcount : (gridLength B N : ℝ)^2 ≤ 9*(Real.log (N : ℝ))^D := by
    simpa only [Finset.card_product,Finset.card_range,Nat.cast_mul,pow_two,D] using
      (chosen_chart_count_le (B:=B) hlog)
  calc
    _ ≤ (L.length : ℝ)*((gridLength B N : ℝ)^2*E) := hsum
    _ ≤ (L.length : ℝ)*(9*(Real.log (N : ℝ))^D*E) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcount hE) (Nat.cast_nonneg _)
    _ = (9*(L.length : ℝ)*C)*(N : ℝ)/(Real.log (N : ℝ))^A := by
      dsimp [E]
      rw [pow_add]
      field_simp [hlogp.ne'] <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N)) (by positivity)

/-- Preserve the complete outside labels. No cardinality is suppressed. -/
def headJointError (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (H δ : ℝ) (K : ℕ) : ℝ :=
  ∑ t ∈ pairSupport N,sigma t*headPairError N t Q rho H δ K

def emptyJointError (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T : ℝ) : ℝ :=
  ∑ t ∈ pairSupport N,sigma t*emptyPairError N t Q rho T

def selectorMass (N : ℕ) (sigma : (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ t ∈ pairSupport N,|sigma t|

theorem jointRetained_eq_head_add_empty (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) :
    originalJointRetainedError N Q rho sigma T H δ K =
      headJointError N Q rho sigma H δ K+emptyJointError N Q rho sigma T := by
  simp only [originalJointRetainedError,retainedPairError_eq_head_add_empty,
    headJointError,emptyJointError,mul_add,Finset.sum_add_distrib]

/-- The real full-family cost is displayed. Selector mass is NOT Theta,
and no bound for it or a relative-Theta theorem is asserted. -/
theorem exists_chosen_headJoint_same_rho (A B : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk : kappa ≤ 1/100) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
        (sigma : (ℕ × ℕ) → ℝ),
      |headJointError N Q (upperRho N nu epsilon retain cap) sigma
        (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N) (gridLength B N)| ≤
        (C*(N : ℝ)/(Real.log (N : ℝ))^A)*selectorMass N sigma := by
  obtain ⟨C,hC,hpair⟩ := exists_chosen_headPair_same_rho A B hB kappa hk0 hk
  refine ⟨C,hC,?_⟩
  filter_upwards [hpair] with N hp
  intro nu epsilon hnu hnu1 heps heps1 retain cap Q sigma
  calc
    _ ≤ ∑ t ∈ pairSupport N,|sigma t*headPairError N t Q
        (upperRho N nu epsilon retain cap) (2*(N : ℝ)^(1-kappa))
        (boundaryLogMesh B N) (gridLength B N)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ pairSupport N,|sigma t|*(C*(N : ℝ)/(Real.log (N : ℝ))^A) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (hp t ht nu epsilon hnu hnu1 heps heps1 retain cap Q) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; dsimp [selectorMass]; ring

end
end ImbalancedChen.P2GammaRetainedSameRhoMother
