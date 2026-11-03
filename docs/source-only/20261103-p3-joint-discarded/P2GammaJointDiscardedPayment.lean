import ImbalancedChen.P2GammaJointLowProductPayment
import ImbalancedChen.P2GammaJointRemainingPayment

/-!
Source-only / UNCOMPILED / KERNEL-UNVERIFIED.
The original smooth-trim remainder and lower rejection are paid as ONE
actual nonnegative weight of height at most one. The exact whole outer
sum is then combined with the existing joint upper/order supplier.
The result is absolute logarithmic accuracy, NOT a relative-Theta PP
estimate. Physical common-Q membership and retained analytic PP remain.
-/

namespace ImbalancedChen.P2GammaJointDiscardedPayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2OriginalGammaUpperLowRankConsumer
open P2OriginalU5ExactNormalizedSource
open P2GammaCompleteProductTrimPayment P2GammaLowerRejectedPayment
open P2GammaOrderingStripPayment P2GammaJointLabels P2GammaJointUpperPayment
open P2GammaJointLowProductPayment P2GammaJointRemainingPayment
open P5OriginalU5CausalFinite (pairSupport)

/-- The actual low terms, not a difference-defined bound or licence. -/
def lowDiscardedWeight (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (T H δ : ℝ) (K : ℕ) (x : Label) : ℝ :=
  trimRemainder T (product (t.1*t.2) x)+wordLowerRejectedWeight N t cs T H δ K x

/-- 1-s+s*r stays in [0,1]. The original partial hat partition supplies
0<=r<=1; no grid-cardinality loss or double counting of the trim. -/
theorem lowDiscardedWeight_range (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (T H δ : ℝ) (K : ℕ) (x : Label) :
    0 ≤ lowDiscardedWeight N t cs T H δ K x ∧
      lowDiscardedWeight N t cs T H δ K x ≤ 1 := by
  have hr := rawLowerRejectedWeight_range N t H δ K x
  have hs0 : 0 ≤ smoothTrim T (product (t.1*t.2) x) := Real.smoothTransition.nonneg _
  have hs1 : smoothTrim T (product (t.1*t.2) x) ≤ 1 := Real.smoothTransition.le_one _
  by_cases hcs : cs=[]
  · simpa only [lowDiscardedWeight,wordLowerRejectedWeight,if_pos hcs,add_zero] using
      trimRemainder_range T (product (t.1*t.2) x)
  · simp only [lowDiscardedWeight,wordLowerRejectedWeight,if_neg hcs,trimRemainder]
    have hp0 := mul_nonneg hs0 hr.1
    have hp1 := mul_le_mul_of_nonneg_left hr.2 hs0
    constructor <;> nlinarith

theorem lowDiscardedWeight_eq_zero_above (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    {T H δ : ℝ} (hT : 0 < T) (hH : 2*T ≤ H) (hδ : 0 ≤ δ)
    (K : ℕ) (x : Label) (hx : enlargedCut H δ < product (t.1*t.2) x) :
    lowDiscardedWeight N t cs T H δ K x=0 := by
  have hH0 : 0 ≤ H := by linarith
  have he : 1 ≤ Real.exp (4*δ) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : (0 : ℝ) ≤ 4*δ)
  have hscale : 2*T ≤ (product (t.1*t.2) x : ℝ) := by
    calc
      _ ≤ H := hH
      _ = H*1 := by ring
      _ ≤ H*Real.exp (4*δ) := mul_le_mul_of_nonneg_left he hH0
      _ ≤ (enlargedCut H δ : ℝ) := Nat.le_ceil _
      _ ≤ _ := by exact_mod_cast hx.le
  rw [lowDiscardedWeight,trimRemainder_eq_zero hT hscale,
    wordLowerRejectedWeight_eq_zero_above N t cs T H δ K x hx,zero_add]

def jointLowWordError (N : ℕ) (cs : List ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  jointError N cs Q rho (fun z => sigma z.1*lowDiscardedWeight N z.1 cs T H δ K z.2)

theorem jointLowWordError_eq_outer (N : ℕ) (cs : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ)
    (T H δ : ℝ) (K : ℕ) :
    jointLowWordError N cs Q rho sigma T H δ K =
      ∑ t ∈ pairSupport N,sigma t*wordError N t cs Q rho
        (lowDiscardedWeight N t cs T H δ K) :=
  jointError_eq_outer_wordError N cs Q rho sigma _

/-- The enlarged INTEGER cut and its sublinear bound are supplied by
Q16. All word, grid, selector and signed-modulus data follow one N. -/
theorem eventually_jointLowWordError (J A : ℕ) (kappa C0 delta0 : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (hC0 : 0 < C0)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (cs : List ℕ), (cs.length+3)^2-1 ≤ J →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ)
        (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ 1) →
      0 < T → 2*T ≤ H → H ≤ C0*(N : ℝ)^(1-kappa) → 0 ≤ δ → δ ≤ delta0 →
      |jointLowWordError N cs Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let C := C0*Real.exp (4*delta0)+1
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [eventually_joint_low_product J A kappa C hkappa hC eta heta,
    eventually_enlargedCut_bounds kappa C0 delta0 hkappa hkappa1 hC0]
    with N hpay hcut
  intro cs hJ Q rho sigma T H δ K hQ hrho hsigma hT hH hHC hδ hδ0
  have hHp : 0 < H := by linarith
  obtain ⟨hYN,hY⟩ := hcut H δ hHp.le hHC hδ0
  have hYpos : 1 ≤ enlargedCut H δ := by
    have hp : (0 : ℝ) < (enlargedCut H δ : ℝ) :=
      (mul_pos hHp (Real.exp_pos _)).trans_le (Nat.le_ceil _)
    exact_mod_cast hp
  apply hpay cs hJ (enlargedCut H δ) hYpos hYN.le hY Q rho _ hQ hrho
  · intro z hz
    have ht := ((mem_jointLabels N cs z).mp hz).1
    have hs := hsigma z.1 ht
    have hw := lowDiscardedWeight_range N z.1 cs T H δ K z.2
    rw [abs_of_nonneg (mul_nonneg hs.1 hw.1)]
    exact (mul_le_mul hs.2 hw.2 hw.1 zero_le_one).trans_eq (by norm_num)
  · intro z hz hlarge
    rw [lowDiscardedWeight_eq_zero_above N z.1 cs hT hH hδ K z.2 hlarge,mul_zero]

/-- The complete original pair/mother source. Occurrences are a LIST. -/
def originalJointLowError (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  (originalMotherOccurrences.map
    (fun cs => jointLowWordError N cs Q rho sigma T H δ K)).sum

theorem originalJointLowError_eq_outer (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) :
    originalJointLowError N Q rho sigma T H δ K =
      ∑ t ∈ pairSupport N,sigma t*
        (listTrimError originalMotherOccurrences N t Q rho T+
          listLowerRejectedError originalMotherOccurrences N t Q rho T H δ K) := by
  have hword (t : ℕ × ℕ) (cs : List ℕ) :
      wordError N t cs Q rho (lowDiscardedWeight N t cs T H δ K) =
        wordError N t cs Q rho (fun x => trimRemainder T (product (t.1*t.2) x))+
          wordLowerRejectedError N t cs Q rho T H δ K := by
    simp only [wordError,lowDiscardedWeight,wordLowerRejectedError,
      add_mul,Finset.sum_add_distrib,mul_add]
  have hlist (L : List (List ℕ)) :
      (L.map (fun cs => jointLowWordError N cs Q rho sigma T H δ K)).sum =
        ∑ t ∈ pairSupport N,sigma t*
          (listTrimError L N t Q rho T+listLowerRejectedError L N t Q rho T H δ K) := by
    induction L with
    | nil => simp [listTrimError,listLowerRejectedError]
    | cons cs L ih =>
        rw [List.map_cons,List.sum_cons,ih,jointLowWordError_eq_outer]
        simp only [hword,listTrimError,listLowerRejectedError,List.map_cons,List.sum_cons]
        simp only [mul_add,Finset.sum_add_distrib]
        ring
  exact hlist originalMotherOccurrences

/-- Identification with the existing gammaDiscrepancy and the literal
originalLowerRejectedKernel, at each SAME modulus and signed rho. -/
theorem originalJointLowError_eq_original (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) :
    originalJointLowError N Q rho sigma T H δ K =
      ∑ t ∈ pairSupport N,sigma t*
        ((∑ q ∈ Q,rho q*(gammaDiscrepancy N t q-
          sourceTest N t (fun m => smoothTrim T m*gammaKernel N q m)))+
        ∑ q ∈ Q,rho q*originalLowerRejectedKernel N t T H δ K q) := by
  rw [originalJointLowError_eq_outer]
  apply Finset.sum_congr rfl
  intro t ht
  have hsplit (q : ℕ) : gammaDiscrepancy N t q-
      sourceTest N t (fun m => smoothTrim T m*gammaKernel N q m) =
        sourceTest N t (fun m => trimRemainder T m*gammaKernel N q m) := by
    rw [gammaDiscrepancy_eq_trim_add_remainder N t q T]
    ring
  simp_rw [hsplit]
  rw [gamma_trim_sum_eq_literal_list,originalLowerRejected_sum_eq_literal_list]

theorem eventually_originalJointLowError (A : ℕ) (kappa C0 delta0 : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (hC0 : 0 < C0)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ → ℝ)
      (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ 1) →
      0 < T → 2*T ≤ H → H ≤ C0*(N : ℝ)^(1-kappa) → 0 ≤ δ → δ ≤ delta0 →
      |originalJointLowError N Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let L := originalMotherOccurrences
  let J := jointListMomentOrder L
  let eta0 := eta/((L.length : ℝ)+1)
  have heta0 : 0 < eta0 := by dsimp [eta0]; positivity
  filter_upwards [eventually_jointLowWordError J A kappa C0 delta0 hkappa hkappa1 hC0 eta0 heta0,
    eventually_one_le_nat_log] with N hword hlog
  intro Q rho sigma T H δ K hQ hrho hsigma hT hH hHC hδ hδ0
  let f := fun cs => jointLowWordError N cs Q rho sigma T H δ K
  let E := eta0*(N : ℝ)/(Real.log (N : ℝ))^A
  have heach : ∀ cs ∈ L,|f cs| ≤ E := by
    intro cs hcs
    exact hword cs (le_jointListMomentOrder hcs) Q rho sigma T H δ K
      hQ hrho hsigma hT hH hHC hδ hδ0
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

/-- Sum of the three existing discarded mechanisms: original low trim,
lower-first rejection, and the original remaining upper/order rejection.
This is not defined by subtracting a desired main term. -/
def originalJointDiscardedError (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  originalJointLowError N Q rho sigma T H δ K+
    originalJointRemainingError N Q rho sigma T H δ K

theorem originalJointDiscardedError_eq_original (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) :
    originalJointDiscardedError N Q rho sigma T H δ K =
      ∑ t ∈ pairSupport N,sigma t*
        ((∑ q ∈ Q,rho q*(gammaDiscrepancy N t q-
          sourceTest N t (fun m => smoothTrim T m*gammaKernel N q m)))+
        (∑ q ∈ Q,rho q*originalLowerRejectedKernel N t T H δ K q)+
          originalRemainingRejectedError N t Q rho T H δ K) := by
  simp only [originalJointDiscardedError,originalJointLowError_eq_original,
    originalJointRemainingError,mul_add,Finset.sum_add_distrib]

/-- One common mesh, threshold, original occurrence list and rho pay
ALL discarded terms after the complete outside pair sum. Retained PP
and positive-Theta normalization are deliberately not asserted. -/
theorem eventually_originalJointDiscardedError (A : ℕ) (kappa C0 delta0 : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (hC0 : 0 < C0)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ → ℝ)
      (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ 1) →
      0 < T → 2*T ≤ H → H ≤ C0*(N : ℝ)^(1-kappa) → 0 < δ → δ ≤ delta0 →
      δ ≤ boundaryLogMesh (orderMeshExponent (jointListMomentOrder originalMotherOccurrences) A) N →
      |originalJointDiscardedError N Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_originalJointLowError A kappa C0 delta0 hkappa hkappa1 hC0
      (eta/2) (half_pos heta),
    eventually_originalJointRemainingError A (eta/2) (half_pos heta)] with N hlow hremaining
  intro Q rho sigma T H δ K hQ hrho hsigma hT hH hHC hδ hδ0 hmesh
  exact (abs_add _ _).trans ((add_le_add
    (hlow Q rho sigma T H δ K hQ hrho hsigma hT hH hHC hδ.le hδ0)
    (hremaining Q rho sigma T H δ K hQ hrho hsigma hδ hmesh)).trans_eq (by ring))

theorem originalJointDiscardedError_smul (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ c : ℝ) (K : ℕ) :
    originalJointDiscardedError N Q rho (fun t => c*sigma t) T H δ K =
      c*originalJointDiscardedError N Q rho sigma T H δ K := by
  rw [originalJointDiscardedError_eq_original,originalJointDiscardedError_eq_original,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem eventually_originalJointDiscardedError_height (C : ℝ) (hC : 0 < C)
    (A : ℕ) (kappa C0 delta0 : ℝ) (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (hC0 : 0 < C0) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ → ℝ)
      (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ C) →
      0 < T → 2*T ≤ H → H ≤ C0*(N : ℝ)^(1-kappa) → 0 < δ → δ ≤ delta0 →
      δ ≤ boundaryLogMesh (orderMeshExponent (jointListMomentOrder originalMotherOccurrences) A) N →
      |originalJointDiscardedError N Q rho sigma T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_originalJointDiscardedError A kappa C0 delta0 hkappa hkappa1 hC0
    (eta/C) (div_pos heta hC)] with N hN
  intro Q rho sigma T H δ K hQ hrho hsigma hT hH hHC hδ hδ0 hmesh
  have hs : ∀ t ∈ pairSupport N,0 ≤ sigma t/C ∧ sigma t/C ≤ 1 := by
    intro t ht
    exact ⟨div_nonneg (hsigma t ht).1 hC.le,(div_le_one hC).mpr (hsigma t ht).2⟩
  have h := hN Q rho (fun t => sigma t/C) T H δ K hQ hrho hs hT hH hHC hδ hδ0 hmesh
  have heq : originalJointDiscardedError N Q rho sigma T H δ K =
      C*originalJointDiscardedError N Q rho (fun t => sigma t/C) T H δ K := by
    rw [← originalJointDiscardedError_smul]
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
end ImbalancedChen.P2GammaJointDiscardedPayment
