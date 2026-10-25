import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapCompiler
import ImbalancedChen.P5ZU1011StaticNativeTopFourExtension
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

ONE literal precision-dependent JOINT FULL16 STATIC native coefficient sigma_N(q).
The rational eta is fixed before N and every tuple. Every
mark is an actual nonfallback JOINT tuple and nonzero divisor coefficient from
its cell-static true selected-mask OR true W native row. Exact full-prefix
modulus pushforward preserves main/AP/centre and the actual count upper,
while tag0 retains its actual count. The top-four extension proves physical
injectivity across BOTH branches, hence sigma has genuine unit amplitude,
squarefree/deleted-target support and q<N^(153/256), with153/256<1.

Native rho density is NOT identified with the static H248 endpoint score.
Feedback-table soundness, PP/distribution, switched fallback payment and
the original analytic mean remain OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenJointNearCapModulusConvolution

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (ownerBox selectedPolicy boxPolicy_certificate)
open U1011OriginalSixteenJointNearCapCompiler
open U1011StaticNativeTopFourExtension P5U1011JointOverlap
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

abbrev Mark := Σ _ : Four, ℕ
def activeRows (n N : ℕ) (eta : ℚ) (t : Four) : Finset ℕ := (support n N eta t).filter (fun d => coefficient n N eta t d ≠ 0)
def marks (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : Finset Mark := (ordinaryTuples n N E).sigma (activeRows n N eta)
def modulus (m : Mark) : ℕ := fullPrefix m.1 * m.2
def weight (n N : ℕ) (eta : ℚ) (m : Mark) : ℝ := coefficient n N eta m.1 m.2
def modulusSupport (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : Finset ℕ := (marks n N eta E).image modulus
def fibre (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (q : ℕ) : Finset Mark := (marks n N eta E).filter (fun m => modulus m=q)
def sigma (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ := ∑ m ∈ fibre n N eta E q,weight n N eta m

private theorem mark_source {n N : ℕ} {eta : ℚ} {E : ℕ × ℕ → Prop} {m : Mark} (hm : m ∈ marks n N eta E) :
    m.1 ∈ ordinaryTuples n N E ∧ m.2 ∈ support n N eta m.1 ∧ weight n N eta m ≠ 0 := by
  obtain ⟨ht,hd⟩ := Finset.mem_sigma.mp hm
  obtain ⟨hd,hnz⟩ := Finset.mem_filter.mp hd
  exact ⟨ht,hd,hnz⟩

theorem modulus_injective_on_marks {n N : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) (E : ℕ×ℕ→Prop) :
    Set.InjOn modulus (marks n N eta E : Set Mark) := by
  intro m hm k hk heq
  have hmd := mark_source hm
  have hkd := mark_source hk
  have hmt := (Finset.mem_filter.mp hmd.1).1
  have hkt := (Finset.mem_filter.mp hkd.1).1
  have hmleg := compiled_legality hN heta hmd.1
  have hkleg := compiled_legality hN heta hkd.1
  have hmsmall := actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ hmd.2.1
  have hksmall := actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ hkd.2.1
  have hparts := actual_native_tuple_divisor_unique hmt hkt
    hmsmall hksmall hmleg.2.2.1 hkleg.2.2.1 heq
  exact Sigma.ext hparts.1 (heq_of_eq hparts.2)

theorem mark_arithmetic {n N : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop} {m : Mark}
    (hm : m∈marks n N eta E) : 0<modulus m ∧ Squarefree (modulus m) ∧ Nat.Coprime (modulus m) N ∧ |weight n N eta m|≤1 := by
  have hmd := mark_source hm
  have hsource := (Finset.mem_filter.mp hmd.1).1
  have hjoint := hsource
  have hleg := compiled_legality hN heta hmd.1
  have hsfD := actualSmallRosserSupport_squarefree _ _ _ hmd.2.1
  have hcopD := actualSmallRosserSupport_coprime_target _ _ _ hmd.2.1
  have hcopB := subproduct_coprime_target hjoint Finset.univ
  have hposB : 0<fullPrefix m.1 := by rw [fullPrefix_eq_multiplier]; exact joint_multiplier_pos hjoint
  have hposD : 0<m.2 := Nat.pos_of_ne_zero hsfD.ne_zero
  have hZ : Z n N eta m.1≤(slots m.1 3:ℝ) := by simpa only [slots,Matrix.cons_val_three] using hleg.2.2.1
  have hdvd : m.2∣sieveProduct N (Nat.ceil (Z n N eta m.1)) := by
    have h := (Nat.mem_divisors.mp hmd.2.1).1
    rwa [currentChen_actualSmallPrimeProduct_eq_sieveProduct N _ _ (Nat.le_ceil _)] at h
  have hcop := chenQuotient_allowed_coprime (fullPrefix_coprime_lowered_sieve hjoint hZ) hdvd
  refine ⟨mul_pos hposB hposD,?_,Nat.coprime_mul_iff_left.mpr ⟨hcopB,hcopD⟩,?_⟩
  · exact (Nat.squarefree_mul hcop).mpr ⟨U1011OriginalFifteenTopFourUniqueness.fullPrefix_squarefree hjoint,hsfD⟩
  · exact actualSmallRosserPlus_abs_le_one _ _ _ _ _

theorem fibre_card_le_one {n N : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) (E : ℕ×ℕ→Prop) (q : ℕ) : (fibre n N eta E q).card≤1 := by
  apply Finset.card_le_one.mpr
  intro m hm k hk
  obtain ⟨hm,hqM⟩ := Finset.mem_filter.mp hm
  obtain ⟨hk,hqK⟩ := Finset.mem_filter.mp hk
  exact modulus_injective_on_marks hN heta E hm hk (hqM.trans hqK.symm)

theorem sigma_abs_le_one {n N : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) (E : ℕ×ℕ→Prop) (q : ℕ) : |sigma n N eta E q|≤1 := by
  have hcard : ((fibre n N eta E q).card:ℝ)≤1 := by exact_mod_cast fibre_card_le_one hN heta E q
  unfold sigma
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ m∈fibre n N eta E q,|weight n N eta m|)≤∑ _m∈fibre n N eta E q,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact (mark_arithmetic hN heta (Finset.mem_filter.mp hm).1).2.2.2
    _ = ((fibre n N eta E q).card:ℝ) := by simp
    _ ≤ 1 := hcard

/-- The coefficient at an active physical modulus is literally the SAME
native divisor coefficient, including its selected cell and policy. -/
theorem sigma_eq_native_coefficient {n N : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop}
    {m : Mark} (hm : m∈marks n N eta E) : sigma n N eta E (modulus m)=coefficient n N eta m.1 m.2 := by
  have hf : fibre n N eta E (modulus m)={m} := by
    ext k
    constructor
    · intro hk
      obtain ⟨hk,hq⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_singleton.mpr (modulus_injective_on_marks hN heta E hk hm hq)
    · intro hk
      have heq := Finset.mem_singleton.mp hk
      subst k
      exact Finset.mem_filter.mpr ⟨hm,rfl⟩
  simp only [sigma,hf,Finset.sum_singleton,weight]

theorem exact_pushforward (n N : ℕ) (eta : ℚ) (E : ℕ×ℕ→Prop) (F : ℕ→ℝ) :
    (∑ t∈ordinaryTuples n N E,∑ d∈support n N eta t,coefficient n N eta t d*F (fullPrefix t*d))=
      ∑ q∈modulusSupport n N eta E,sigma n N eta E q*F q := by
  have hmarks : (∑ t∈ordinaryTuples n N E,∑ d∈support n N eta t,coefficient n N eta t d*F (fullPrefix t*d))=
      ∑ m∈marks n N eta E,weight n N eta m*F (modulus m) := by
    rw [marks,Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro t ht
    unfold activeRows
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hz : coefficient n N eta t d=0 <;> simp [weight,modulus,hz]
  rw [hmarks]
  have hf := Finset.sum_fiberwise_of_maps_to (s:=marks n N eta E) (t:=modulusSupport n N eta E) (g:=modulus)
    (fun m hm=>Finset.mem_image_of_mem modulus hm) (fun m=>weight n N eta m*F (modulus m))
  rw [←hf]
  apply Finset.sum_congr rfl
  intro q hq
  unfold sigma fibre
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [(Finset.mem_filter.mp hm).2]

theorem AP_pushforward (n N : ℕ) (eta : ℚ) (E : ℕ×ℕ→Prop) :
    (∑ t∈ordinaryTuples n N E,signedAP n N eta t)=∑ q∈modulusSupport n N eta E,
      sigma n N eta E q*chenQuotientPrimeAPError N (trueLogarithmicIntegral N) q := exact_pushforward n N eta E _
theorem centre_pushforward (n N : ℕ) (eta : ℚ) (E : ℕ×ℕ→Prop) :
    (∑ t∈ordinaryTuples n N E,signedCentre n N eta t)=∑ q∈modulusSupport n N eta E,
      sigma n N eta E q*chenCentrePrimeAPCount N N q := exact_pushforward n N eta E _
theorem estimator_pushforward (n N : ℕ) (eta : ℚ) (E : ℕ×ℕ→Prop) :
    (∑ t∈ordinaryTuples n N E,estimator n N eta t)=∑ q∈modulusSupport n N eta E,
      sigma n N eta E q*(chenPrimeAPCount N N q-chenCentrePrimeAPCount N N q) := exact_pushforward n N eta E _

theorem main_pushforward {n N : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) (E : ℕ×ℕ→Prop) :
    (∑ t∈ordinaryTuples n N E,main n N eta t)=∑ q∈modulusSupport n N eta E,
      sigma n N eta E q*(trueLogarithmicIntegral N/(Nat.totient q:ℝ)) := by
  have hrows : (∑ t∈ordinaryTuples n N E,estimator n N eta t)=
      ∑ t∈ordinaryTuples n N E,main n N eta t+signedAP n N eta t-signedCentre n N eta t :=
    Finset.sum_congr rfl (fun t ht=>compiled_estimator_identity hN heta ht)
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,estimator_pushforward,AP_pushforward,centre_pushforward] at hrows
  have hs : (∑ q∈modulusSupport n N eta E,sigma n N eta E q*(chenPrimeAPCount N N q-chenCentrePrimeAPCount N N q))=
      (∑ q∈modulusSupport n N eta E,sigma n N eta E q*(trueLogarithmicIntegral N/(Nat.totient q:ℝ)))+
      (∑ q∈modulusSupport n N eta E,sigma n N eta E q*chenQuotientPrimeAPError N (trueLogarithmicIntegral N) q)-
      ∑ q∈modulusSupport n N eta E,sigma n N eta E q*chenCentrePrimeAPCount N N q := by
    rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    unfold chenQuotientPrimeAPError
    ring
  linarith

/-- Unmarked original count upper with ONE physical coefficient. The
static tag0 JOINT count is retained exactly and is not assumed bounded by its score. -/
theorem original_count_upper_sigma {n N : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) (E : ℕ×ℕ→Prop) :
    currentChenUpsilon10 N+currentChenUpsilon11 N E≤(∑ t∈fallbackTuples n N E,U11Adaptive.weight N t)+
      ∑ q∈modulusSupport n N eta E,sigma n N eta E q*(chenPrimeAPCount N N q-chenCentrePrimeAPCount N N q) := by
  have h := original_joint_source_upper hN E heta
  have hrows : (∑ t∈ordinaryTuples n N E,main n N eta t+signedAP n N eta t-signedCentre n N eta t)=
      ∑ t∈ordinaryTuples n N E,estimator n N eta t :=
    Finset.sum_congr rfl (fun t ht=>(compiled_estimator_identity hN heta ht).symm)
  rw [hrows,estimator_pushforward] at h
  exact h

/-- The actual joint count, reciprocal-totient main, signed AP discrepancy
and centre deletion all use ONE literal physical coefficient. -/
theorem original_count_upper_same_sigma {n N : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) (E : ℕ×ℕ→Prop) :
    currentChenUpsilon10 N+currentChenUpsilon11 N E≤
      (∑t∈fallbackTuples n N E,U11Adaptive.weight N t)+
      (∑q∈modulusSupport n N eta E,sigma n N eta E q*(trueLogarithmicIntegral N/(Nat.totient q:ℝ)))+
      (∑q∈modulusSupport n N eta E,sigma n N eta E q*chenQuotientPrimeAPError N (trueLogarithmicIntegral N) q)-
      ∑q∈modulusSupport n N eta E,sigma n N eta E q*chenCentrePrimeAPCount N N q := by
  have hu := original_joint_source_upper (n:=n) hN E heta
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,main_pushforward hN heta E,
    AP_pushforward n N eta E,centre_pushforward n N eta E] at hu
  linarith

private theorem cap_le_Lambda (p : Policy) (v : LogFour) (hv2 : 0≤v 2) : cap p v≤(153/256:ℝ) := by
  by_cases hp : p.val<15
  · unfold cap
    rw [if_pos hp]
    by_cases hs : selectedMass p v≤(25/128:ℝ)
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  · unfold cap
    rw [if_neg hp]
    linarith

theorem mark_modulus_cap {n N : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop} {m : Mark}
    (hm : m∈marks n N eta E) : (modulus m:ℝ)<(N:ℝ)^(153/256:ℝ) := by
  have hmd := mark_source hm
  have hsource := (Finset.mem_filter.mp hmd.1).1
  have htag := (Finset.mem_filter.mp hmd.1).2
  let B := ownerBox n N m.1
  let p := selectedPolicy n N m.1
  have hcert := (boxPolicy_certificate B htag).2
  have hvalid : B.Valid := gridBox_valid n _
  have hpositive : 0<B.lo 3 := gridBox_lower_positive n _ 3
  have hp2 : (0:ℝ)≤(B.lo 2:ℝ) := by exact_mod_cast (gridBox_lower_positive n (owner n (coordinates N m.1)) 2).le
  have hcorner := U1011OriginalSixteenStaticCellWinner.corner_mem_region B hvalid
  have hpar := U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p B eta hvalid hpositive hcert heta
  have hnuLower : (U1011OriginalSixteenNearCapBoxProfiles.nu p B eta:ℝ)<(capLower p B:ℝ) := by exact_mod_cast hpar.2.1
  have hnu : (U1011OriginalSixteenNearCapBoxProfiles.nu p B eta:ℝ)<(153/256:ℝ) :=
    hnuLower.trans_le ((cap_bounds p B hcorner).1.trans (cap_le_Lambda p _ hp2))
  have hdelta : (0:ℝ)<(U1011OriginalSixteenNearCapBoxProfiles.delta p B eta:ℝ) := by exact_mod_cast hpar.2.2.1
  have hgeom := owner_mem n (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hsource)
  have hcap := joint_row_active_full_modulus_cap hN hsource p B eta (cell_subset_closed_box n _ hgeom) hmd.2.2
  exact hcap.trans_le (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (Nat.le_of_lt hN)) (by linarith))

theorem theta_lt_one : (153/256:ℝ)<1 := by norm_num

theorem modulusSupport_profile {n N q : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop}
    (hq : q∈modulusSupport n N eta E) :
    0<q ∧ Squarefree q ∧ Nat.Coprime q N ∧ (q:ℝ)<(N:ℝ)^(153/256:ℝ) := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hq
  have ha := mark_arithmetic hN heta hm
  exact ⟨ha.1,ha.2.1,ha.2.2.1,mark_modulus_cap hN heta hm⟩

theorem sigma_zero_off_support {n N q : ℕ} {eta : ℚ} {E : ℕ×ℕ→Prop} (hq : q∉modulusSupport n N eta E) : sigma n N eta E q=0 := by
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨hm,hq'⟩ := Finset.mem_filter.mp hm
  exact (hq (Finset.mem_image.mpr ⟨m,hm,hq'⟩)).elim

/-- Actual near-cap JOINT FULL16 static sigma arithmetic profile: every assertion is
derived from native source ownership and factorization, never assumed. -/
theorem sigma_nonzero_profile {n N q : ℕ} {eta : ℚ} (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop} (hq : sigma n N eta E q≠0) :
    0<q ∧ Squarefree q ∧ Nat.Coprime q N ∧ |sigma n N eta E q|≤1 ∧ (q:ℝ)<(N:ℝ)^(153/256:ℝ) := by
  have hmem : q∈modulusSupport n N eta E := by
    by_contra hn
    exact hq (sigma_zero_off_support hn)
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hmem
  have hdata := mark_arithmetic hN heta hm
  exact ⟨hdata.1,hdata.2.1,hdata.2.2.1,sigma_abs_le_one hN heta E _,mark_modulus_cap hN heta hm⟩

end
end ImbalancedChen.P5Z.U1011OriginalSixteenJointNearCapModulusConvolution



