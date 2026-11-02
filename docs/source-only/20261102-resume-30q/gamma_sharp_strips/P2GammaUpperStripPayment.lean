import ImbalancedChen.P2GammaLowerRejectedPayment
import ImbalancedChen.BoundaryArbitraryLog

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual Gamma upper-product strips, after the full bounded signed modulus
sum. The two moment suppliers are the original complete-product fibre
second moment and the native divisor second moment on the SHORT interval
of positive differences N-m. No pointwise N^epsilon divisor bound, BV
estimate, rejected-mass estimate, or shifted-correlation estimate is a
premise. The aggregate grid rejection is paid once; there is no K^2 loss.

The strict source ceiling m<N is essential. This file does not estimate
the remaining head-order strip or assert full Gamma distribution.
-/

namespace ImbalancedChen.P2GammaUpperStripPayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2OriginalGammaUpperLowRankConsumer
open P2GammaCompleteProductTrimPayment P2GammaRetainedInteriorGeometry
open P2GammaSmoothLogGrid
open P2GammaLowerRejectedPayment
open P5OriginalU5CausalFinite (pairSupport)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def upperProducts (N : ℕ) (Y : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter (fun m => m < N ∧ ((N-m : ℕ) : ℝ) ≤ Y)

theorem upperProducts_difference_maps {N : ℕ} {Y : ℝ} (hY : 0 ≤ Y) :
    ∀ m ∈ upperProducts N Y, N-m ∈ Finset.Ioc 0 ⌊Y⌋₊ := by
  intro m hm
  obtain ⟨_,hmN,hmY⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_Ioc.mpr ⟨Nat.sub_pos_of_lt hmN,
    (Nat.le_floor_iff hY).mpr hmY⟩

theorem upperProducts_difference_inj (N : ℕ) (Y : ℝ) :
    Set.InjOn (fun m => N-m) (upperProducts N Y) := by
  intro m hm n hn heq
  have hmN := (Finset.mem_filter.mp hm).2.1
  have hnN := (Finset.mem_filter.mp hn).2.1
  omega

theorem upperProducts_card_le {N : ℕ} {Y : ℝ} (hY : 0 ≤ Y) :
    ((upperProducts N Y).card : ℝ) ≤ Y := by
  have hc : (upperProducts N Y).card ≤ (Finset.Ioc 0 ⌊Y⌋₊).card :=
    Finset.card_le_card_of_injOn (fun m => N-m)
      (upperProducts_difference_maps hY) (upperProducts_difference_inj N Y)
  have hc' : ((upperProducts N Y).card : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by
    exact_mod_cast (by simpa using hc : (upperProducts N Y).card ≤ ⌊Y⌋₊)
  exact hc'.trans (Nat.floor_le hY)

/-- The short-difference moment is supplied by the native unshifted
divisor mean after an actual injection. There is no tau(0) term. -/
theorem upperProducts_difference_square_sum_le {N : ℕ} {Y : ℝ}
    (hY : 1 ≤ Y) (hYN : Y ≤ N) :
    (∑ m ∈ upperProducts N Y, ((N-m).divisors.card : ℝ)^2) ≤
      Y * (1+Real.log (N : ℝ))^3 := by
  let S := upperProducts N Y
  let T := S.image (fun m => N-m)
  have hT : T ⊆ Finset.Ioc 0 ⌊Y⌋₊ := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact upperProducts_difference_maps (by linarith : 0 ≤ Y) m hm
  have hmoment : (∑ n ∈ T, (n.divisors.card : ℝ)^2) ≤
      Y * (1+Real.log Y)^3 := by
    apply sum_alpha_sq_le_fouvryTau (k := 2) (by norm_num) hY T hT
      (fun n => (n.divisors.card : ℝ))
    intro n hn
    simp only [abs_of_nonneg (Nat.cast_nonneg _),fouvryTau_two]
  have hlog : 1+Real.log Y ≤ 1+Real.log (N : ℝ) :=
    add_le_add_left (Real.log_le_log (by linarith) hYN) 1
  calc
    _ = ∑ n ∈ T, (n.divisors.card : ℝ)^2 :=
      (Finset.sum_image (upperProducts_difference_inj N Y)).symm
    _ ≤ Y * (1+Real.log Y)^3 := hmoment
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg hY]) hlog 3)
      (by linarith)

theorem root_product_positive {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {cs : List ℕ} {x : Label}
    (hx : x ∈ rootLabels N t cs) : 0 < product (t.1*t.2) x := by
  have hd := rootLabels_data hx
  exact Nat.mul_pos (Nat.mul_pos
    (P2OriginalU5SmallPartnerRootPayment.pair_product_pos ht)
    (word_prod_pos hd.1)) hd.2.1

/-- Literal labels, the same signed rho, and the exact q-coprime mean
are retained before grouping the nonnegative majorant by complete product. -/
theorem wordError_upper_majorant {N : ℕ} (hN : 1 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (cs : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (w : Label → ℝ) (Y : ℝ)
    (hQ : Q ⊆ Finset.Icc 1 N) (hrho : ∀ q ∈ Q, |rho q| ≤ 1)
    (hw : ∀ x ∈ rootLabels N t cs, |w x| ≤ 1)
    (hzero : ∀ x ∈ rootLabels N t cs,
      Y < ((N-product (t.1*t.2) x : ℕ) : ℝ) → w x=0) :
    |wordError N t cs Q rho w| ≤
      ∑ m ∈ upperProducts N Y, ((rootProductFiber N t cs m).card : ℝ) *
        (((N-m).divisors.card : ℝ)+4*(1+Real.log (N : ℝ))) := by
  let B : ℕ → ℝ := fun m =>
    ((N-m).divisors.card : ℝ)+4*(1+Real.log (N : ℝ))
  let F : ℕ → ℝ := fun m =>
    if ((N-m : ℕ) : ℝ) ≤ Y then B m else 0
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB (m : ℕ) : 0 ≤ B m := by
    dsimp [B]
    have := Real.log_nonneg hNreal
    positivity
  have hF (m : ℕ) : 0 ≤ F m := by dsimp [F]; split_ifs <;> positivity
  have heq : wordError N t cs Q rho w =
      ∑ x ∈ rootLabels N t cs, w x *
        ∑ q ∈ Q, rho q * gammaKernel N q (product (t.1*t.2) x) := by
    simp only [wordError,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hlabels : |wordError N t cs Q rho w| ≤
      ∑ x ∈ rootLabels N t cs, F (product (t.1*t.2) x) := by
    rw [heq]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    by_cases hband : ((N-product (t.1*t.2) x : ℕ) : ℝ) ≤ Y
    · have hk := kernel_absolute_modulus_sum_le (rootLabels_data hx).2.2.2
        Q rho hQ hrho
      rw [max_eq_right hNreal] at hk
      simp only [F,if_pos hband]
      change |w x * _| ≤ B (product (t.1*t.2) x)
      rw [abs_mul]
      exact (mul_le_mul (hw x hx) (Finset.abs_sum_le_sum_abs _ _)
        (abs_nonneg _) zero_le_one).trans (by simpa only [one_mul] using hk)
    · simp only [F,if_neg hband,hzero x hx (lt_of_not_ge hband),zero_mul,abs_zero]
  have hproducts : rootProducts N t cs ⊆ Finset.Ioc 0 N := by
    intro m hm
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_Ioc.mpr ⟨root_product_positive ht hx,(rootLabels_data hx).2.2.2.le⟩
  calc
    _ ≤ ∑ x ∈ rootLabels N t cs, F (product (t.1*t.2) x) := hlabels
    _ = ∑ m ∈ rootProducts N t cs, ((rootProductFiber N t cs m).card : ℝ)*F m :=
      root_word_real_test_eq_grouped N t cs F
    _ ≤ ∑ m ∈ Finset.Ioc 0 N, ((rootProductFiber N t cs m).card : ℝ)*F m :=
      Finset.sum_le_sum_of_subset_of_nonneg hproducts
        (fun m hm hnot => mul_nonneg (Nat.cast_nonneg _) (hF m))
    _ = ∑ m ∈ upperProducts N Y, ((rootProductFiber N t cs m).card : ℝ)*B m := by
      rw [upperProducts,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmN : m < N
      · by_cases hmY : ((N-m : ℕ) : ℝ) ≤ Y <;> simp [F,hmN,hmY]
      · have hempty : rootProductFiber N t cs m = ∅ := by
          apply Finset.eq_empty_iff_forall_not_mem.mpr
          intro x hx
          obtain ⟨hx,hxm⟩ := Finset.mem_filter.mp hx
          exact hmN (hxm ▸ (rootLabels_data hx).2.2.2)
        simp [hempty,hmN]

theorem young_scaled (a b u : ℝ) (hu : 0 < u) :
    a*b ≤ u*a^2+b^2/u := by
  calc
    a*b ≤ (u^2*a^2+b^2)/u :=
      (le_div_iff₀ hu).mpr (by nlinarith [sq_nonneg (u*a-b),sq_nonneg (u*a),sq_nonneg b])
    _ = _ := by field_simp [hu.ne']; ring

/-- Genuine finite upper-strip payment. J is only a fixed divisor-moment
exponent; every original word of the indicated bounded length is covered.
The second term is proportional to the short difference length Y. -/
theorem wordError_upper_strip_le {N : ℕ} (hN : 1 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (cs : List ℕ) (J : ℕ)
    (hJ : (cs.length+2)^2-1 ≤ J) {Y u : ℝ}
    (hY : 1 ≤ Y) (hYN : Y ≤ N) (hu : 0 < u)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (w : Label → ℝ)
    (hQ : Q ⊆ Finset.Icc 1 N) (hrho : ∀ q ∈ Q, |rho q| ≤ 1)
    (hw : ∀ x ∈ rootLabels N t cs, |w x| ≤ 1)
    (hzero : ∀ x ∈ rootLabels N t cs,
      Y < ((N-product (t.1*t.2) x : ℕ) : ℝ) → w x=0) :
    |wordError N t cs Q rho w| ≤
      u*(N : ℝ)*(1+Real.log (N : ℝ))^J +
        34*Y*(1+Real.log (N : ℝ))^3/u := by
  let S := upperProducts N Y
  let L := 1+Real.log (N : ℝ)
  let a := fun m => ((rootProductFiber N t cs m).card : ℝ)
  let b := fun m => ((N-m).divisors.card : ℝ)+4*L
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hNreal]
  have hS : S ⊆ Finset.Ioc 0 ⌊(N : ℝ)⌋₊ := by
    simpa only [Nat.floor_natCast] using (Finset.filter_subset
      (fun m => m < N ∧ ((N-m : ℕ) : ℝ) ≤ Y) (Finset.Ioc 0 N))
  have ha : (∑ m ∈ S, a m^2) ≤ (N : ℝ)*L^J :=
    (original_Gamma_word_square_sum_le ht cs hNreal S hS).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hJ) (Nat.cast_nonneg N))
  have htau : (∑ m ∈ S, ((N-m).divisors.card : ℝ)^2) ≤ Y*L^3 :=
    upperProducts_difference_square_sum_le hY hYN
  have hc : (S.card : ℝ) ≤ Y := upperProducts_card_le (by linarith)
  have hL2 : L^2 ≤ L^3 := pow_le_pow_right₀ hL (by omega)
  have hb : (∑ m ∈ S, b m^2) ≤ 34*Y*L^3 := by
    calc
      _ ≤ ∑ m ∈ S, 2*((N-m).divisors.card : ℝ)^2+32*L^2 := by
        apply Finset.sum_le_sum
        intro m hm
        dsimp [b]
        nlinarith [sq_nonneg (((N-m).divisors.card : ℝ)-4*L)]
      _ = 2*(∑ m ∈ S, ((N-m).divisors.card : ℝ)^2)+32*L^2*(S.card : ℝ) := by
        rw [Finset.sum_add_distrib,Finset.mul_sum]
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ 2*(Y*L^3)+32*L^2*Y := by gcongr
      _ ≤ 34*Y*L^3 := by nlinarith [mul_le_mul_of_nonneg_right hL2 (by linarith : 0 ≤ Y)]
  calc
    _ ≤ ∑ m ∈ S, a m*b m :=
      wordError_upper_majorant hN ht cs Q rho w Y hQ hrho hw hzero
    _ ≤ ∑ m ∈ S, u*a m^2+b m^2/u :=
      Finset.sum_le_sum (fun m hm => young_scaled (a m) (b m) u hu)
    _ = u*(∑ m ∈ S, a m^2)+(∑ m ∈ S, b m^2)/u := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_div]
    _ ≤ u*((N : ℝ)*L^J)+(34*Y*L^3)/u := by gcongr
    _ = _ := by ring

/-- The exponential upper wall really is a short positive difference.
Only the elementary exp tangent bound is used; no asymptotic is assumed. -/
theorem upper_wall_difference_le {N m : ℕ} {δ : ℝ} (hm : m < N)
    (hwall : (N : ℝ) < (m : ℝ)*Real.exp (4*δ)) :
    ((N-m : ℕ) : ℝ) ≤ 4*δ*(N : ℝ) := by
  have he : 1-4*δ ≤ Real.exp (-(4*δ)) := by
    linarith [Real.add_one_le_exp (-(4*δ))]
  have hmR : (N : ℝ)*Real.exp (-(4*δ)) < m := by
    have h := mul_lt_mul_of_pos_right hwall (Real.exp_pos (-(4*δ)))
    have hexp : Real.exp (4*δ)*Real.exp (-(4*δ))=1 := by
      rw [← Real.exp_add]; simp
    simpa only [mul_assoc,hexp,mul_one] using h
  have hscaled := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)
  rw [Nat.cast_sub hm.le]
  nlinarith

/-- One mesh exponent is fixed before N, the marked pair, and every
arithmetic choice. The two Young contributions have the same log decay. -/
def upperMeshExponent (J A : ℕ) : ℕ := J+(A+2)+(A+2)+3

private theorem logMesh_budget {N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ))
    (J A : ℕ) :
    (1/(Real.log (N : ℝ))^(J+(A+2)))*(N : ℝ)*(1+Real.log (N : ℝ))^J +
      34*(4*boundaryLogMesh (upperMeshExponent J A) N*(N : ℝ))*
        (1+Real.log (N : ℝ))^3/(1/(Real.log (N : ℝ))^(J+(A+2))) ≤
      ((2 : ℝ)^J+1088)*(N : ℝ)/(Real.log (N : ℝ))^(A+2) := by
  let l := Real.log (N : ℝ)
  have hl : 0 < l := by dsimp [l]; linarith
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hL : 1+l ≤ 2*l := by dsimp [l]; linarith
  have hC : (1+l)^J ≤ (2*l)^J :=
    pow_le_pow_left₀ (by linarith) hL J
  have h3 : (1+l)^3 ≤ (2*l)^3 :=
    pow_le_pow_left₀ (by linarith) hL 3
  calc
    _ ≤ (1/l^(J+(A+2)))*(N : ℝ)*(2*l)^J +
        34*(4*boundaryLogMesh (upperMeshExponent J A) N*(N : ℝ))*
          (2*l)^3/(1/l^(J+(A+2))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hC (by positivity)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h3 (by
            unfold boundaryLogMesh
            positivity)) (by positivity)
    _ = _ := by
      change (1/l^(J+(A+2)))*(N : ℝ)*(2*l)^J +
        34*(4*(1/l^(J+(A+2)+(A+2)+3))*(N : ℝ))*(2*l)^3/
          (1/l^(J+(A+2))) = ((2 : ℝ)^J+1088)*(N : ℝ)/l^(A+2)
      simp only [pow_add,mul_pow]
      field_simp [hl.ne']
      ring

/-- Uniform actual-word upper-wall payment. Its inputs are only bounded
weights and their literal geometric support, not a residual estimate.
The moment exponent J is fixed; no data-dependent constants occur. -/
theorem eventually_word_upper_wall_logAccuracy (J A : ℕ) (eta : ℝ)
    (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (t : ℕ × ℕ), t ∈ pairSupport N →
      ∀ (cs : List ℕ), (cs.length+2)^2-1 ≤ J →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (w : Label → ℝ) (δ : ℝ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q, |rho q| ≤ 1) →
      δ ≤ boundaryLogMesh (upperMeshExponent J A) N →
      (∀ x ∈ rootLabels N t cs, |w x| ≤ 1) →
      (∀ x ∈ rootLabels N t cs, w x ≠ 0 →
        (N : ℝ) < (product (t.1*t.2) x : ℝ)*Real.exp (4*δ)) →
      |wordError N t cs Q rho w| ≤ eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let B := upperMeshExponent J A
  let C : ℝ := (2 : ℝ)^J+1088
  have hB : 0 < B := by dsimp [B,upperMeshExponent]; omega
  have hmesh : ∀ᶠ N : ℕ in atTop, 4*boundaryLogMesh B N ≤ 1 := by
    have h := (tendsto_boundaryLogMesh hB).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))
    filter_upwards [h] with N hN
    linarith
  have hgrowth : ∀ᶠ N : ℕ in atTop, (Real.log (N : ℝ))^B ≤ N := by
    simpa only [Real.rpow_zero,one_mul,pow_zero,div_one] using
      eventually_powerLog_le_logAccuracy 1 0 B 0 (by norm_num) 1 (by norm_num)
  have hcost := eventually_boundaryLogMesh_main_le_logAccuracy C A
    (k := A+4) (by omega) eta heta
  filter_upwards [hmesh,hgrowth,hcost,eventually_one_le_nat_log,
    eventually_ge_atTop (1 : ℕ)] with N hmeshN hgrowthN hcostN hlog hN
  intro t ht cs hJ Q rho w δ hQ hrho hδ hw hwall
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
  have hzero : ∀ x ∈ rootLabels N t cs,
      Y < ((N-product (t.1*t.2) x : ℕ) : ℝ) → w x=0 := by
    intro x hx hlarge
    by_contra hwx
    have hd := upper_wall_difference_le (rootLabels_data hx).2.2.2 (hwall x hx hwx)
    have hwidth : 4*δ*(N : ℝ) ≤ Y := by
      dsimp [Y]
      gcongr
    exact (not_lt_of_ge (hd.trans hwidth)) hlarge
  have hfinite := wordError_upper_strip_le hN ht cs J hJ hY hYN hu
    Q rho w hQ hrho hw hzero
  have hnumeric := logMesh_budget hlog J A
  have hcost' : C*(N : ℝ)/l^(A+2) ≤ eta*(N : ℝ)/l^A := by
    have heq : C*(N : ℝ)/l^(A+2) =
        C*boundaryLogMesh (A+4) N*(N : ℝ)*l^2 := by
      unfold boundaryLogMesh
      change C*(N : ℝ)/l^(A+2)=C*(1/l^(A+4))*(N : ℝ)*l^2
      rw [show A+4=(A+2)+2 by omega,pow_add]
      field_simp [hl.ne']
      ring
    rw [heq]
    exact hcostN
  exact hfinite.trans (hnumeric.trans hcost')

/-- Continue Q16's first-priority lower split. The upper boundary itself
is assigned to the final ordering remainder, so the split is exact. -/
def rawUpperRejectedWeight (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ) (K : ℕ)
    (x : Label) : ℝ :=
  if (N : ℝ) < (product (t.1*t.2) x : ℝ)*Real.exp (4*δ) then
    rawRemainingRejectedWeight N t H δ K x else 0

def rawOrderRejectedWeight (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ) (K : ℕ)
    (x : Label) : ℝ :=
  if (N : ℝ) < (product (t.1*t.2) x : ℝ)*Real.exp (4*δ) then 0 else
    rawRemainingRejectedWeight N t H δ K x

theorem remaining_eq_upper_add_order (N : ℕ) (t : ℕ × ℕ)
    (H δ : ℝ) (K : ℕ) (x : Label) :
    rawRemainingRejectedWeight N t H δ K x =
      rawUpperRejectedWeight N t H δ K x+rawOrderRejectedWeight N t H δ K x := by
  by_cases h : (N : ℝ) < (product (t.1*t.2) x : ℝ)*Real.exp (4*δ) <;>
    simp [rawUpperRejectedWeight,rawOrderRejectedWeight,h]

def wordUpperRejectedWeight (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (T H δ : ℝ) (K : ℕ) (x : Label) : ℝ :=
  if cs=[] then 0 else smoothTrim T (product (t.1*t.2) x) *
    rawUpperRejectedWeight N t H δ K x

theorem wordUpperRejectedWeight_abs_le_one (N : ℕ) (t : ℕ × ℕ)
    (cs : List ℕ) (T H δ : ℝ) (K : ℕ) (x : Label) :
    |wordUpperRejectedWeight N t cs T H δ K x| ≤ 1 := by
  have hr := rejectedRealWeight_range N t H δ K x
  have h0 : 0 ≤ smoothTrim T (product (t.1*t.2) x) :=
    Real.smoothTransition.nonneg _
  have h1 : smoothTrim T (product (t.1*t.2) x) ≤ 1 :=
    Real.smoothTransition.le_one _
  unfold wordUpperRejectedWeight rawUpperRejectedWeight rawRemainingRejectedWeight
  split_ifs <;> simp only [mul_zero,abs_zero,zero_le_one]
  rw [abs_of_nonneg (mul_nonneg h0 hr.1)]
  exact (mul_le_mul h1 hr.2 hr.1 zero_le_one).trans_eq (by norm_num)

theorem wordUpperRejectedWeight_support {N : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    {T H δ : ℝ} {K : ℕ} {x : Label}
    (hw : wordUpperRejectedWeight N t cs T H δ K x ≠ 0) :
    (N : ℝ) < (product (t.1*t.2) x : ℝ)*Real.exp (4*δ) := by
  by_contra h
  exact hw (by simp [wordUpperRejectedWeight,rawUpperRejectedWeight,h])

/-- The already defined rejection is attached to the proved arithmetic
payment. Neither a small-mass assertion nor a distribution port is an input. -/
theorem eventually_actual_upperRejected_word_logAccuracy (J A : ℕ)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (t : ℕ × ℕ), t ∈ pairSupport N →
      ∀ (cs : List ℕ), (cs.length+2)^2-1 ≤ J →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q, |rho q| ≤ 1) →
      δ ≤ boundaryLogMesh (upperMeshExponent J A) N →
      |wordError N t cs Q rho (wordUpperRejectedWeight N t cs T H δ K)| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_word_upper_wall_logAccuracy J A eta heta] with N hN
  intro t ht cs hJ Q rho T H δ K hQ hrho hδ
  exact hN t ht cs hJ Q rho (wordUpperRejectedWeight N t cs T H δ K) δ
    hQ hrho hδ (fun x hx => wordUpperRejectedWeight_abs_le_one N t cs T H δ K x)
    (fun x hx hw => wordUpperRejectedWeight_support hw)

/-- A symbolic maximum over the literal occurrence list. It is not a
deduplicated set and no finite numeric guard is evaluated. -/
def listMomentOrder : List (List ℕ) → ℕ
  | [] => 0
  | cs::L => max ((cs.length+2)^2-1) (listMomentOrder L)

theorem le_listMomentOrder {L : List (List ℕ)} {cs : List ℕ}
    (hcs : cs ∈ L) : (cs.length+2)^2-1 ≤ listMomentOrder L := by
  induction L with
  | nil => simp at hcs
  | cons ds L ih =>
      rcases List.mem_cons.mp hcs with h|h
      · subst cs
        exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

def originalUpperRejectedError (N : ℕ) (t : ℕ × ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  (originalMotherOccurrences.map (fun cs => wordError N t cs Q rho
    (wordUpperRejectedWeight N t cs T H δ K))).sum

/-- ALL literal mother occurrences use one mesh and one N threshold.
Every later t, grid, complete-product trim and signed modulus family is
covered. This is a fixed-t assertion; it does not pay an outside t-sum. -/
theorem eventually_original_upperRejected_logAccuracy (A : ℕ) (eta : ℝ)
    (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (t : ℕ × ℕ), t ∈ pairSupport N →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q, |rho q| ≤ 1) →
      δ ≤ boundaryLogMesh
        (upperMeshExponent (listMomentOrder originalMotherOccurrences) A) N →
      |originalUpperRejectedError N t Q rho T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let L := originalMotherOccurrences
  let J := listMomentOrder L
  let eta0 := eta/((L.length : ℝ)+1)
  have heta0 : 0 < eta0 := by dsimp [eta0]; positivity
  filter_upwards [eventually_actual_upperRejected_word_logAccuracy J A eta0 heta0,
    eventually_one_le_nat_log] with N hword hlog
  intro t ht Q rho T H δ K hQ hrho hδ
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  let f := fun cs => wordError N t cs Q rho (wordUpperRejectedWeight N t cs T H δ K)
  let E := eta0*(N : ℝ)/(Real.log (N : ℝ))^A
  have heach : ∀ cs ∈ L, |f cs| ≤ E := by
    intro cs hcs
    exact hword t ht cs (le_listMomentOrder hcs) Q rho T H δ K hQ hrho hδ
  have hsum : ∀ W : List (List ℕ), (∀ cs ∈ W, |f cs| ≤ E) →
      |(W.map f).sum| ≤ (W.length : ℝ)*E := by
    intro W
    induction W with
    | nil => intro _; simp
    | cons cs W ih =>
        intro hW
        have hc := hW cs (List.mem_cons_self cs W)
        have hw := ih (fun ds hds => hW ds (List.mem_cons_of_mem cs hds))
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        exact (abs_add (f cs) ((W.map f).sum)).trans
          ((add_le_add hc hw).trans_eq (by ring))
  have hcoefficient : (L.length : ℝ)*eta0 ≤ eta := by
    dsimp [eta0]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (L.length : ℝ)+1)).mpr
    nlinarith
  calc
    _ ≤ (L.length : ℝ)*E := hsum L heach
    _ = ((L.length : ℝ)*eta0)*((N : ℝ)/(Real.log (N : ℝ))^A) := by
      dsimp [E]
      ring
    _ ≤ eta*((N : ℝ)/(Real.log (N : ℝ))^A) :=
      mul_le_mul_of_nonneg_right hcoefficient
        (div_nonneg (Nat.cast_nonneg N) (pow_nonneg hlog0 A))
    _ = _ := by ring

/-- Exact continuation of Q16's already established lower split. The
only final source remainder is the displayed rawOrderRejectedWeight. -/
theorem original_rejected_remaining_eq_upper_add_order
    (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ)
    (T H δ : ℝ) (K : ℕ) (F : ℕ → ℂ) :
    (∑ x ∈ rootLabels N t (c::cs),
      (rawRemainingRejectedWeight N t H δ K x : ℂ) *
        (smoothTrim T (product (t.1*t.2) x) : ℂ)*F (product (t.1*t.2) x)) =
    (∑ x ∈ rootLabels N t (c::cs),
      (wordUpperRejectedWeight N t (c::cs) T H δ K x : ℂ)*F (product (t.1*t.2) x)) +
    ∑ x ∈ rootLabels N t (c::cs),
      (rawOrderRejectedWeight N t H δ K x : ℂ) *
        (smoothTrim T (product (t.1*t.2) x) : ℂ)*F (product (t.1*t.2) x) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [remaining_eq_upper_add_order]
  simp only [wordUpperRejectedWeight,List.cons_ne_nil,if_false,
    Complex.ofReal_add,Complex.ofReal_mul]
  ring

/-- The remaining aggregate is an actual STRICT ordering strip on the
original labels. This supplies its carrier, not an estimate for its mass. -/
theorem rawOrderRejectedWeight_support {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ) {K : ℕ} {x : Label}
    (hx : x ∈ rootLabels N t (c::cs))
    (hw : rawOrderRejectedWeight N t H δ K x ≠ 0) :
    ∃ r ∈ (labelComplement x).1, labelHead x < r ∧
      (r : ℝ) < (labelHead x : ℝ)*Real.exp (2*δ) := by
  have hlow : ¬ (product (t.1*t.2) x : ℝ) < H*Real.exp (4*δ) := by
    intro h
    exact hw (by simp [rawOrderRejectedWeight,rawRemainingRejectedWeight,h])
  have hupp : ¬ (N : ℝ) < (product (t.1*t.2) x : ℝ)*Real.exp (4*δ) := by
    intro h
    exact hw (by simp [rawOrderRejectedWeight,h])
  have hrej : rejectedWeight N t H δ K x ≠ 0 := by
    intro hz
    have hzC : (rejectedRealWeight N t H δ K x : ℂ)=0 :=
      (rejectedRealWeight_cast N t H δ K x).trans hz
    have hzR : rejectedRealWeight N t H δ K x=0 := Complex.ofReal_eq_zero.mp hzC
    exact hw (by simp [rawOrderRejectedWeight,rawRemainingRejectedWeight,hzR])
  have hp := P2GammaOriginalCartesianMask.original_head_mem_carrier hx
  have hy : labelComplement x ∈ rootComplementLabels N t (c::cs) :=
    Finset.mem_image_of_mem (fun z : Label => (z.1.tail,z.2)) hx
  have hp0 : (0 : ℝ) < labelHead x := by
    exact_mod_cast (original_label_head_prime (by simp) hx).pos
  have hm0 : (0 : ℝ) < product (t.1*t.2) (labelComplement x) := by
    exact_mod_cast P2GammaOriginalCartesianMask.complement_product_pos ht hy
  have hprod : (labelHead x : ℝ)*(product (t.1*t.2) (labelComplement x) : ℝ) =
      (product (t.1*t.2) x : ℝ) := by
    rw [original_label_head_product (by simp) hx]
    push_cast
    ring
  have hnear : ∃ r ∈ (labelComplement x).1,
      (r : ℝ) < (labelHead x : ℝ)*Real.exp (2*δ) := by
    by_contra hn
    apply hrej
    unfold rejectedWeight
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro l hl
    by_contra hterm
    rcases rejected_row_support hδ hp0 hm0 hterm with hlow'|hupp'|hnear'
    · exact hlow (by simpa only [hprod] using hlow')
    · exact hupp (by simpa only [hprod] using hupp')
    · exact hn hnear'
  obtain ⟨r,hr,hclose⟩ := hnear
  have hlegal : P2GammaOriginalCartesianMask.rebuild (labelHead x) (labelComplement x) ∈
      rootLabels N t (c::cs) := by
    rw [P2GammaOriginalCartesianMask.rebuild_head_complement hx]
    exact hx
  exact ⟨r,hr,((P2GammaOriginalCartesianMask.rebuild_mem_root_iff hp hy).mp hlegal).1 r hr,
    hclose⟩

end
end ImbalancedChen.P2GammaUpperStripPayment
