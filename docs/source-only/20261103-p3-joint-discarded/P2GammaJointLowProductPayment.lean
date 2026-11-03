import ImbalancedChen.P2GammaJointOrderPayment

/-!
Source-only / UNCOMPILED / KERNEL-UNVERIFIED.
An actual joint low-product count and payment. Both old prime slots,
all mother-word positions and the positive quotient are retained.
The existing joint second moment and joint kernel energy are reused.
There is no multiplication by the number of outside pairs and no
assumed coefficient energy or low-product error estimate.
-/

namespace ImbalancedChen.P2GammaJointLowProductPayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2OriginalGammaUpperLowRankConsumer
open P2GammaCompleteProductTrimPayment P2GammaUpperStripPayment
open P2GammaOrderingStripPayment P2GammaJointLabels P2GammaJointOrderPayment

/-- The original joint labels cut by their complete integer product. -/
def jointLowLabels (N : ℕ) (cs : List ℕ) (Y : ℕ) : Finset JointLabel :=
  (jointLabels N cs).filter (fun z => jointProduct z ≤ Y)

private theorem card_cast_le_square (n : ℕ) : (n : ℝ) ≤ (n : ℝ)^2 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      nlinarith

/-- The joint multiplicity is NOT discarded. The integer inequality
`a <= a^2` and R17's proved fibre moment pay its entire low-product mass. -/
theorem jointLowLabels_card_le {N Y : ℕ} (hY : 1 ≤ Y) (hYN : Y ≤ N)
    (cs : List ℕ) (J : ℕ) (hJ : (cs.length+3)^2-1 ≤ J) :
    ((jointLowLabels N cs Y).card : ℝ) ≤
      (Y : ℝ)*(1+Real.log (N : ℝ))^J := by
  let S := jointLowLabels N cs Y
  let a := fun m => ((jointProductFiber N cs m).card : ℝ)
  have hYr : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hYpos : (0 : ℝ) < Y := by linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hY.trans hYN
  have hL : 1 ≤ 1+Real.log (N : ℝ) := by linarith [Real.log_nonneg hNr]
  have hmap : ∀ z ∈ S, jointProduct z ∈ Finset.Ioc 0 Y := by
    intro z hz
    obtain ⟨hz,hzy⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_Ioc.mpr ⟨(jointProduct_bounds hz).1,hzy⟩
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.Ioc 0 Y) (g := jointProduct) hmap (fun _ => (1 : ℝ))
  have hc : (S.card : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 Y, a m := by
    calc
      _ = ∑ m ∈ Finset.Ioc 0 Y, ∑ z ∈ S with jointProduct z=m, (1 : ℝ) := by
        simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hf.symm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m hm
        have hsub : S.filter (fun z => jointProduct z=m) ⊆ jointProductFiber N cs m := by
          intro z hz
          obtain ⟨hz,heq⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,heq⟩
        have hh : ((S.filter (fun z => jointProduct z=m)).card : ℝ) ≤ a m := by
          exact_mod_cast Finset.card_le_card hsub
        simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
  have hmoment := joint_multiplicity_square_sum_le N cs hYr (Finset.Ioc 0 Y)
    (by intro m hm; simpa only [Nat.floor_natCast] using hm)
  have hlog : Real.log (Y : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hYpos (by exact_mod_cast hYN)
  calc
    _ ≤ ∑ m ∈ Finset.Ioc 0 Y, a m := hc
    _ ≤ ∑ m ∈ Finset.Ioc 0 Y, a m^2 :=
      Finset.sum_le_sum (fun m hm => card_cast_le_square _)
    _ ≤ (Y : ℝ)*(1+Real.log (Y : ℝ))^((cs.length+3)^2-1) := hmoment
    _ ≤ (Y : ℝ)*(1+Real.log (N : ℝ))^((cs.length+3)^2-1) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [Real.log_nonneg hYr]) (by linarith) _)
        (Nat.cast_nonneg Y)
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hJ) (Nat.cast_nonneg Y)

/-- A finite actual-source estimate, with the exact signed modulus sum
and its coprime mean. The only weight premises are height and support. -/
theorem jointError_low_product_le {N Y : ℕ} (hN : 1 ≤ N)
    (hY : 1 ≤ Y) (hYN : Y ≤ N) (cs : List ℕ) (J : ℕ)
    (hJ : (cs.length+3)^2-1 ≤ J) {u : ℝ} (hu : 0 < u)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (w : JointLabel → ℝ)
    (hQ : Q ⊆ Finset.Icc 1 N) (hrho : ∀ q ∈ Q, |rho q| ≤ 1)
    (hw : ∀ z ∈ jointLabels N cs, |w z| ≤ 1)
    (hzero : ∀ z ∈ jointLabels N cs, Y < jointProduct z → w z=0) :
    |jointError N cs Q rho w| ≤
      u*(Y : ℝ)*(1+Real.log (N : ℝ))^J+
        34*(N : ℝ)*(1+Real.log (N : ℝ))^(kernelMomentExponent J)/u := by
  let S := jointLowLabels N cs Y
  let L := 1+Real.log (N : ℝ)
  let b := fun z : JointLabel => ((N-jointProduct z).divisors.card : ℝ)+4*L
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsub : S ⊆ jointLabels N cs := Finset.filter_subset _ _
  have heq : jointError N cs Q rho w =
      ∑ z ∈ jointLabels N cs,w z*∑ q ∈ Q,rho q*gammaKernel N q (jointProduct z) := by
    simp only [jointError,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hlabel : |jointError N cs Q rho w| ≤ ∑ z ∈ S,b z := by
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
        · have hlarge : Y < jointProduct z := by
            by_contra hh
            exact hs (Finset.mem_filter.mpr ⟨hz,le_of_not_gt hh⟩)
          simp only [if_neg hs,hzero z hz hlarge,zero_mul,abs_zero]
      _ = ∑ z ∈ S,b z := by
        rw [← Finset.sum_filter]
        congr 1
        ext z
        simp [S,jointLowLabels]
  have henergy : (∑ z ∈ S,b z^2) ≤ 34*(N : ℝ)*L^(kernelMomentExponent J) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z hz hnot => sq_nonneg _)).trans
      (joint_label_kernel_energy_le hN cs J hJ)
  have hcard := jointLowLabels_card_le hY hYN cs J hJ
  calc
    _ ≤ ∑ z ∈ S,b z := hlabel
    _ ≤ ∑ z ∈ S,u+b z^2/u :=
      Finset.sum_le_sum (fun z hz => by simpa using young_scaled 1 (b z) u hu)
    _ = u*(S.card : ℝ)+(∑ z ∈ S,b z^2)/u := by
      rw [Finset.sum_add_distrib,Finset.sum_div]
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ u*((Y : ℝ)*L^J)+(34*(N : ℝ)*L^(kernelMomentExponent J))/u := by
      exact add_le_add (mul_le_mul_of_nonneg_left hcard hu.le)
        (div_le_div_of_nonneg_right henergy hu.le)
    _ = _ := by ring

/-- All outer pairs are already INSIDE the estimate. Fixed kappa, C,
J, A and eta precede one threshold; Y, word and weight come afterwards.
The displayed support/height premises will be discharged for the actual
combined discarded weight in the next module. -/
theorem eventually_joint_low_product (J A : ℕ) (kappa C : ℝ)
    (hkappa : 0 < kappa) (hC : 0 < C) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (cs : List ℕ), (cs.length+3)^2-1 ≤ J →
      ∀ (Y : ℕ), 1 ≤ Y → Y ≤ N → (Y : ℝ) ≤ C*(N : ℝ)^(1-kappa) →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (w : JointLabel → ℝ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ z ∈ jointLabels N cs,|w z| ≤ 1) →
      (∀ z ∈ jointLabels N cs,Y < jointProduct z → w z=0) →
      |jointError N cs Q rho w| ≤ eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let E := kernelMomentExponent J
  filter_upwards [eventually_powerLog_le_logAccuracy
      ((C+34)*(2 : ℝ)^E) (1-kappa/2) E A (by linarith) eta heta,
    eventually_one_le_nat_log,eventually_ge_atTop (1 : ℕ)] with N hbudget hlog hN
  intro cs hJ Y hY hYN hcut Q rho w hQ hrho hw hzero
  let L := 1+Real.log (N : ℝ)
  let u := (N : ℝ)^(kappa/2)
  let v := (N : ℝ)^(1-kappa/2)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hu : 0 < u := Real.rpow_pos_of_pos hNp _
  have hv : 0 < v := Real.rpow_pos_of_pos hNp _
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hJE : J ≤ E := (show J ≤ J+2 by omega).trans (le_max_left _ _)
  have hp : L^J ≤ L^E := pow_le_pow_right₀ hL hJE
  have hu_mul : u*(N : ℝ)^(1-kappa)=v := by
    dsimp [u,v]
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hv_mul : v*u=(N : ℝ) := by
    dsimp [u,v]
    rw [← Real.rpow_add hNp]
    rw [show (1-kappa/2)+kappa/2=(1 : ℝ) by ring,Real.rpow_one]
  have hfirst : u*(Y : ℝ)*L^J ≤ C*v*L^E := by
    calc
      _ ≤ u*(C*(N : ℝ)^(1-kappa))*L^J :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcut hu.le)
          (pow_nonneg (by linarith : 0 ≤ L) _)
      _ = C*v*L^J := by rw [mul_left_comm u C,hu_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hC.le hv.le)
  have hsecond : 34*(N : ℝ)*L^E/u=34*v*L^E := by
    apply (div_eq_iff hu.ne').mpr
    calc
      _ = 34*(v*u)*L^E := by rw [hv_mul]
      _ = _ := by ring
  have hfinite := jointError_low_product_le hN hY hYN cs J hJ hu Q rho w hQ hrho hw hzero
  have hpow : L^E ≤ (2*Real.log (N : ℝ))^E :=
    pow_le_pow_left₀ (by linarith : 0 ≤ L) (by dsimp [L]; linarith) _
  calc
    _ ≤ u*(Y : ℝ)*L^J+34*(N : ℝ)*L^E/u := hfinite
    _ ≤ C*v*L^E+34*v*L^E := by rw [hsecond]; exact add_le_add_right hfirst _
    _ = (C+34)*v*L^E := by ring
    _ ≤ (C+34)*v*(2*Real.log (N : ℝ))^E :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ((C+34)*(2 : ℝ)^E)*v*(Real.log (N : ℝ))^E := by rw [mul_pow]; ring
    _ ≤ _ := hbudget

end
end ImbalancedChen.P2GammaJointLowProductPayment
