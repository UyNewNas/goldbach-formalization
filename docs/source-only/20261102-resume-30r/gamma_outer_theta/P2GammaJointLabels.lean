import ImbalancedChen.P2GammaUpperStripPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The old marked pair is now part of the finite arithmetic source, rather
than an index outside a fixed-pair error estimate. Its TWO entries are
encoded separately. This retains equal complete products, all original
word positions and the original positive quotient, including quotient 1.
The fibre divisor order is therefore length(cs)+3, not length(cs)+2.

This file supplies a joint absolute upper-strip payment. It makes no
relative-Theta assertion and does not supply the lower/order remainders
or the causal selected-family dictionary. No pair-support cardinality
multiplies a fixed-t discrepancy estimate.
-/

namespace ImbalancedChen.P2GammaJointLabels
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2OriginalGammaUpperLowRankConsumer
open P2GammaCompleteProductTrimPayment P2GammaUpperStripPayment
open P5OriginalU5CausalFinite (pairSupport)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev JointLabel := (ℕ × ℕ) × Label

def jointLabels (N : ℕ) (cs : List ℕ) : Finset JointLabel :=
  (pairSupport N).biUnion (fun t => (rootLabels N t cs).image (fun x => (t,x)))

theorem mem_jointLabels (N : ℕ) (cs : List ℕ) (z : JointLabel) :
    z ∈ jointLabels N cs ↔ z.1 ∈ pairSupport N ∧ z.2 ∈ rootLabels N z.1 cs := by
  rcases z with ⟨t,x⟩
  simp [jointLabels]

def jointProduct (z : JointLabel) : ℕ := product (z.1.1*z.1.2) z.2

theorem jointProduct_bounds {N : ℕ} {cs : List ℕ} {z : JointLabel}
    (hz : z ∈ jointLabels N cs) : 0 < jointProduct z ∧ jointProduct z < N := by
  obtain ⟨ht,hx⟩ := (mem_jointLabels N cs z).mp hz
  exact ⟨root_product_positive ht hx,(rootLabels_data hx).2.2.2⟩

/-- Disjoint tagged pair fibres give the literal outer-pair sum exactly. -/
theorem joint_sum_eq_pair_sum (N : ℕ) (cs : List ℕ) (F : JointLabel → ℝ) :
    (∑ z ∈ jointLabels N cs,F z) =
      ∑ t ∈ pairSupport N,∑ x ∈ rootLabels N t cs,F (t,x) := by
  have hdisj : (↑(pairSupport N) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun t => (rootLabels N t cs).image (fun x => (t,x))) := by
    intro t ht u hu htu
    apply Finset.disjoint_left.mpr
    intro z hzt hzu
    obtain ⟨x,hx,hxeq⟩ := Finset.mem_image.mp hzt
    obtain ⟨y,hy,hyeq⟩ := Finset.mem_image.mp hzu
    exact htu (congrArg Prod.fst (hxeq.trans hyeq.symm))
  rw [jointLabels,Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro t ht
  exact Finset.sum_image (fun x hx y hy hxy => (Prod.mk.inj hxy).2)

def jointProductFiber (N : ℕ) (cs : List ℕ) (m : ℕ) : Finset JointLabel :=
  (jointLabels N cs).filter (fun z => jointProduct z=m)

def jointProducts (N : ℕ) (cs : List ℕ) : Finset ℕ :=
  (jointLabels N cs).image jointProduct

def jointFactorList (z : JointLabel) : List ℕ :=
  z.1.1 :: z.1.2 :: (z.2.1 ++ [z.2.2])

/-- Both old primes occur as labelled factor slots. Thus equality of
the code recovers the old pair as well as the complete word/quotient. -/
theorem card_jointProductFiber_le (N : ℕ) (cs : List ℕ) (m : ℕ) :
    (jointProductFiber N cs m).card ≤ fouvryTau (cs.length+3) m := by
  rw [← card_orderedFactors]
  apply Finset.card_le_card_of_injOn jointFactorList
  · intro z hz
    obtain ⟨hz,hm⟩ := Finset.mem_filter.mp hz
    obtain ⟨ht,hx⟩ := (mem_jointLabels N cs z).mp hz
    apply (mem_orderedFactors (cs.length+3) m (jointFactorList z)).mpr
    refine ⟨?_,?_,hm ▸ (jointProduct_bounds hz).1⟩
    · simp only [jointFactorList,List.length_cons,List.length_append,
        List.length_singleton,root_word_length hx]
      omega
    · simpa only [jointFactorList,List.prod_cons,List.prod_append,
        List.prod_singleton,jointProduct,product,mul_assoc] using hm
  · intro z hz v hv hcode
    have hzroot := (mem_jointLabels N cs z).mp (Finset.mem_filter.mp hz).1
    have hvroot := (mem_jointLabels N cs v).mp (Finset.mem_filter.mp hv).1
    obtain ⟨ht1,htail⟩ := List.cons.inj hcode
    obtain ⟨ht2,happend⟩ := List.cons.inj htail
    obtain ⟨hword,hquot⟩ := List.append_inj happend
      ((root_word_length hzroot.2).trans (root_word_length hvroot.2).symm)
    exact Prod.ext (Prod.ext ht1 ht2) (Prod.ext hword (by simpa using hquot))

/-- Grouping is by the complete product AFTER retaining every pair and
word/quotient label. No injectivity of jointProduct is asserted. -/
theorem joint_real_test_eq_grouped (N : ℕ) (cs : List ℕ) (F : ℕ → ℝ) :
    (∑ z ∈ jointLabels N cs,F (jointProduct z)) =
      ∑ m ∈ jointProducts N cs,((jointProductFiber N cs m).card : ℝ)*F m := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := jointLabels N cs) (t := jointProducts N cs) (g := jointProduct)
    (fun z hz => Finset.mem_image_of_mem _ hz) (fun z => F (jointProduct z))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m hm
  calc
    _ = ∑ _z ∈ jointProductFiber N cs m,F m := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
    _ = _ := by simp

/-- The divisor norm is supplied for the actual complete joint source.
Its exponent is fixed by the word length before any accuracy or N. -/
theorem joint_multiplicity_square_sum_le (N : ℕ) (cs : List ℕ)
    {X : ℝ} (hX : 1 ≤ X) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc 0 ⌊X⌋₊) :
    (∑ m ∈ S,((jointProductFiber N cs m).card : ℝ)^2) ≤
      X*(1+Real.log X)^((cs.length+3)^2-1) := by
  apply sum_alpha_sq_le_fouvryTau (by omega : 1 ≤ cs.length+3) hX S hS
    (fun m => ((jointProductFiber N cs m).card : ℝ))
  intro m hm
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast card_jointProductFiber_le N cs m

def jointError (N : ℕ) (cs : List ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (w : JointLabel → ℝ) : ℝ :=
  ∑ q ∈ Q,rho q*∑ z ∈ jointLabels N cs,w z*gammaKernel N q (jointProduct z)

/-- Exact attachment to the unchanged Q wordError, with the same rho. -/
theorem jointError_eq_outer_wordError (N : ℕ) (cs : List ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ) (w : JointLabel → ℝ) :
    jointError N cs Q rho (fun z => sigma z.1*w z) =
      ∑ t ∈ pairSupport N,sigma t*wordError N t cs Q rho (fun x => w (t,x)) := by
  unfold jointError wordError
  simp_rw [joint_sum_eq_pair_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro x hx
  dsimp [jointProduct]
  ring

/-- The exact signed modulus sum is paid jointly. The primitive bounded
label weight can include any later one-bounded positive outer selector. -/
theorem jointError_upper_majorant {N : ℕ} (hN : 1 ≤ N)
    (cs : List ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) (w : JointLabel → ℝ) (Y : ℝ)
    (hQ : Q ⊆ Finset.Icc 1 N) (hrho : ∀ q ∈ Q,|rho q| ≤ 1)
    (hw : ∀ z ∈ jointLabels N cs,|w z| ≤ 1)
    (hzero : ∀ z ∈ jointLabels N cs,Y < ((N-jointProduct z : ℕ) : ℝ) → w z=0) :
    |jointError N cs Q rho w| ≤
      ∑ m ∈ upperProducts N Y,((jointProductFiber N cs m).card : ℝ)*
        (((N-m).divisors.card : ℝ)+4*(1+Real.log (N : ℝ))) := by
  let b : ℕ → ℝ := fun m => ((N-m).divisors.card : ℝ)+4*(1+Real.log (N : ℝ))
  let F : ℕ → ℝ := fun m => if ((N-m : ℕ) : ℝ) ≤ Y then b m else 0
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb (m : ℕ) : 0 ≤ b m := by
    dsimp [b]
    have := Real.log_nonneg hNr
    positivity
  have hF (m : ℕ) : 0 ≤ F m := by dsimp [F]; split_ifs <;> positivity
  have heq : jointError N cs Q rho w =
      ∑ z ∈ jointLabels N cs,w z*∑ q ∈ Q,rho q*gammaKernel N q (jointProduct z) := by
    simp only [jointError,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hlabels : |jointError N cs Q rho w| ≤ ∑ z ∈ jointLabels N cs,F (jointProduct z) := by
    rw [heq]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro z hz
    by_cases hband : ((N-jointProduct z : ℕ) : ℝ) ≤ Y
    · have hk := kernel_absolute_modulus_sum_le (jointProduct_bounds hz).2 Q rho hQ hrho
      rw [max_eq_right hNr] at hk
      simp only [F,if_pos hband]
      rw [abs_mul]
      exact (mul_le_mul (hw z hz) (Finset.abs_sum_le_sum_abs _ _)
        (abs_nonneg _) zero_le_one).trans (by simpa only [one_mul] using hk)
    · simp only [F,if_neg hband,hzero z hz (lt_of_not_ge hband),zero_mul,abs_zero]
  have hproducts : jointProducts N cs ⊆ Finset.Ioc 0 N := by
    intro m hm
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_Ioc.mpr ⟨(jointProduct_bounds hz).1,(jointProduct_bounds hz).2.le⟩
  calc
    _ ≤ ∑ z ∈ jointLabels N cs,F (jointProduct z) := hlabels
    _ = ∑ m ∈ jointProducts N cs,((jointProductFiber N cs m).card : ℝ)*F m :=
      joint_real_test_eq_grouped N cs F
    _ ≤ ∑ m ∈ Finset.Ioc 0 N,((jointProductFiber N cs m).card : ℝ)*F m :=
      Finset.sum_le_sum_of_subset_of_nonneg hproducts
        (fun m hm hnot => mul_nonneg (Nat.cast_nonneg _) (hF m))
    _ = _ := by
      rw [upperProducts,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmN : m < N
      · by_cases hmY : ((N-m : ℕ) : ℝ) ≤ Y <;> simp [F,b,hmN,hmY]
      · have hempty : jointProductFiber N cs m=∅ := by
          apply Finset.eq_empty_iff_forall_not_mem.mpr
          intro z hz
          obtain ⟨hz,heq⟩ := Finset.mem_filter.mp hz
          exact hmN (heq ▸ (jointProduct_bounds hz).2)
        simp [hempty,hmN]

/-- Joint finite upper-strip payment. Q's positive-difference moment and
Young inequality are reused; only the joint actual fibre norm is new. -/
theorem jointError_upper_strip_le {N : ℕ} (hN : 1 ≤ N) (cs : List ℕ) (J : ℕ)
    (hJ : (cs.length+3)^2-1 ≤ J) {Y u : ℝ}
    (hY : 1 ≤ Y) (hYN : Y ≤ N) (hu : 0 < u)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (w : JointLabel → ℝ)
    (hQ : Q ⊆ Finset.Icc 1 N) (hrho : ∀ q ∈ Q,|rho q| ≤ 1)
    (hw : ∀ z ∈ jointLabels N cs,|w z| ≤ 1)
    (hzero : ∀ z ∈ jointLabels N cs,Y < ((N-jointProduct z : ℕ) : ℝ) → w z=0) :
    |jointError N cs Q rho w| ≤
      u*(N : ℝ)*(1+Real.log (N : ℝ))^J+34*Y*(1+Real.log (N : ℝ))^3/u := by
  let S := upperProducts N Y
  let L := 1+Real.log (N : ℝ)
  let a := fun m => ((jointProductFiber N cs m).card : ℝ)
  let b := fun m => ((N-m).divisors.card : ℝ)+4*L
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hNr]
  have hS : S ⊆ Finset.Ioc 0 ⌊(N : ℝ)⌋₊ := by
    simpa only [Nat.floor_natCast] using (Finset.filter_subset
      (fun m => m < N ∧ ((N-m : ℕ) : ℝ) ≤ Y) (Finset.Ioc 0 N))
  have ha : (∑ m ∈ S,a m^2) ≤ (N : ℝ)*L^J :=
    (joint_multiplicity_square_sum_le N cs hNr S hS).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hJ) (Nat.cast_nonneg N))
  have htau : (∑ m ∈ S,((N-m).divisors.card : ℝ)^2) ≤ Y*L^3 :=
    upperProducts_difference_square_sum_le hY hYN
  have hc : (S.card : ℝ) ≤ Y := upperProducts_card_le (by linarith)
  have hL2 : L^2 ≤ L^3 := pow_le_pow_right₀ hL (by omega)
  have hb : (∑ m ∈ S,b m^2) ≤ 34*Y*L^3 := by
    calc
      _ ≤ ∑ m ∈ S,2*((N-m).divisors.card : ℝ)^2+32*L^2 := by
        apply Finset.sum_le_sum
        intro m hm
        dsimp [b]
        nlinarith [sq_nonneg (((N-m).divisors.card : ℝ)-4*L)]
      _ = 2*(∑ m ∈ S,((N-m).divisors.card : ℝ)^2)+32*L^2*(S.card : ℝ) := by
        rw [Finset.sum_add_distrib,Finset.mul_sum]
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ 2*(Y*L^3)+32*L^2*Y := by gcongr
      _ ≤ 34*Y*L^3 := by nlinarith [mul_le_mul_of_nonneg_right hL2 (by linarith : 0 ≤ Y)]
  calc
    _ ≤ ∑ m ∈ S,a m*b m := jointError_upper_majorant hN cs Q rho w Y hQ hrho hw hzero
    _ ≤ ∑ m ∈ S,u*a m^2+b m^2/u :=
      Finset.sum_le_sum (fun m hm => young_scaled (a m) (b m) u hu)
    _ = u*(∑ m ∈ S,a m^2)+(∑ m ∈ S,b m^2)/u := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_div]
    _ ≤ u*((N : ℝ)*L^J)+(34*Y*L^3)/u := by gcongr
    _ = _ := by ring

end
end ImbalancedChen.P2GammaJointLabels
