import ImbalancedChen.P2GammaJointRetainedComplement

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

Partition the ACTUAL outside pairs by any fixed key, without paying the
number of keys or the selector L1 mass. At each complementary integer,
the SUM of block coefficient norms is bounded by height * tau_k.
This yields summed L1 and summed squared L2 bounds for the entire block
family, including the quotient projectors of the conductor decomposition.
The key can depend on the original source parameters but has no modulus
or error-sign argument here. No PP estimate is assumed or concluded.
-/

namespace ImbalancedChen.P2GammaJointComplementBlockNorms
noncomputable section
open scoped Classical BigOperators
open P2GammaJointRetainedComplement P2GammaJointLabels
open P2GammaRetainedInteriorGeometry P2GammaRetainedActualNorms
open P2GammaSmoothLogGrid P2GammaSmallConductorIntervalBridge
open P2GammaConvolutionLargeConductor P2GammaVariablePrimeProfile P2GammaPrimeCharacterSW
open P5OriginalU5CausalFinite (pairSupport)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {κ : Type*} [DecidableEq κ]

def blockKeys (N : ℕ) (key : (ℕ × ℕ) → κ) : Finset κ :=
  (pairSupport N).image key

def blockBeta (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (key : (ℕ × ℕ) → κ) (sigma : (ℕ × ℕ) → ℂ) (a : κ) (m : ℕ) : ℂ :=
  jointBeta N c cs H δ j l (fun t => if key t = a then sigma t else 0) m

/-- A source test may vary between blocks. Reindexing never identifies
these tests, their head windows, or their residues with one another. -/
theorem block_test_eq_pair (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (key : (ℕ × ℕ) → κ) (sigma : (ℕ × ℕ) → ℂ) (F : κ → ℕ → ℂ) :
    (∑ a ∈ blockKeys N key,∑ m ∈ jointRetainedProducts N c cs H δ j l,
      blockBeta N c cs H δ j l key sigma a m * F a m) =
      ∑ t ∈ pairSupport N,sigma t *
        ∑ m ∈ retainedComplementSupport N t c cs H δ j l,
          retainedBeta N t c cs H δ j l m * F (key t) m := by
  simp only [blockBeta]
  simp_rw [jointBeta_test_eq_pair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hk : key t ∈ blockKeys N key := Finset.mem_image_of_mem key ht
  calc
    _ = (if key t = key t then sigma t else 0) *
        ∑ m ∈ retainedComplementSupport N t c cs H δ j l,
          retainedBeta N t c cs H δ j l m * F (key t) m :=
      Finset.sum_eq_single (key t)
        (fun a ha hne => by simp [Ne.symm hne])
        (fun hn => (hn hk).elim)
    _ = _ := by simp

/-- Sum of norms of ALL blocks at a single complete complementary m.
A label belongs to precisely one key. Complex phases and product collisions
are retained; no triangle inequality is applied separately to old pairs. -/
theorem block_norm_sum_le (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l m : ℕ)
    (key : (ℕ × ℕ) → κ) (sigma : (ℕ × ℕ) → ℂ) {height : ℝ}
    (hh : 0 ≤ height) (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) :
    (∑ a ∈ blockKeys N key,‖blockBeta N c cs H δ j l key sigma a m‖) ≤
      height * (fouvryTau (cs.length+3) m : ℝ) := by
  calc
    _ ≤ ∑ a ∈ blockKeys N key,∑ z ∈ jointRetainedFiber N c cs H δ j l m,
        ‖(if key z.1 = a then sigma z.1 else 0) * betaLabel N z.1 H δ j l z.2‖ :=
      Finset.sum_le_sum (fun a ha => norm_sum_le _ _)
    _ = ∑ z ∈ jointRetainedFiber N c cs H δ j l m,
        ‖sigma z.1 * betaLabel N z.1 H δ j l z.2‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      have ht := ((mem_jointRetainedLabels N c cs H δ j l z).mp
        (Finset.mem_filter.mp hz).1).1
      have hk : key z.1 ∈ blockKeys N key := Finset.mem_image_of_mem key ht
      calc
        _ = ‖(if key z.1 = key z.1 then sigma z.1 else 0) *
            betaLabel N z.1 H δ j l z.2‖ :=
          Finset.sum_eq_single (key z.1)
            (fun a ha hne => by simp [Ne.symm hne])
            (fun hn => (hn hk).elim)
        _ = _ := by simp
    _ ≤ ∑ _z ∈ jointRetainedFiber N c cs H δ j l m,height := by
      apply Finset.sum_le_sum
      intro z hz
      have ht := ((mem_jointRetainedLabels N c cs H δ j l z).mp
        (Finset.mem_filter.mp hz).1).1
      rw [norm_mul]
      exact (mul_le_mul (hs z.1 ht) (betaLabel_norm_le_one N z.1 H δ j l z.2)
        (norm_nonneg _) hh).trans_eq (mul_one _)
    _ ≤ _ := by
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using
        mul_le_mul_of_nonneg_left
          (show ((jointRetainedFiber N c cs H δ j l m).card : ℝ) ≤
              (fouvryTau (cs.length+3) m : ℝ) by
            exact_mod_cast card_jointRetainedFiber_le N c cs H δ j l m) hh

/-- Square AFTER the whole block norm sum, not after multiplying a
per-pair worst-case error by the number of pairs. -/
theorem block_square_sum_le (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l m : ℕ)
    (key : (ℕ × ℕ) → κ) (sigma : (ℕ × ℕ) → ℂ) {height : ℝ}
    (hh : 0 ≤ height) (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) :
    (∑ a ∈ blockKeys N key,‖blockBeta N c cs H δ j l key sigma a m‖^2) ≤
      height^2 * (fouvryTau (cs.length+3) m : ℝ)^2 := by
  let f := fun a => ‖blockBeta N c cs H δ j l key sigma a m‖
  let S := blockKeys N key
  have hf (a : κ) : 0 ≤ f a := norm_nonneg _
  have hsum : 0 ≤ ∑ a ∈ S,f a := Finset.sum_nonneg (fun a _ => hf a)
  calc
    _ ≤ ∑ a ∈ S,f a * (∑ b ∈ S,f b) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun b hb => hf b) ha) (hf a)
    _ = (∑ a ∈ S,f a)^2 := by rw [← Finset.sum_mul,pow_two]
    _ ≤ (height * (fouvryTau (cs.length+3) m : ℝ))^2 :=
      pow_le_pow_left₀ hsum (block_norm_sum_le N c cs H δ j l m key sigma hh hs) 2
    _ = _ := mul_pow _ _ _

/-- Both moment bounds hold for every finite set on the complete beta
scale. Their fixed order depends on the original tail length only. -/
theorem block_moments_le (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (key : (ℕ × ℕ) → κ) (sigma : (ℕ × ℕ) → ℂ) {height X : ℝ}
    (hh : 0 ≤ height) (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height)
    (hX : 1 ≤ X) (S : Finset ℕ) (hS : S ⊆ Finset.Ioc 0 ⌊X⌋₊) :
    (∑ a ∈ blockKeys N key,∑ m ∈ S,‖blockBeta N c cs H δ j l key sigma a m‖) ≤
        height * X * (1+Real.log X)^(cs.length+2) ∧
    (∑ a ∈ blockKeys N key,∑ m ∈ S,‖blockBeta N c cs H δ j l key sigma a m‖^2) ≤
        height^2 * X * (1+Real.log X)^((cs.length+3)^2-1) := by
  have hfirst : (∑ m ∈ S,(fouvryTau (cs.length+3) m : ℝ)) ≤
      X*(1+Real.log X)^(cs.length+2) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun m _ _ => Nat.cast_nonneg _)).trans
    simpa only [show cs.length+3-1 = cs.length+2 by omega] using
      sum_fouvryTau_le_real (k:=cs.length+3) (by omega) hX
  have hsecond : (∑ m ∈ S,(fouvryTau (cs.length+3) m : ℝ)^2) ≤
      X*(1+Real.log X)^((cs.length+3)^2-1) := by
    apply sum_alpha_sq_le_fouvryTau (k:=cs.length+3) (by omega) hX S hS
      (fun m => (fouvryTau (cs.length+3) m : ℝ))
    intro m hm
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
  constructor
  · rw [Finset.sum_comm]
    calc
      _ ≤ ∑ m ∈ S,height*(fouvryTau (cs.length+3) m : ℝ) :=
        Finset.sum_le_sum (fun m hm => block_norm_sum_le N c cs H δ j l m key sigma hh hs)
      _ = height*(∑ m ∈ S,(fouvryTau (cs.length+3) m : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfirst hh
  · rw [Finset.sum_comm]
    calc
      _ ≤ ∑ m ∈ S,height^2*(fouvryTau (cs.length+3) m : ℝ)^2 :=
        Finset.sum_le_sum (fun m hm => block_square_sum_le N c cs H δ j l m key sigma hh hs)
      _ = height^2*(∑ m ∈ S,(fouvryTau (cs.length+3) m : ℝ)^2) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hsecond (sq_nonneg height)

/-- The actual joint hat support supplies the padded natural cap. These
are already SUMMED family norms, not one bound per pair or per block. -/
theorem actual_block_raw_norms (N c : ℕ) (cs : List ℕ) (H : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    (hV : 1 ≤ lower δ l) (key : (ℕ × ℕ) → κ) (sigma : (ℕ × ℕ) → ℂ)
    {height : ℝ} (hh : 0 ≤ height)
    (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) :
    let S := jointRetainedProducts N c cs H δ j l
    let P := Nat.floor (2*lower δ l)
    (∑ a ∈ blockKeys N key,rowMass S (blockBeta N c cs H δ j l key sigma a)) ≤
      height*(2*lower δ l)*(1+Real.log (2*lower δ l))^(cs.length+2) ∧
    (∑ a ∈ blockKeys N key,
      rowEnergy (paddedRow S (blockBeta N c cs H δ j l key sigma a)) 0 P) ≤
      height^2*(2*lower δ l)*(1+Real.log (2*lower δ l))^((cs.length+3)^2-1) := by
  let S := jointRetainedProducts N c cs H δ j l
  have hS := jointRetainedProducts_subset_cap N c cs H hδ hwidth j l
  have hSIoc : S ⊆ Finset.Ioc 0 (Nat.floor (2*lower δ l)) := by
    intro m hm
    exact Finset.mem_Ioc.mpr (Finset.mem_Icc.mp (hS hm))
  have hnorm := block_moments_le N c cs H δ j l key sigma hh hs
    (by linarith : 1 ≤ 2*lower δ l) S hSIoc
  constructor
  · exact hnorm.1
  · simp_rw [paddedRow_energy _ _ _ hS]
    exact hnorm.2

/-- Quotient projectors are applied after constructing the original
modulus-independent rows; summed energy still contracts. -/
theorem actual_block_masked_energy (N c : ℕ) (cs : List ℕ) (H : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    (hV : 1 ≤ lower δ l) (key : (ℕ × ℕ) → κ) (sigma : (ℕ × ℕ) → ℂ)
    {height : ℝ} (hh : 0 ≤ height)
    (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) (k : ℕ) :
    (∑ a ∈ blockKeys N key,
      rowEnergy (unitMask k (paddedRow (jointRetainedProducts N c cs H δ j l)
        (blockBeta N c cs H δ j l key sigma a))) 0 (Nat.floor (2*lower δ l))) ≤
      height^2*(2*lower δ l)*(1+Real.log (2*lower δ l))^((cs.length+3)^2-1) := by
  apply (Finset.sum_le_sum (fun a ha => unitMask_energy_le k _ _ _)).trans
  exact (actual_block_raw_norms N c cs H hδ hwidth j l hV key sigma hh hs).2

end
end ImbalancedChen.P2GammaJointComplementBlockNorms
