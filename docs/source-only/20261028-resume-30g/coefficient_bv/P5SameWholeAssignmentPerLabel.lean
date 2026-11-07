import ImbalancedChen.P5ActualInnerPerLabelGamma

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Whole-word marked+rough ORIGINAL per-label tensor port. One independently
fixed occurrence partition is used both for the common Cartesian source
and for every coefficient. All marked slots enter the same convolution;
no marked product is hidden in the test. The original source scalar c,
original M_all, residual-rank beta choice and complete q are literal.

An actual source reconstruction must supply B/fullword/out. This finite
port is not an assumption of a desired source equality or SW licence.
-/

namespace ImbalancedChen.P5Z.SameWholeAssignmentPerLabel
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open ActualInnerPerLabelGamma ActualAll16UnrestrictedResidualConvolution

def support {ι : Type*} (B : ι → Finset ℕ) (word : List ι) : Finset ℕ :=
  (actualPrimeSlotBox B word).image List.prod

theorem support_rough {ι : Type*} (B : ι → Finset ℕ) (word : List ι) (w : ℝ)
    (hp : ∀ i ∈ word, ∀ p ∈ B i, Nat.Prime p)
    (hw : ∀ i ∈ word, ∀ p ∈ B i, w ≤ (p : ℝ))
    {d : ℕ} (hd : d ∈ support B word) : RoughPrimeSupportedAt w d := by
  obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hd
  have hprime := actualPrimeSlotBox_prime B word hp ps hps
  have hpos := List.prod_pos (fun p hp => (hprime p hp).pos)
  refine ⟨hpos.ne', ?_⟩
  intro p hp
  have hlist : p ∈ ps.prod.primeFactorsList := by
    apply List.mem_toFinset.mp
    simpa only [Nat.toFinset_factors] using hp
  have hperm := Nat.primeFactorsList_unique (rfl : ps.prod = ps.prod) hprime
  exact actualPrimeSlotBox_forall B word (fun p => w ≤ (p : ℝ)) hw ps hps p (hperm.mem_iff.mpr hlist)

def attachedSupport {ι : Type*} (B : ι → Finset ℕ) (word : List ι)
    (N cap : ℕ) (w : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w) (support B word)

def attachedGamma {ι : Type*} [DecidableEq ι] (B : ι → Finset ℕ) (word : List ι)
    (N cap r : ℕ) (w L : ℝ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w) (support B word) (gamma B word)
    (rawBetaWeight N cap r w L) (rawBetaWeight N cap r w L)

theorem attachedGamma_abs_le_one {ι : Type*} [DecidableEq ι]
    (B : ι → Finset ℕ) (word : List ι) (hnd : word.Nodup)
    (N cap r : ℕ) (w L : ℝ)
    (hp : ∀ i, ∀ p ∈ B i, Nat.Prime p)
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hw : ∀ i ∈ word, ∀ p ∈ B i, w ≤ (p : ℝ)) (q : ℕ) :
    |attachedGamma B word N cap r w L q| ≤ 1 := by
  by_cases hq : q ∈ attachedSupport B word N cap w
  · obtain ⟨⟨e, d⟩, hed, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
    exact abs_smallRoughRho_mul_le_one
      (fun e he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he)
      (fun d hd => support_rough B word w (fun i _ => hp i) hw hd)
      (gamma B word) _ _ (fun d _ => gamma_abs_le_one_of_nodup B word hnd hp hdis d)
      (fun e _ => raw_beta_abs_le_one N cap r w L e)
      (fun e _ => raw_beta_abs_le_one N cap r w L e) he hd
  · rw [attachedGamma, smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hq]
    norm_num

theorem attached_fullq_sum {ι : Type*} [DecidableEq ι]
    (B : ι → Finset ℕ) (word : List ι) (N cap r : ℕ) (w L : ℝ)
    (hp : ∀ i ∈ word, ∀ p ∈ B i, Nat.Prime p)
    (hw : ∀ i ∈ word, ∀ p ∈ B i, w ≤ (p : ℝ)) (H : ℕ → ℝ) :
    (∑ q ∈ attachedSupport B word N cap w, attachedGamma B word N cap r w L q * H q) =
      ∑ e ∈ actualSmallRosserSupport N cap w, ∑ d ∈ support B word,
        gamma B word d * rawBetaWeight N cap r w L e * H (e * d) := by
  rw [attachedSupport, attachedGamma, sum_smallRoughRho_mul
    (fun e he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he)
    (fun d hd => support_rough B word w hp hw hd)]
  rw [smallRoughPairs, Finset.sum_product]
  simp only [smallRoughPairCoefficient, signAttachedCoefficient, ite_self]

/-- Word-local one-bounds for the SAME complete marked+rough partition.
Actual source geometry, not rank exclusion, supplies the nodup fullword. -/
theorem same_assignment_one_bounds {ι : Type*} [DecidableEq ι]
    (B : ι → Finset ℕ) (word : List ι) (out : List ι × List ι × List ι)
    (hpart : (out.1 ++ out.2.1 ++ out.2.2).Perm word) (hnd : word.Nodup)
    (N cap r : ℕ) (w L : ℝ)
    (hp : ∀ i, ∀ p ∈ B i, Nat.Prime p)
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hw : ∀ i ∈ word, ∀ p ∈ B i, w ≤ (p : ℝ)) :
    (∀ a, |gamma B out.1 a| ≤ 1) ∧ (∀ b, |gamma B out.2.1 b| ≤ 1) ∧
      (∀ q3, |attachedGamma B out.2.2 N cap r w L q3| ≤ 1) := by
  obtain ⟨h1, h23, _⟩ := List.nodup_append.mp (hpart.nodup_iff.mpr hnd)
  obtain ⟨h2, h3, _⟩ := List.nodup_append.mp h23
  have hright : ∀ i ∈ out.2.2, ∀ p ∈ B i, w ≤ (p : ℝ) := by
    intro i hi p hp'
    apply hw i (hpart.mem_iff.mp ?_) p hp'
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hi)))
  exact ⟨gamma_abs_le_one_of_nodup B _ h1 hp hdis,
    gamma_abs_le_one_of_nodup B _ h2 hp hdis,
    attachedGamma_abs_le_one B _ h3 N cap r w L hp hdis hright⟩

/-- ORIGINAL per-label exact whole-word regrouping BEFORE beta. The
source scalar and all marked occurrences are retained exactly once. -/
theorem same_assignment_fixed_e {ι : Type*} [DecidableEq ι]
    (B : ι → Finset ℕ) (word : List ι) (out : List ι × List ι × List ι)
    (hpart : (out.1 ++ out.2.1 ++ out.2.2).Perm word)
    (c : ℝ) (e : ℕ) (H : ℕ → ℝ) :
    (c / (multiplicity word : ℝ)) * (∑ ps ∈ actualPrimeSlotBox B word, H (e * ps.prod)) =
      ∑ a ∈ support B out.1, ∑ b ∈ support B out.2.1, ∑ d ∈ support B out.2.2,
        (c * (multiplicity out.1 : ℝ) * (multiplicity out.2.1 : ℝ) *
          (multiplicity out.2.2 : ℝ) / (multiplicity word : ℝ)) *
            gamma B out.1 a * gamma B out.2.1 b * gamma B out.2.2 d * H (e * (a * b * d)) := by
  rw [actualPrimeSlotBox_product_sum_perm B hpart.symm,
    actualPrimeSlotBox_product_sum_append]
  simp_rw [actualPrimeSlotBox_product_sum_append, Finset.mul_sum]
  have h := three_group_sum_per_label B out.1 out.2.1 out.2.2
    (c / (multiplicity word : ℝ)) (fun n => H (e * n))
  calc
    _ = ∑ ps ∈ actualPrimeSlotBox B out.1, ∑ qs ∈ actualPrimeSlotBox B out.2.1,
        ∑ rs ∈ actualPrimeSlotBox B out.2.2,
          (c / (multiplicity word : ℝ)) * H (e * (ps.prod * qs.prod * rs.prod)) := by
      rfl
    _ = _ := by
      rw [h]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- Exact COMPLETE q tensor for an actual frozen whole-word partition.
The marked primes are inside a*b*q3; actual beta belongs only to q3.
No product test retains a native gate, owner predicate or marked prefix. -/
theorem same_assignment_beta_tensor {ι : Type*} [DecidableEq ι]
    (B : ι → Finset ℕ) (word : List ι) (out : List ι × List ι × List ι)
    (hpart : (out.1 ++ out.2.1 ++ out.2.2).Perm word)
    (N cap r : ℕ) (w L c : ℝ)
    (hp : ∀ i ∈ word, ∀ p ∈ B i, Nat.Prime p)
    (hw : ∀ i ∈ word, ∀ p ∈ B i, w ≤ (p : ℝ)) (H : ℕ → ℝ) :
    (∑ e ∈ actualSmallRosserSupport N cap w,
      (c * rawBetaWeight N cap r w L e / (multiplicity word : ℝ)) *
        (∑ ps ∈ actualPrimeSlotBox B word, H (e * ps.prod))) =
      ∑ a ∈ support B out.1, ∑ b ∈ support B out.2.1,
        ∑ q3 ∈ attachedSupport B out.2.2 N cap w,
          (c * (multiplicity out.1 : ℝ) * (multiplicity out.2.1 : ℝ) *
            (multiplicity out.2.2 : ℝ) / (multiplicity word : ℝ)) *
              gamma B out.1 a * gamma B out.2.1 b * attachedGamma B out.2.2 N cap r w L q3 *
                H (a * b * q3) := by
  have hright (P : ι → Prop) (hP : ∀ i ∈ word, P i) : ∀ i ∈ out.2.2, P i := by
    intro i hi
    apply hP i (hpart.mem_iff.mp ?_)
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hi)))
  simp_rw [same_assignment_fixed_e B word out hpart]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  have hpush := attached_fullq_sum B out.2.2 N cap r w L
    (hright _ hp) (hright _ hw) (fun q3 =>
      (c * (multiplicity out.1 : ℝ) * (multiplicity out.2.1 : ℝ) *
        (multiplicity out.2.2 : ℝ) / (multiplicity word : ℝ)) *
          gamma B out.1 a * gamma B out.2.1 b * H (a * b * q3))
  calc
    _ = ∑ e ∈ actualSmallRosserSupport N cap w, ∑ d ∈ support B out.2.2,
        gamma B out.2.2 d * rawBetaWeight N cap r w L e *
          ((c * (multiplicity out.1 : ℝ) * (multiplicity out.2.1 : ℝ) *
            (multiplicity out.2.2 : ℝ) / (multiplicity word : ℝ)) *
              gamma B out.1 a * gamma B out.2.1 b * H (a * b * (e * d))) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro d hd
      rw [show a * b * (e * d) = e * (a * b * d) by ring]
      ring
    _ = _ := by
      rw [← hpush]
      apply Finset.sum_congr rfl
      intro q3 hq3
      ring

end
end ImbalancedChen.P5Z.SameWholeAssignmentPerLabel
