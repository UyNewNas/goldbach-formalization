import ImbalancedChen.Part3OriginalInversePairRectangle
import ImbalancedChen.Part3OriginalShortIntervalLayers

/-! The modulus mean of the original inverse-residue short sums in (4.30).
The two prefix endpoints may vary even with the modulus. -/
namespace ImbalancedChen.Part3.OriginalInverseShortMean20261113
noncomputable section
open Finset
open scoped BigOperators
open OriginalSmoothPoissonTail OriginalInverseShortSums20261113 OriginalShortIntervalLayers20261113
open OriginalInversePairRectangle20261113 IntervalHarmonicPairBoundSourceOnly

/-- The (4.30) arithmetic mean on an arbitrary dyadic subset, with an
explicit cost for both lengths and no epsilon or phase dependent constant. -/
theorem dyadic_mean (L : Finset ℕ+) {K : ℝ} (hK : 1≤K)
    (level : ∀ k ∈ L, K≤(k.val:ℝ) ∧ (k.val:ℝ)≤2*K)
    (M N : ℕ) (a b c d : ℕ+ → ℕ)
    (length₁ : ∀ k ∈ L, a k≤b k ∧ b k-a k≤M)
    (length₂ : ∀ k ∈ L, c k≤d k ∧ d k-c k≤N) (ω : ℝ) :
    (∑ k ∈ L, inverseShortMean k (Ico (a k) (b k)) (Ico (c k) (d k)) ω) ≤
      6000*(1+Real.log (1+12*K))*
        (K*(M:ℝ)*(N:ℝ)+K^2*(harmonic M:ℝ)*(harmonic N:ℝ)) := by
  classical
  let cap := ⌊2*K⌋₊+1
  let U := (L ×ˢ range cap).filter (fun p => p.2<p.1.val ∧ Nat.Coprime p.2 p.1.val)
  let x (p : ℕ+ × ℕ) := (p.2:ℝ)/(p.1.val:ℝ)+ω
  let y (p : ℕ+ × ℕ) := (inverseResidue p.1.val p.2:ℝ)/(p.1.val:ℝ)-ω
  let V (p : ℕ+ × ℕ) := ‖shortSum (Ico (a p.1) (b p.1)) (x p)‖
  let W (p : ℕ+ × ℕ) := ‖shortSum (Ico (c p.1) (d p.1)) (y p)‖
  have key (p) (hp : p∈U) : p.1∈L := (mem_product.mp (mem_filter.mp hp).1).1
  have unit (p) (hp : p∈U) : p.2<p.1.val ∧ Nat.Coprime p.2 p.1.val := (mem_filter.mp hp).2
  have start : (∑ k ∈ L, inverseShortMean k (Ico (a k) (b k)) (Ico (c k) (d k)) ω) =
      ∑ p ∈ U, V p*W p := by
    dsimp only [U]
    rw [sum_filter,sum_product]
    apply sum_congr rfl
    intro k hk
    have kcap : k.val ≤ ⌊2*K⌋₊ := Nat.le_floor (level k hk).2
    have same : (range cap).filter (fun u => u<k.val ∧ Nat.Coprime u k.val) =
        (range k.val).filter (fun u => Nat.Coprime u k.val) := by
      ext u
      simp only [mem_filter,mem_range,cap]
      omega
    unfold inverseShortMean
    rw [←same,sum_filter] <;> rfl
  let I := Icc 1 M
  let J := Icc 1 N
  let box (i j : ℕ) := U.filter (fun p => i≤⌈V p⌉₊ ∧ j≤⌈W p⌉₊)
  let C := 6000*(1+Real.log (1+12*K))
  have layers (p) (hp : p∈U) : V p*W p ≤
      ∑ i ∈ I, ∑ j ∈ J, layer i (V p)*layer j (W p) := by
    obtain ⟨hl₁,hl₂⟩ := length₁ _ (key p hp)
    obtain ⟨hr₁,hr₂⟩ := length₂ _ (key p hp)
    rw [←sum_mul_sum]
    exact mul_le_mul (layer_cover hl₁ hl₂ (x p)) (layer_cover hr₁ hr₂ (y p)) (norm_nonneg _)
      (sum_nonneg (fun i _ => layer_nonneg i _))
  have count (i j : ℕ) : (∑ p ∈ U, layer i (V p)*layer j (W p))=((box i j).card:ℝ) := by
    have eq (p) : layer i (V p)*layer j (W p) =
        (if i≤⌈V p⌉₊ ∧ j≤⌈W p⌉₊ then (1:ℝ) else 0) := by
      by_cases hi : i≤⌈V p⌉₊ <;> by_cases hj : j≤⌈W p⌉₊ <;> simp [layer,hi,hj]
    simp only [eq,←sum_filter,sum_const,nsmul_eq_mul,mul_one,box]
  have one (i) (hi : i∈I) (j) (hj : j∈J) :
      ((box i j).card:ℝ) ≤ C*(K+K^2*(1/(j:ℝ))*(1/(i:ℝ))) := by
    have hI := (mem_Icc.mp hi).1
    have hJ := (mem_Icc.mp hj).1
    have ir : (1:ℝ) ≤ i := by exact_mod_cast hI
    have jr : (1:ℝ) ≤ j := by exact_mod_cast hJ
    have le1 {t : ℝ} (ht : 1≤t) : 1/t≤1 :=
      (div_le_iff₀ (zero_lt_one.trans_le ht)).mpr (by simpa only [one_mul] using ht)
    exact rectangle_card (box i j) hK (by positivity) (by positivity) (le1 jr) (le1 ir)
      ω (fun p => nearest (y p)) (fun p => nearest (x p))
      (fun p hp => level _ (key p (mem_filter.mp hp).1)) (fun p hp => unit _ (mem_filter.mp hp).1)
      (fun p hp => short_arc (y p) (length₂ _ (key p (mem_filter.mp hp).1)).1 hJ (mem_filter.mp hp).2.2)
      (fun p hp => short_arc (x p) (length₁ _ (key p (mem_filter.mp hp).1)).1 hI (mem_filter.mp hp).2.1)
  have last : (∑ i ∈ I, ∑ j ∈ J, C*(K+K^2*(1/(j:ℝ))*(1/(i:ℝ)))) =
      C*(K*(M:ℝ)*(N:ℝ)+K^2*(harmonic M:ℝ)*(harmonic N:ℝ)) := by
    have inner (i : ℕ) : (∑ j ∈ J, C*(K+K^2*(1/(j:ℝ))*(1/(i:ℝ)))) =
        (N:ℝ)*(C*K)+(C*K^2*(1/(i:ℝ)))*(harmonic N:ℝ) := by
      simp_rw [show ∀ j : ℕ, C*(K+K^2*(1/(j:ℝ))*(1/(i:ℝ))) =
        C*K+(C*K^2*(1/(i:ℝ)))*(1/(j:ℝ)) from fun _ => by ring]
      rw [sum_add_distrib,←Finset.mul_sum J (fun j : ℕ => 1/(j:ℝ)) (C*K^2*(1/(i:ℝ)))]
      simp only [J,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,real_reciprocal_sum_eq_harmonic]
    simp_rw [inner]
    rw [sum_add_distrib,←Finset.sum_mul I (fun i : ℕ => C*K^2*(1/(i:ℝ))) (harmonic N:ℝ),
      ←Finset.mul_sum I (fun i : ℕ => 1/(i:ℝ)) (C*K^2)]
    simp only [I,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,real_reciprocal_sum_eq_harmonic]
    ring
  rw [start]
  calc
    _ ≤ ∑ p ∈ U, ∑ i ∈ I, ∑ j ∈ J, layer i (V p)*layer j (W p) := sum_le_sum layers
    _ = ∑ i ∈ I, ∑ j ∈ J, ∑ p ∈ U, layer i (V p)*layer j (W p) := by
      rw [sum_comm (s := U) (t := I)]
      exact sum_congr rfl (fun _ _ => sum_comm)
    _ = ∑ i ∈ I, ∑ j ∈ J, ((box i j).card:ℝ) := by simp only [count]
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, C*(K+K^2*(1/(j:ℝ))*(1/(i:ℝ))) :=
      sum_le_sum (fun i hi => sum_le_sum (one i hi))
    _ = _ := last

end
end ImbalancedChen.Part3.OriginalInverseShortMean20261113
