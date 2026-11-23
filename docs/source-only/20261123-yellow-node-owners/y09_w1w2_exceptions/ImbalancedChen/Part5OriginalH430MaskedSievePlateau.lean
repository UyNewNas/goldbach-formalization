import ImbalancedChen.Part5OriginalH430MonotoneSieveHeight
import ImbalancedChen.Part5OriginalH430ReceiptDirections

/-! Sieve and least-factor windows on actual original receipts. The outside
receiver retains the entire change of cutoff, with the original sign. -/
namespace ImbalancedChen.Part5OriginalH430MaskedSievePlateau
noncomputable section
open Finset Real Wu2008DoubleSieve
open P2EnhancedLowerPrimeChildCarriers (parentProduct)
open P2FrozenReceiverCountActions (frozen_selected_buchstab)
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430ReceiptFourBand Part5OriginalH430ReceiptDirections
open Part5OriginalH430MonotoneSieveHeight
open scoped Classical BigOperators

/-- The original quotient at its actual old prime, for any admitted additive label. -/
theorem quotient_on_root {N ell p B D : ℕ} (hp : 0<p) (hB : B=p*D) (hd : B∣N-ell) :
    (N-ell)/p = D*((N-ell)/B) := by
  apply Nat.eq_of_mul_eq_mul_left hp
  have hpB : p∣B := by rw [hB]; exact dvd_mul_right p D
  rw [Nat.mul_div_cancel' (hpB.trans hd),←Nat.mul_assoc,←hB,Nat.mul_div_cancel' hd]

theorem quotient_rough {N ell p B D : ℕ} (hp : 0<p) (hB : B=p*D)
    (hd : B∣N-ell) (hE : rootMask N p ell) : ChenPrimeRough ((N:ℝ)^a) ((N-ell)/B) := by
  intro q hq hqd
  apply hE.2 q hq
  rw [quotient_on_root hp hB hd]
  exact hqd.trans (dvd_mul_left _ _)

/-- Equality of additive-label carriers for both directions and arbitrary
further masks which keep the original root receipt. -/
theorem carriers_equal {N p B D : ℕ} {z w : ℝ} {P : ℕ → Prop}
    (hp : 0<p) (hB : B=p*D) (hP : ∀ell,P ell→rootMask N p ell)
    (hz : z≤(N:ℝ)^a) (hw : w≤(N:ℝ)^a) :
    (sieveCarrier N B (B*N) z).filter P = (sieveCarrier N B (B*N) w).filter P := by
  have sub (x y : ℝ) (hy : y≤(N:ℝ)^a) :
      (sieveCarrier N B (B*N) x).filter P ⊆ (sieveCarrier N B (B*N) y).filter P := by
    intro ell he
    obtain ⟨hd,hE⟩ := mem_filter.mp he
    obtain ⟨hr,hpr,hdv,_⟩ := mem_filter.mp hd
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hr,hpr,hdv,?_⟩,hE⟩
    intro q hq _ hlt hdiv
    exact (not_lt_of_ge (quotient_rough hp hB hdv (hP ell hE) q hq hdiv)) (hlt.trans_le hy)
  exact Subset.antisymm (sub z w hw) (sub w z hz)

theorem counts_equal {N p B D : ℕ} {z w : ℝ} {P : ℕ → Prop}
    (hp : 0<p) (hB : B=p*D) (hP : ∀ell,P ell→rootMask N p ell)
    (hz : z≤(N:ℝ)^a) (hw : w≤(N:ℝ)^a) : count N B P z = count N B P w := by
  rw [count_card,count_card,carriers_equal hp hB hP hz hw]

theorem small_divisor_labels_empty {N p B D ell : ℕ} {P : ℕ → Prop} {lo hi : ℝ}
    (hp : 0<p) (hB : B=p*D) (hP : ∀ell,P ell→rootMask N p ell) (hhi : hi≤(N:ℝ)^a)
    (he : ell∈(sieveCarrier N B (B*N) lo).filter P) :
    divisorsIn (primeWindow (B*N) lo hi) ((N-ell)/B) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hqwin,hqd⟩ := mem_filter.mp hq
  obtain ⟨hpr,_,_,htop⟩ := mem_primeWindow.mp hqwin
  have hlabel := mem_filter.mp he
  have hdv := (mem_filter.mp hlabel.1).2.2.1
  exact (not_lt_of_ge (quotient_rough hp hB hdv (hP ell hlabel.2) q hpr hqd)) (htop.trans_le hhi)

/-- The true signed first-factor window for every emitted Member equals
zero on each root-preserving receiver, before the marked sum. On the full
receiver its entire difference equals the difference on the original outside. -/
theorem member_window {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈originalBand N k) (ho : o∈rootHistory N n k t p) (P : ℕ → Prop)
    (hP : ∀ell,P ell→rootMask N p ell) {w : ℝ}
    (hw : w≤memberCutoff (rootQ N n k t p) o) :
    let z := memberCutoff (rootQ N n k t p) o
    let B := parentProduct o.current.old
    count N B P w = count N B P z ∧
      (∑ q∈primeWindow (B*N) w z, count N (B*q) P (q:ℝ)) = 0 ∧
      count N B (receiver N) w - count N B (receiver N) z =
        count N B (outsideReceipt N p) w - count N B (outsideReceipt N p) z := by
  dsimp only
  let B := parentProduct o.current.old
  let z := memberCutoff (rootQ N n k t p) o
  have hz : z≤(N:ℝ)^a := member_cutoff_le_original hN ht hu hn hp ho
  have hp' := (original_band_prime hp).1.pos
  have hB := member_product ho
  have hid : ∀ell,rootMask N p ell→rootMask N p ell := fun _ h => h
  have hmask := counts_equal hp' hB hid (hw.trans hz) hz
  have hrec := counts_equal hp' hB hP (hw.trans hz) hz
  have hb : count N B P w = count N B P z + ∑ q∈primeWindow (B*N) w z, count N (B*q) P (q:ℝ) := by
    exact_mod_cast frozen_selected_buchstab N B P hw
  refine ⟨hrec,by linarith only [hrec,hb],?_⟩
  rw [receiver_count_split N p B w,receiver_count_split N p B z,hmask]
  ring

end
end ImbalancedChen.Part5OriginalH430MaskedSievePlateau
