import ImbalancedChen.P2OriginalW2CountTupleReindex
import ImbalancedChen.P2EnhancedLowerPrimeChildGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual finite ordinary child constructor is identified with the
original half-open prime window, with its lower endpoint retained as a
separate finite fibre. W1 uses the original d*N mask. W2 uses the original
N mask and has an additional, disjoint p | d lane. Nothing here discards
either lane, pays it again, or supplies an old H/h analytic licence.
-/

namespace ImbalancedChen.P2OriginalSingleChildWindowDictionary
noncomputable section
open Finset Set Wu2008DoubleSieve
open scoped Classical BigOperators
open P5OriginalActionMassBound P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalPrefixMaskMass

/-- Exact conversion of the relative logarithm, including both endpoints. -/
theorem relativePrime_window {Q : ℝ} {old : List ℕ} {p : ℕ}
    (hR : 1 < residualLevel Q old) (hp : 0 < p) (lo hi : ℝ) :
    (lo ≤ relativePrime Q old p ∧ relativePrime Q old p < hi) ↔
      (residualLevel Q old)^lo ≤ (p : ℝ) ∧ (p : ℝ) < (residualLevel Q old)^hi := by
  have hR0 : 0 < residualLevel Q old := zero_lt_one.trans hR
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hlog : 0 < Real.log (residualLevel Q old) := Real.log_pos hR
  have hl := Real.log_le_log_iff (Real.rpow_pos_of_pos hR0 lo) hp0
  have hh := Real.log_lt_log_iff hp0 (Real.rpow_pos_of_pos hR0 hi)
  rw [Real.log_rpow hR0] at hl hh
  unfold relativePrime
  rw [le_div_iff₀ hlog, div_lt_iff₀ hlog]
  exact and_congr hl hh

theorem relativePrime_eq_lower {Q : ℝ} {old : List ℕ} {p : ℕ}
    (hR : 1 < residualLevel Q old) (hp : 0 < p) (lo : ℝ) :
    relativePrime Q old p = lo ↔ (p : ℝ) = (residualLevel Q old)^lo := by
  have hR0 : 0 < residualLevel Q old := zero_lt_one.trans hR
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hlog : Real.log (residualLevel Q old) ≠ 0 := (Real.log_pos hR).ne'
  unfold relativePrime
  rw [div_eq_iff hlog]
  rw [← Real.log_rpow hR0]
  constructor
  · exact Real.log_injOn_pos hp0 (Real.rpow_pos_of_pos hR0 lo)
  · intro h
    rw [h]

/-- Product and enumeration cap are consequences of a strict relative
upper endpoint at most one; neither is a new source-licence premise. -/
theorem single_window_support {N p : ℕ} {Q chi hi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hp : p.Prime)
    (hu : relativePrime Q old p < hi) (hhi : hi ≤ 1) :
    ((parentProduct old*p : ℕ) : ℝ) < Q ∧ p < N := by
  have hlogs := parentWindow_logs hw
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hd0 : (0 : ℝ) < parentProduct old := Nat.cast_pos.mpr hw.2.1
  have hd1 : (1 : ℝ) ≤ parentProduct old := by
    exact_mod_cast (show 1 ≤ parentProduct old by omega)
  have hlog : Real.log (p : ℝ) < Real.log (residualLevel Q old) := by
    have h := (div_lt_iff₀ (Real.log_pos hlogs.2.1)).mp (hu.trans_le hhi)
    simpa only [one_mul] using h
  have hpR : (p : ℝ) < residualLevel Q old :=
    (Real.log_lt_log_iff hp0 (zero_lt_one.trans hlogs.2.1)).mp hlog
  have hprod : ((parentProduct old*p : ℕ) : ℝ) < Q := by
    have h := (lt_div_iff₀ hd0).mp hpR
    simpa only [Nat.cast_mul, mul_comm] using h
  refine ⟨hprod, ?_⟩
  have hcap : (p : ℝ) < N := by
    have hprod' : (parentProduct old : ℝ)*(p : ℝ) < (N : ℝ) :=
      hprod.trans_le hw.2.2.2.1
    nlinarith
  exact_mod_cast hcap

/-- The private general bridge is instantiated below with literal W1/W2
domain definitions. Its `hdom` input is only a definitional domain equality. -/
private theorem single_image_window {N : ℕ} {Q chi lo hi : ℝ}
    {old : List ℕ} (rule : SingleRule) (hw : parentWindow N Q old chi)
    (hhi : hi ≤ 1) (hc : physicalLevel N Q old*hi ≤ chi)
    (hdom : ∀ p, singleDomain rule Q old p ↔
      lo < relativePrime Q old p ∧ relativePrime Q old p < hi) :
    (singleChildren rule N Q old chi).image Fin.val =
      (primeWindow (parentProduct old*N) ((residualLevel Q old)^lo)
        ((residualLevel Q old)^hi)).filter (fun p => lo < relativePrime Q old p) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    have h := mem_singleChildren.mp hq
    have hd := (hdom q.val).mp h.2.2.1
    have hwin := (relativePrime_window (parentWindow_logs hw).2.1 h.1.1.pos lo hi).mp
      ⟨hd.1.le,hd.2⟩
    exact mem_filter.mpr ⟨mem_primeWindow.mpr
      ⟨h.1.1, by simpa only [Nat.mul_comm] using h.1.2, hwin⟩, hd.1⟩
  · intro hp
    obtain ⟨hp,hlo⟩ := mem_filter.mp hp
    have h := mem_primeWindow.mp hp
    have hx := (relativePrime_window (parentWindow_logs hw).2.1 h.1.pos lo hi).mpr h.2.2
    have hs := single_window_support hw h.1 hx.2 hhi
    let q : Fin (N+1) := ⟨p, by omega⟩
    refine mem_image.mpr ⟨q, ?_, rfl⟩
    apply mem_singleChildren.mpr
    refine ⟨⟨h.1, by simpa only [Nat.mul_comm] using h.2.1⟩, hw,
      (hdom p).mpr ⟨hlo,hx.2⟩, ?_, hs.1⟩
    have hh := mul_lt_mul_of_pos_left hx.2 (parentWindow_logs hw).2.2
    rw [relativePrime_physical hw] at hh
    exact hh.trans_le hc

/-- Endpoint fibres are genuine finite sums, even for a signed history test. -/
private theorem single_window_sum {N : ℕ} {Q chi lo hi : ℝ}
    {old : List ℕ} (rule : SingleRule) (hw : parentWindow N Q old chi)
    (hhi : hi ≤ 1) (hc : physicalLevel N Q old*hi ≤ chi)
    (hdom : ∀ p, singleDomain rule Q old p ↔
      lo < relativePrime Q old p ∧ relativePrime Q old p < hi)
    (F : ℕ → ℝ) :
    (∑ p ∈ primeWindow (parentProduct old*N) ((residualLevel Q old)^lo)
      ((residualLevel Q old)^hi), F p) =
      (∑ p ∈ singleChildren rule N Q old chi, F p.val) +
      ∑ p ∈ (primeWindow (parentProduct old*N) ((residualLevel Q old)^lo)
        ((residualLevel Q old)^hi)).filter
        (fun p => (p : ℝ) = (residualLevel Q old)^lo), F p := by
  have hi' := single_image_window rule hw hhi hc hdom
  have hs : (∑ p ∈ singleChildren rule N Q old chi, F p.val) =
      ∑ p ∈ (primeWindow (parentProduct old*N) ((residualLevel Q old)^lo)
        ((residualLevel Q old)^hi)).filter (fun p => lo < relativePrime Q old p), F p := by
    rw [← hi']
    exact (sum_image (fun a _ b _ h => Fin.ext h)).symm
  rw [hs]
  simp only [sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have h := mem_primeWindow.mp hp
  have hx := (relativePrime_window (parentWindow_logs hw).2.1 h.1.pos lo hi).mpr h.2.2
  have he := relativePrime_eq_lower (parentWindow_logs hw).2.1 h.1.pos lo
  by_cases ho : lo < relativePrime Q old p
  · have hn : (p : ℝ) ≠ (residualLevel Q old)^lo := by
      intro hp'
      have hx' := he.mpr hp'
      linarith
    simp only [if_pos ho, if_neg hn, add_zero]
  · have hp' : (p : ℝ) = (residualLevel Q old)^lo := he.mp (by linarith)
    simp only [if_neg ho, if_pos hp', zero_add]

/-- W1: the complete original d*N half-open childWindow equals the
production child sum plus its exact lower endpoint. The ceiling test is
the original parent cutoff test, with its actual residual physical level. -/
theorem W1_childWindow_sum {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (i : Fin 7) (j : Fin 10)
    (hc : physicalLevel N Q old/W1Target i ≤ chi) (F : ℕ → ℝ) :
    (∑ p ∈ P2EnhancedActualBuchstabTransfer.childWindow N (parentProduct old) Q
      (W1Target i) (W1Anchor j), F p) =
      (∑ p ∈ singleChildren (.w1 i j) N Q old chi, F p.val) +
      ∑ p ∈ (P2EnhancedActualBuchstabTransfer.childWindow N (parentProduct old) Q
        (W1Target i) (W1Anchor j)).filter
        (fun p => (p : ℝ) = cutoff Q (parentProduct old) (W1Anchor j)), F p := by
  have ht : (2 : ℝ) ≤ W1Target i := by
    have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    dsimp [W1Target]
    linarith
  have hhi : 1/W1Target i ≤ (1 : ℝ) :=
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) ht).trans (by norm_num)
  simpa only [P2EnhancedActualBuchstabTransfer.childWindow, cutoff, residualLevel,
    mul_one_div] using single_window_sum (.w1 i j) hw hhi
      (by simpa only [mul_one_div] using hc) (fun _ => Iff.rfl) F

def W2Upper (bank : Fin 36) : Fin 3 → ℝ :=
  ![(originalW2At bank).s, (originalW2At bank).phi2, (originalW2At bank).phi3]

theorem W2Upper_order (bank : Fin 36) (piece : Fin 3) :
    2 ≤ (originalW2At bank).s ∧ (originalW2At bank).s ≤ W2Upper bank piece := by
  obtain ⟨hs,h3,h2,h1,h0,h5⟩ :=
    P2AllW2SameQRawCountAction.original_W2_order _ (originalW2At_mem bank)
  refine ⟨hs,?_⟩
  fin_cases piece <;> simp only [W2Upper, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] <;> linarith

/-- W2 singleton: retained N-window = strict child + fresh lower
endpoint + old-prefix repeat. The repeat test is p | old.prod, not p=q. -/
theorem W2_singleton_window_sum {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (bank : Fin 36) (piece : Fin 3)
    (hc : physicalLevel N Q old/(originalW2At bank).s ≤ chi) (F : ℕ → ℝ) :
    (∑ p ∈ primeWindow N (cutoff Q (parentProduct old) (originalW2At bank).s0)
      (cutoff Q (parentProduct old) (W2Upper bank piece)), F p) =
      (∑ p ∈ singleChildren (.w2 bank piece) N Q old chi, F p.val) +
      (∑ p ∈ (primeWindow (parentProduct old*N)
        (cutoff Q (parentProduct old) (originalW2At bank).s0)
        (cutoff Q (parentProduct old) (W2Upper bank piece))).filter
          (fun p => (p : ℝ) = cutoff Q (parentProduct old) (originalW2At bank).s0), F p) +
      ∑ p ∈ (primeWindow N (cutoff Q (parentProduct old) (originalW2At bank).s0)
        (cutoff Q (parentProduct old) (W2Upper bank piece))).filter
          (fun p => p ∣ parentProduct old), F p := by
  have ho := W2Upper_order bank piece
  have hs0 : 0 < (originalW2At bank).s := by linarith [ho.1]
  have hrec := one_div_le_one_div_of_le hs0 ho.2
  have hhi : 1/W2Upper bank piece ≤ (1 : ℝ) :=
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (ho.1.trans ho.2)).trans (by norm_num)
  have hcap : physicalLevel N Q old*(1/W2Upper bank piece) ≤ chi := by
    have hh := mul_le_mul_of_nonneg_left hrec (parentWindow_logs hw).2.2.le
    exact hh.trans (by simpa only [mul_one_div] using hc)
  have hd (p : ℕ) : singleDomain (.w2 bank piece) Q old p ↔
      1/(originalW2At bank).s0 < relativePrime Q old p ∧
        relativePrime Q old p < 1/W2Upper bank piece := by
    fin_cases piece <;> rfl
  have hstrict := single_window_sum (.w2 bank piece) hw hhi hcap hd F
  have hsplit :
      (∑ p ∈ primeWindow N (cutoff Q (parentProduct old) (originalW2At bank).s0)
        (cutoff Q (parentProduct old) (W2Upper bank piece)), F p) =
        (∑ p ∈ primeWindow (parentProduct old*N)
          (cutoff Q (parentProduct old) (originalW2At bank).s0)
          (cutoff Q (parentProduct old) (W2Upper bank piece)), F p) +
        ∑ p ∈ (primeWindow N (cutoff Q (parentProduct old) (originalW2At bank).s0)
          (cutoff Q (parentProduct old) (W2Upper bank piece))).filter
            (fun p => p ∣ parentProduct old), F p := by
    rw [primeWindow_prefixMask]
    simp only [sum_filter]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hp : p ∣ parentProduct old <;> simp [hp]
  rw [hsplit]
  simpa only [cutoff, residualLevel] using congrArg
    (fun x => x + ∑ p ∈ (primeWindow N (cutoff Q (parentProduct old) (originalW2At bank).s0)
      (cutoff Q (parentProduct old) (W2Upper bank piece))).filter
        (fun p => p ∣ parentProduct old), F p) hstrict

end
end ImbalancedChen.P2OriginalSingleChildWindowDictionary
