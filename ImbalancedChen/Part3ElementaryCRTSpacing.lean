import ImbalancedChen.Part3ElementaryE1RealEndpoint
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Max

/-! SOURCE PROPOSAL ONLY -- UNCOMPILED -- HOLD.
Finite simultaneous divisibility/progression count at exact real endpoints.
No CRT representative is constructed and no coprimality is assumed.
-/

namespace ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment

noncomputable section
open Finset

/-- A common integer residue and d-divisibility force lcm(d,q) spacing.
The real support may start below zero; empty sets and zero length are allowed. -/
theorem card_real_supported_modEq_dvd_le_lcm (S : Finset ℕ) {a b : ℝ}
    {q d : ℕ} {r : ℤ} (hab : a ≤ b) (hq : 0 < q) (hd : 0 < d)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b)
    (hmod : ∀ n ∈ S, Int.ModEq (q : ℤ) (n : ℤ) r)
    (hdiv : ∀ n ∈ S, d ∣ n) :
    (S.card : ℝ) ≤ (b - a) / (Nat.lcm d q : ℝ) + 1 := by
  classical
  by_cases hne : S.Nonempty
  · let n0 : ℕ := S.min' hne
    have hn0 : n0 ∈ S := Finset.min'_mem S hne
    have hmin : ∀ n ∈ S, n0 ≤ n := by
      intro n hn
      exact Finset.min'_le S n hn
    let T : Finset ℕ := S.image (fun n => n - n0)
    have hT : ∀ t ∈ T, (0 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ b - a := by
      intro t ht
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
      constructor
      · exact Nat.cast_nonneg _
      · rw [Nat.cast_sub (hmin n hn)]
        linarith [(hS n hn).2, (hS n0 hn0).1]
    have hTd : ∀ t ∈ T, Nat.lcm d q ∣ t := by
      intro t ht
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
      have hqdiff : (q : ℤ) ∣ (n : ℤ) - (n0 : ℤ) :=
        ((hmod n0 hn0).trans (hmod n hn).symm).dvd
      have hqnat : q ∣ n - n0 := by
        apply Int.natCast_dvd_natCast.mp
        rw [Int.natCast_sub (hmin n hn)]
        exact hqdiff
      exact Nat.lcm_dvd (Nat.dvd_sub (hdiv n hn) (hdiv n0 hn0)) hqnat
    have hcard : T.card = S.card := by
      dsimp only [T]
      apply Finset.card_image_of_injOn
      intro n hn m hm hnm
      calc
        n = (n - n0) + n0 := (Nat.sub_add_cancel (hmin n hn)).symm
        _ = (m - n0) + n0 := congrArg (fun t : ℕ => t + n0) hnm
        _ = m := Nat.sub_add_cancel (hmin m hm)
    have hfilter : T.filter (fun t => Nat.lcm d q ∣ t) = T :=
      Finset.filter_eq_self.mpr hTd
    have hcount := real_supported_multiples_card_le T
      (a := (0 : ℝ)) (b := b - a) (d := Nat.lcm d q)
      (le_refl 0) (sub_nonneg.mpr hab) (Nat.lcm_pos hd hq) hT
    rw [hfilter, hcard] at hcount
    simpa only [sub_zero] using hcount
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hnonneg : (0 : ℝ) ≤ (b - a) / (Nat.lcm d q : ℝ) :=
      div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
    linarith

end
end ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment
