import ImbalancedChen.P5U7OriginalSourceMass
import ImbalancedChen.ChenInitialCorrectionBudget

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual terminal prime window differs from the inclusive PNT prefix
only by its lower wall, one possible strict upper endpoint, and actual
prime divisors of the target N. No rough-number unit is counted as prime.
-/
namespace ImbalancedChen
noncomputable section
open LiLiuPrereqBuchstab
open Classical

/-- Finite prefix coverage retaining the target exclusion and both walls. -/
theorem p5U7TerminalPrime_prefix_cover (N a ell : ℕ) (ha : 0 < a) (hN : 0 < N) :
    Nat.primesLE (Nat.floor ((N : ℝ) / (a : ℝ))) ⊆
      ((p5U7MassPrimeFibre N a ell ∪ Finset.range ell) ∪
        {Nat.floor ((N : ℝ) / (a : ℝ))}) ∪ N.primeFactors := by
  intro q hq
  obtain ⟨hqx, hp⟩ := Nat.mem_primesLE.mp hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hx0 : 0 ≤ (N : ℝ) / (a : ℝ) := div_nonneg (Nat.cast_nonneg _) haR.le
  have hqxR : (q : ℝ) ≤ (N : ℝ) / (a : ℝ) := (Nat.le_floor_iff hx0).mp hqx
  by_cases hlow : q < ell
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_range.mpr hlow)))
  by_cases htop : a * q < N
  · by_cases hcop : Nat.Coprime q N
    · have hqN : q < N := (Nat.le_mul_of_pos_left q ha).trans_lt htop
      have hf : q ∈ p5U7MassPrimeFibre N a ell := Finset.mem_filter.mpr
        ⟨mem_chenAdditivePrimeCarrier.mpr ⟨hqN,hp,hcop⟩,by omega,htop⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hf))
    · have hd : q ∣ N := by
        by_contra hn
        exact hcop (hp.coprime_iff_not_dvd.mpr hn)
      exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp,hd,hN.ne'⟩)
  · have hge : N ≤ a * q := by omega
    have hgeR : (N : ℝ) ≤ (a : ℝ) * q := by exact_mod_cast hge
    have hEq : (q : ℝ) = (N : ℝ) / (a : ℝ) := by
      apply le_antisymm hqxR
      exact (div_le_iff₀ haR).mpr (by nlinarith only [hgeR])
    have hfloor : q = Nat.floor ((N : ℝ) / (a : ℝ)) := by rw [← hEq]; simp
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa using hfloor))

/-- No absolute constant or target-prime loss is silently discarded. -/
theorem p5U7TerminalPrime_prefix_gap (N a ell : ℕ) (ha : 0 < a) (hN : 0 < N) :
    0 ≤ primePi ((N : ℝ) / (a : ℝ)) - ((p5U7MassPrimeFibre N a ell).card : ℝ) ∧
      primePi ((N : ℝ) / (a : ℝ)) - ((p5U7MassPrimeFibre N a ell).card : ℝ) ≤
        (ell : ℝ) + 1 + (N.primeFactors.card : ℝ) := by
  have hcover := Finset.card_le_card (p5U7TerminalPrime_prefix_cover N a ell ha hN)
  have h1 := Finset.card_union_le
    ((p5U7MassPrimeFibre N a ell ∪ Finset.range ell) ∪
      {Nat.floor ((N : ℝ) / (a : ℝ))}) N.primeFactors
  have h2 := Finset.card_union_le (p5U7MassPrimeFibre N a ell ∪ Finset.range ell)
    ({Nat.floor ((N : ℝ) / (a : ℝ))} : Finset ℕ)
  have h3 := Finset.card_union_le (p5U7MassPrimeFibre N a ell) (Finset.range ell)
  simp only [Finset.card_range, Finset.card_singleton] at h1 h2 h3
  have hcard : (Nat.primesLE (Nat.floor ((N : ℝ) / (a : ℝ)))).card ≤
      (p5U7MassPrimeFibre N a ell).card + ell + 1 + N.primeFactors.card := by omega
  rw [Nat.primesLE_card_eq_primeCounting] at hcard
  have hcast : primePi ((N : ℝ) / (a : ℝ)) ≤
      ((p5U7MassPrimeFibre N a ell).card : ℝ) + (ell : ℝ) + 1 +
        (N.primeFactors.card : ℝ) := by exact_mod_cast hcard
  exact ⟨sub_nonneg.mpr (p5U7Mass_primeFibre_card_le_primePi N a ell ha), by linarith only [hcast]⟩

/-- An actual PNT error plus the exact finite deleted-prefix payment. -/
theorem p5U7TerminalPrime_abs_error (N a ell : ℕ) (ha : 0 < a) (hN : 0 < N)
    {Y : ℝ} (hY : primeErrorStart ≤ Y) (hYx : Y ≤ (N : ℝ) / (a : ℝ)) :
    |((p5U7MassPrimeFibre N a ell).card : ℝ) -
        ((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ))| ≤
      primeErrorEnvelope Y * (((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ))) +
        ((ell : ℝ) + 1 + (N.primeFactors.card : ℝ)) := by
  have hg := p5U7TerminalPrime_prefix_gap N a ell ha hN
  have he := primePi_error_le hY hYx
  have htri := abs_add_le
    (((p5U7MassPrimeFibre N a ell).card : ℝ) - primePi ((N : ℝ) / (a : ℝ)))
    (primePi ((N : ℝ) / (a : ℝ)) -
      ((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ)))
  rw [abs_of_nonpos (by linarith only [hg.1])] at htri
  have hid : ((p5U7MassPrimeFibre N a ell).card : ℝ) - primePi ((N : ℝ) / (a : ℝ)) +
      (primePi ((N : ℝ) / (a : ℝ)) -
        ((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ))) =
      ((p5U7MassPrimeFibre N a ell).card : ℝ) -
        ((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ)) := by ring
  rw [hid] at htri
  linarith only [htri,he,hg.2]
end
end ImbalancedChen

