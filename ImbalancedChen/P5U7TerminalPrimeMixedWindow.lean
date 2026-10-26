import ImbalancedChen.P5U7TerminalPrimeFiniteWindow

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual original-target N exclusions with a genuinely INDEPENDENT product
cutoff M<=N. The prime carrier remains N everywhere. The finite prefix
loss retains the lower wall, strict upper endpoint and N.primeFactors.
-/
namespace ImbalancedChen
noncomputable section
open LiLiuPrereqBuchstab
open Classical

def p5U7MassPrimeWindow (N M a ell : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter fun q => ell ≤ q ∧ a*q < M

/-- The physical product wall is M while every excluded target prime is
still a divisor of the original N. -/
theorem p5U7MassPrimeWindow_subset_prefix (N M a ell : ℕ) (ha : 0 < a) :
    p5U7MassPrimeWindow N M a ell ⊆ Nat.primesLE (Nat.floor ((M : ℝ)/(a : ℝ))) := by
  intro q hq
  obtain ⟨hqc,_hwall,htop⟩ := Finset.mem_filter.mp hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hx0 : 0 ≤ (M : ℝ)/(a : ℝ) := div_nonneg (Nat.cast_nonneg _) haR.le
  have htopR : (a : ℝ)*(q : ℝ) < M := by exact_mod_cast htop
  have hqx : (q : ℝ) ≤ (M : ℝ)/(a : ℝ) :=
    ((lt_div_iff₀ haR).mpr (by nlinarith only [htopR])).le
  exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hx0).mpr hqx,
    (mem_chenAdditivePrimeCarrier.mp hqc).2.1⟩

theorem p5U7MassPrimeWindow_card_le_primePi (N M a ell : ℕ) (ha : 0 < a) :
    ((p5U7MassPrimeWindow N M a ell).card : ℝ) ≤ primePi ((M : ℝ)/(a : ℝ)) := by
  have hc := (Finset.card_le_card (p5U7MassPrimeWindow_subset_prefix N M a ell ha)).trans_eq
    (Nat.primesLE_card_eq_primeCounting _)
  change ((p5U7MassPrimeWindow N M a ell).card : ℝ) ≤
    (Nat.primeCounting (Nat.floor ((M : ℝ)/(a : ℝ))) : ℝ)
  exact_mod_cast hc

/-- Exact finite prefix coverage for the mixed target/cutoff window. -/
theorem p5U7TerminalPrimeMixed_prefix_cover (N M a ell : ℕ)
    (ha : 0 < a) (hN : 0 < N) (hMN : M ≤ N) :
    Nat.primesLE (Nat.floor ((M : ℝ)/(a : ℝ))) ⊆
      ((p5U7MassPrimeWindow N M a ell ∪ Finset.range ell) ∪
        {Nat.floor ((M : ℝ)/(a : ℝ))}) ∪ N.primeFactors := by
  intro q hq
  obtain ⟨hqx,hp⟩ := Nat.mem_primesLE.mp hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hx0 : 0 ≤ (M : ℝ)/(a : ℝ) := div_nonneg (Nat.cast_nonneg _) haR.le
  have hqxR : (q : ℝ) ≤ (M : ℝ)/(a : ℝ) := (Nat.le_floor_iff hx0).mp hqx
  by_cases hlow : q < ell
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_range.mpr hlow)))
  by_cases htop : a*q < M
  · by_cases hcop : Nat.Coprime q N
    · have hqN : q < N := (Nat.le_mul_of_pos_left q ha).trans_lt (htop.trans_le hMN)
      have hf : q ∈ p5U7MassPrimeWindow N M a ell := Finset.mem_filter.mpr
        ⟨mem_chenAdditivePrimeCarrier.mpr ⟨hqN,hp,hcop⟩,by omega,htop⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hf))
    · have hd : q ∣ N := by
        by_contra hn
        exact hcop (hp.coprime_iff_not_dvd.mpr hn)
      exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp,hd,hN.ne'⟩)
  · have hge : M ≤ a*q := by omega
    have hgeR : (M : ℝ) ≤ (a : ℝ)*q := by exact_mod_cast hge
    have hEq : (q : ℝ) = (M : ℝ)/(a : ℝ) := by
      apply le_antisymm hqxR
      exact (div_le_iff₀ haR).mpr (by nlinarith only [hgeR])
    have hfloor : q = Nat.floor ((M : ℝ)/(a : ℝ)) := by rw [← hEq]; simp
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa using hfloor))

/-- The original N pays every target-prime loss, independently of M. -/
theorem p5U7TerminalPrimeMixed_prefix_gap (N M a ell : ℕ)
    (ha : 0 < a) (hN : 0 < N) (hMN : M ≤ N) :
    0 ≤ primePi ((M : ℝ)/(a : ℝ))-((p5U7MassPrimeWindow N M a ell).card : ℝ) ∧
      primePi ((M : ℝ)/(a : ℝ))-((p5U7MassPrimeWindow N M a ell).card : ℝ) ≤
        (ell : ℝ)+1+(N.primeFactors.card : ℝ) := by
  have hcover := Finset.card_le_card (p5U7TerminalPrimeMixed_prefix_cover N M a ell ha hN hMN)
  have h1 := Finset.card_union_le
    ((p5U7MassPrimeWindow N M a ell ∪ Finset.range ell) ∪ {Nat.floor ((M : ℝ)/(a : ℝ))})
    N.primeFactors
  have h2 := Finset.card_union_le (p5U7MassPrimeWindow N M a ell ∪ Finset.range ell)
    ({Nat.floor ((M : ℝ)/(a : ℝ))} : Finset ℕ)
  have h3 := Finset.card_union_le (p5U7MassPrimeWindow N M a ell) (Finset.range ell)
  simp only [Finset.card_range,Finset.card_singleton] at h1 h2 h3
  have hc : (Nat.primesLE (Nat.floor ((M : ℝ)/(a : ℝ)))).card ≤
      (p5U7MassPrimeWindow N M a ell).card+ell+1+N.primeFactors.card := by omega
  rw [Nat.primesLE_card_eq_primeCounting] at hc
  have hcast : primePi ((M : ℝ)/(a : ℝ)) ≤
      ((p5U7MassPrimeWindow N M a ell).card : ℝ)+(ell : ℝ)+1+(N.primeFactors.card : ℝ) := by
    exact_mod_cast hc
  exact ⟨sub_nonneg.mpr (p5U7MassPrimeWindow_card_le_primePi N M a ell ha),by linarith only [hcast]⟩

/-- Actual mixed-window PNT error, with a free real threshold Y. -/
theorem p5U7TerminalPrimeMixed_abs_error (N M a ell : ℕ)
    (ha : 0 < a) (hN : 0 < N) (hMN : M ≤ N)
    {Y : ℝ} (hY : primeErrorStart ≤ Y) (hYx : Y ≤ (M : ℝ)/(a : ℝ)) :
    |((p5U7MassPrimeWindow N M a ell).card : ℝ)-
      ((M : ℝ)/(a : ℝ))/Real.log ((M : ℝ)/(a : ℝ))| ≤
      primeErrorEnvelope Y*(((M : ℝ)/(a : ℝ))/Real.log ((M : ℝ)/(a : ℝ)))+
        ((ell : ℝ)+1+(N.primeFactors.card : ℝ)) := by
  have hg := p5U7TerminalPrimeMixed_prefix_gap N M a ell ha hN hMN
  have he := primePi_error_le hY hYx
  have ht := abs_add_le
    (((p5U7MassPrimeWindow N M a ell).card : ℝ)-primePi ((M : ℝ)/(a : ℝ)))
    (primePi ((M : ℝ)/(a : ℝ))-((M : ℝ)/(a : ℝ))/Real.log ((M : ℝ)/(a : ℝ)))
  rw [abs_of_nonpos (by linarith only [hg.1])] at ht
  have hid : ((p5U7MassPrimeWindow N M a ell).card : ℝ)-primePi ((M : ℝ)/(a : ℝ))+
      (primePi ((M : ℝ)/(a : ℝ))-((M : ℝ)/(a : ℝ))/Real.log ((M : ℝ)/(a : ℝ))) =
      ((p5U7MassPrimeWindow N M a ell).card : ℝ)-
        ((M : ℝ)/(a : ℝ))/Real.log ((M : ℝ)/(a : ℝ)) := by ring
  rw [hid] at ht
  linarith only [ht,he,hg.2]
end
end ImbalancedChen
