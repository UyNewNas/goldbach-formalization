import ImbalancedChen.P5U7TerminalPrimeMixedWindow

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual mixed terminal prime window versus the genuine primePi difference.
The inclusive lower endpoint and strict upper endpoint are paid as integer
atoms; original N target-prime exclusions remain explicit. No endpoint is
deleted by a measure-zero argument or a change of target to M.
-/
namespace ImbalancedChen
noncomputable section
open LiLiuPrereqBuchstab
open Classical

/-- Signed endpoint budgets for the actual [ell,M/a) prime window. -/
theorem p5U7TerminalPrimeMixed_primePi_difference_bounds (N M a ell : ℕ)
    (ha : 0 < a) (hN : 0 < N) (hMN : M ≤ N)
    (hell : (ell : ℝ) ≤ (M : ℝ)/(a : ℝ)) :
    -(1+(N.primeFactors.card : ℝ)) ≤
      ((p5U7MassPrimeWindow N M a ell).card : ℝ)-
        (primePi ((M : ℝ)/(a : ℝ))-primePi (ell : ℝ)) ∧
    ((p5U7MassPrimeWindow N M a ell).card : ℝ)-
      (primePi ((M : ℝ)/(a : ℝ))-primePi (ell : ℝ)) ≤ 1 := by
  let P := Nat.primesLE (Nat.floor ((M : ℝ)/(a : ℝ)))
  let L := Nat.primesLE ell
  let W := p5U7MassPrimeWindow N M a ell
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hx0 : 0 ≤ (M : ℝ)/(a : ℝ) := div_nonneg (Nat.cast_nonneg _) haR.le
  have hLP : L ⊆ P := by
    intro q hq
    obtain ⟨hqe,hqp⟩ := Nat.mem_primesLE.mp hq
    have hqR : (q : ℝ) ≤ (M : ℝ)/(a : ℝ) :=
      (show (q : ℝ) ≤ ell by exact_mod_cast hqe).trans hell
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hx0).mpr hqR,hqp⟩
  have hcover : P ⊆ ((W ∪ L) ∪ {Nat.floor ((M : ℝ)/(a : ℝ))}) ∪ N.primeFactors := by
    intro q hq
    have hp := (Nat.mem_primesLE.mp hq).2
    have hc := p5U7TerminalPrimeMixed_prefix_cover N M a ell ha hN hMN hq
    rcases Finset.mem_union.mp hc with hleft | hfactor
    · rcases Finset.mem_union.mp hleft with hlow | hend
      · rcases Finset.mem_union.mp hlow with hw | hrange
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hw))
        · have hqell : q ≤ ell := (Finset.mem_range.mp hrange).le
          have hl : q ∈ L := Nat.mem_primesLE.mpr ⟨hqell,hp⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hl))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hend)
    · exact Finset.mem_union_right _ hfactor
  have hc := Finset.card_le_card hcover
  have h1 := Finset.card_union_le ((W ∪ L) ∪ {Nat.floor ((M : ℝ)/(a : ℝ))}) N.primeFactors
  have h2 := Finset.card_union_le (W ∪ L) ({Nat.floor ((M : ℝ)/(a : ℝ))} : Finset ℕ)
  have h3 := Finset.card_union_le W L
  simp only [Finset.card_singleton] at h1 h2
  have hlowerNat : P.card ≤ W.card+L.card+1+N.primeFactors.card := by omega
  have hWcover : W ⊆ (P \ L) ∪ {ell} := by
    intro q hq
    have hqp : q ∈ P := p5U7MassPrimeWindow_subset_prefix N M a ell ha hq
    have hwall := (Finset.mem_filter.mp hq).2.1
    by_cases hqe : q = ell
    · exact Finset.mem_union_right _ (by simpa using hqe)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hqp,fun h =>
        hqe (Nat.le_antisymm (Nat.mem_primesLE.mp h).1 hwall)⟩)
  have hWU := (Finset.card_le_card hWcover).trans (Finset.card_union_le _ _)
  simp only [Finset.card_singleton] at hWU
  have hPL := Finset.card_sdiff_add_card_eq_card hLP
  have hupperNat : W.card+L.card ≤ P.card+1 := by omega
  have hPcard : P.card = Nat.primeCounting (Nat.floor ((M : ℝ)/(a : ℝ))) :=
    Nat.primesLE_card_eq_primeCounting _
  have hLcard : L.card = Nat.primeCounting ell := Nat.primesLE_card_eq_primeCounting _
  rw [hPcard,hLcard] at hlowerNat hupperNat
  have hlower : primePi ((M : ℝ)/(a : ℝ)) ≤ (W.card : ℝ)+
      (Nat.primeCounting ell : ℝ)+1+(N.primeFactors.card : ℝ) := by exact_mod_cast hlowerNat
  have hupper : (W.card : ℝ)+(Nat.primeCounting ell : ℝ) ≤
      primePi ((M : ℝ)/(a : ℝ))+1 := by exact_mod_cast hupperNat
  have hpiell : primePi (ell : ℝ) = (Nat.primeCounting ell : ℝ) := by simp [primePi]
  change -(1+(N.primeFactors.card : ℝ)) ≤ (W.card : ℝ)-
      (primePi ((M : ℝ)/(a : ℝ))-primePi (ell : ℝ)) ∧
    (W.card : ℝ)-(primePi ((M : ℝ)/(a : ℝ))-primePi (ell : ℝ)) ≤ 1
  rw [hpiell]
  exact ⟨by linarith only [hlower],by linarith only [hupper]⟩

/-- Explicit two-endpoint payment, with original target-divisor loss. -/
theorem p5U7TerminalPrimeMixed_primePi_difference_error (N M a ell : ℕ)
    (ha : 0 < a) (hN : 0 < N) (hMN : M ≤ N)
    (hell : (ell : ℝ) ≤ (M : ℝ)/(a : ℝ)) :
    |((p5U7MassPrimeWindow N M a ell).card : ℝ)-
      (primePi ((M : ℝ)/(a : ℝ))-primePi (ell : ℝ))| ≤
        2+(N.primeFactors.card : ℝ) := by
  have hb := p5U7TerminalPrimeMixed_primePi_difference_bounds N M a ell ha hN hMN hell
  apply abs_le.mpr
  have hf : (0 : ℝ) ≤ N.primeFactors.card := Nat.cast_nonneg _
  exact ⟨by linarith only [hb.1,hf],by linarith only [hb.2,hf]⟩
end
end ImbalancedChen
