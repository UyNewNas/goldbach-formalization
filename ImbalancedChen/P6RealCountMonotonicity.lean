import ImbalancedChen.CurrentMainTheorem

/-!
# All-real exponent monotonicity and extension from a fixed base exponent

Source-only draft: no compilation is claimed. The ordered-region bridge's
existing below-one `ImbalancedChen.RealB_antitone` is not reproved here.
Instead the complement definition gives antitonicity for every real exponent.
All eventual interval conclusions use a lower estimate at one fixed `b0`;
there is no analytic hypothesis quantified over the interval of exponents.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- Increasing any real exponent preserves a receiver witness: its prime base
is at least two, so real powers increase with the exponent. -/
theorem realImbalancedReceiver_mono {a b : ℝ} {m : ℕ} (hab : a ≤ b)
    (hm : RealImbalancedReceiver a m) : RealImbalancedReceiver b m := by
  rcases hm with hm | ⟨r, q, hr, hq, hm, hpow⟩
  · exact Or.inl hm
  · have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := le_trans (by norm_num) hq2
    exact Or.inr ⟨r, q, hr, hq, hm,
      hpow.trans (Real.rpow_le_rpow_of_exponent_le hq1 hab)⟩

/-- Inclusion preserves the additive-prime indexing and strict endpoint. -/
theorem realImbalancedPrimes_mono {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    realImbalancedPrimes a N ⊆ realImbalancedPrimes b N := by
  intro p hp
  rcases mem_realImbalancedPrimes.mp hp with ⟨hpN, hpprime, hm⟩
  exact mem_realImbalancedPrimes.mpr
    ⟨hpN, hpprime, realImbalancedReceiver_mono hab hm⟩

/-- The accepted count is monotone on the whole real line. -/
theorem RealDb_mono {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    RealDb a N ≤ RealDb b N := by
  exact Finset.card_le_card (realImbalancedPrimes_mono hab N)

theorem monotone_RealDb (N : ℕ) : Monotone (fun b : ℝ => RealDb b N) := by
  intro a b hab
  exact RealDb_mono hab N

theorem RealDb_cast_mono {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    (RealDb a N : ℝ) ≤ (RealDb b N : ℝ) := by
  exact_mod_cast RealDb_mono hab N

/-- Direct complement argument, independent of the ordered bad region and
valid even when either exponent is at or above one. -/
theorem realBadReceiver_antitone {a b : ℝ} {m : ℕ} (hab : a ≤ b)
    (hm : RealBadReceiver b m) : RealBadReceiver a m := by
  rcases hm with ⟨hreceiver, hbad⟩
  exact ⟨hreceiver, fun hgood => hbad (realImbalancedReceiver_mono hab hgood)⟩

theorem realBadPrimes_antitone {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    realBadPrimes b N ⊆ realBadPrimes a N := by
  intro p hp
  rcases mem_realBadPrimes.mp hp with ⟨hpN, hpprime, hreceiver, hbad⟩
  exact mem_realBadPrimes.mpr ⟨hpN, hpprime, hreceiver,
    fun hgood => hbad (realImbalancedReceiver_mono hab hgood)⟩

/-- All-real antitonicity; this does not require `a < 1` or `b < 1`. -/
theorem RealB_antitone_all {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    RealB b N ≤ RealB a N := by
  exact Finset.card_le_card (realBadPrimes_antitone hab N)

theorem antitone_RealB (N : ℕ) : Antitone (fun b : ℝ => RealB b N) := by
  intro a b hab
  exact RealB_antitone_all hab N

/-- Natural subtraction has no truncation loss because the counts partition
the finite prime-or-semiprime set. -/
theorem RealDb_eq_D12_sub_RealB (b : ℝ) (N : ℕ) :
    RealDb b N = D12 N - RealB b N := by
  have h := D12_eq_RealDb_add_RealB b N
  omega

theorem RealB_eq_D12_sub_RealDb (b : ℝ) (N : ℕ) :
    RealB b N = D12 N - RealDb b N := by
  have h := D12_eq_RealDb_add_RealB b N
  omega

theorem RealDb_le_D12 (b : ℝ) (N : ℕ) : RealDb b N ≤ D12 N := by
  exact Finset.card_le_card (realImbalancedPrimes_subset_chenPrimes b N)

theorem RealB_le_D12 (b : ℝ) (N : ℕ) : RealB b N ≤ D12 N := by
  exact Finset.card_le_card (realBadPrimes_subset_chenPrimes b N)

theorem RealDb_bounds (b : ℝ) (N : ℕ) :
    0 ≤ RealDb b N ∧ RealDb b N ≤ D12 N := by
  exact ⟨Nat.zero_le _, RealDb_le_D12 b N⟩

/-- A strict complement margin is exactly positivity of the accepted count. -/
theorem RealDb_pos_iff_RealB_lt_D12 (b : ℝ) (N : ℕ) :
    0 < RealDb b N ↔ RealB b N < D12 N := by
  have h := D12_eq_RealDb_add_RealB b N
  omega

/-- Finite real-valued bounds, with no exponent restriction. -/
theorem RealDb_cast_bounds (b : ℝ) (N : ℕ) :
    0 ≤ (RealDb b N : ℝ) ∧ (RealDb b N : ℝ) ≤ (D12 N : ℝ) := by
  constructor
  · exact Nat.cast_nonneg _
  · exact_mod_cast RealDb_le_D12 b N

theorem RealB_cast_bounds (b : ℝ) (N : ℕ) :
    0 ≤ (RealB b N : ℝ) ∧ (RealB b N : ℝ) ≤ (D12 N : ℝ) := by
  constructor
  · exact Nat.cast_nonneg _
  · exact_mod_cast RealB_le_D12 b N

/-- A fixed-base finite lower bound extends to every larger exponent. -/
theorem realDb_lower_on_Ici {b0 lower : ℝ} {N : ℕ}
    (hLower : lower ≤ (RealDb b0 N : ℝ)) :
    ∀ b : ℝ, b0 ≤ b → lower ≤ (RealDb b N : ℝ) := by
  intro b hb
  exact hLower.trans (RealDb_cast_mono hb N)

/-- One threshold from a bound at `b0` works simultaneously for all `b ≥ b0`.
The input has no uniform-in-exponent analytic quantifier. -/
theorem eventually_realDb_lower_on_Ici {b0 : ℝ} {lower : ℕ → ℝ}
    (hLower : ∀ᶠ N in Filter.atTop, Even N →
      lower N ≤ (RealDb b0 N : ℝ)) :
    ∀ᶠ N in Filter.atTop, Even N →
      ∀ b : ℝ, b0 ≤ b → lower N ≤ (RealDb b N : ℝ) := by
  refine hLower.mono ?_
  intro N hN hEven b hb
  exact realDb_lower_on_Ici (hN hEven) b hb

/-- The same fixed-base estimate gives normalized bounds, with the actual
normalization's proved eventual positivity supplying the division step. -/
theorem eventually_normalized_realDb_lower_on_Ici {b0 delta : ℝ}
    (hLower : ∀ᶠ N in Filter.atTop, Even N →
      delta * singularNormalization N ≤ (RealDb b0 N : ℝ)) :
    ∀ᶠ N in Filter.atTop, Even N → ∀ b : ℝ, b0 ≤ b →
      delta ≤ (RealDb b N : ℝ) / singularNormalization N := by
  refine (eventually_singularNormalization_pos.and
    (eventually_realDb_lower_on_Ici hLower)).mono ?_
  rintro N ⟨hpos, hN⟩ hEven b hb
  exact (le_div_iff₀ hpos).2 (hN hEven b hb)

/-- An epsilon/eventual lower estimate at a single fixed exponent extends
the literal even-natural lower-limit conclusion to the entire upper ray. -/
theorem even_liminf_lower_on_Ici_of_fixed_eventual {b0 L : ℝ}
    (hLower : ∀ delta : ℝ, delta < L →
      ∀ᶠ N in Filter.atTop, Even N →
        delta * singularNormalization N ≤ (RealDb b0 N : ℝ)) :
    ∀ b : ℝ, b0 ≤ b →
      (L : EReal) ≤ Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
        evenNatAtTop := by
  intro b hb
  apply ereal_le_even_liminf_of_eventually_ge
  intro delta hdelta
  exact (eventually_normalized_realDb_lower_on_Ici (hLower delta hdelta)).mono
    (fun N hN hEven => hN hEven b hb)

/-- Only the two analytic estimates at the fixed base exponent are inputs.
The resulting coefficient is frozen at `b0`; increasing `b` cannot decrease
the accepted count, so no new analytic estimate at `b` is required. -/
theorem current_interval_lower_of_bounds_at_base {b0 : ℝ}
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (RealB b0 N : ℝ) ≤
          (currentK * Real.log (1 / b0) + epsilon) * singularNormalization N) :
    ∀ b : ℝ, b0 ≤ b →
      ((currentC - currentK * Real.log (1 / b0) : ℝ) : EReal) ≤
        Filter.liminf
          (fun N : ℕ =>
            (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
          evenNatAtTop := by
  apply even_liminf_lower_on_Ici_of_fixed_eventual
  intro delta hdelta
  exact eventually_real_transfer_of_bounds
    (eventually_singularNormalization_pos.mono (fun _ hN _ => hN))
    hLower hUpper hdelta

end

end ImbalancedChen.P6
