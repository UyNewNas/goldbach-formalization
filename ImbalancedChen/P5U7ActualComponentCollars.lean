import ImbalancedChen.P5U7ActualInteriorComponentMeans

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Arithmetic collars are literal complementary filters of the actual marked
prime and ordered-semiprime label families. Their mass is the exact full
source minus the exact fixed interior. The existing two actual means and
analytic eta continuity therefore pay the collar before removing eta.
No arithmetic wall is deleted using Lebesgue nullity.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology Set
open scoped BigOperators
open Classical

def p5U7ActualPrimeCollar (N : ℕ) (eta : ℝ) : Finset P5U7ThreeLabel :=
  (p5U7ArithmeticThree N).filter (fun x => x.1 ∉ p5U7InteriorSelector N eta)

def p5U7ActualSemiprimeCollar (N : ℕ) (eta : ℝ) : Finset P5U7FourLabel :=
  (p5U7ArithmeticFour N).filter (fun x => x.1 ∉ p5U7InteriorSelector N eta)

def p5U7ActualComponentCollarMass (N : ℕ) (eta : ℝ) : ℝ :=
  ((p5U7ActualPrimeCollar N eta).card : ℝ) +
    ((p5U7ActualSemiprimeCollar N eta).card : ℝ)

/-- Finite exact complement count; all strict/inclusive endpoints retain
their original arithmetic membership. -/
theorem p5U7ActualPrimeCollar_card_split (N : ℕ) (eta : ℝ) :
    ((p5U7ArithmeticThree N).card : ℝ) =
      ((p5U7ActualInteriorThree N eta).card : ℝ) +
        ((p5U7ActualPrimeCollar N eta).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not (s := p5U7ArithmeticThree N)
    (p := fun x => x.1 ∈ p5U7InteriorSelector N eta)
  rw [← p5U7ActualInteriorThree_eq_original_filter] at h
  exact_mod_cast h.symm

theorem p5U7ActualSemiprimeCollar_card_split (N : ℕ) (eta : ℝ) :
    ((p5U7ArithmeticFour N).card : ℝ) =
      ((p5U7ActualInteriorFour N eta).card : ℝ) +
        ((p5U7ActualSemiprimeCollar N eta).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not (s := p5U7ArithmeticFour N)
    (p := fun x => x.1 ∈ p5U7InteriorSelector N eta)
  rw [← p5U7ActualInteriorFour_eq_original_filter] at h
  exact_mod_cast h.symm

/-- The two literal component collars partition exactly the lost full
marked source. No squarefree or product-injectivity assumption occurs. -/
theorem p5U7ActualComponentCollarMass_eq_sub (N : ℕ) (eta : ℝ) :
    p5U7ActualComponentCollarMass N eta =
      p5U7ActualFullSourceMass N-p5U7ActualInteriorSourceMass N eta := by
  have hp := p5U7ActualPrimeCollar_card_split N eta
  have hs := p5U7ActualSemiprimeCollar_card_split N eta
  rw [← p5U7ActualInterior_label_mass_eq_rows,p5U7ActualFullSourceMass]
  unfold p5U7ActualComponentCollarMass
  linarith only [hp,hs]

theorem p5U7ActualComponentCollarMass_nonneg (N : ℕ) (eta : ℝ) :
    0 ≤ p5U7ActualComponentCollarMass N eta := by
  unfold p5U7ActualComponentCollarMass
  positivity

theorem p5U7ActualPrimeCollar_le_joint (N : ℕ) (eta : ℝ) :
    ((p5U7ActualPrimeCollar N eta).card : ℝ) ≤ p5U7ActualComponentCollarMass N eta := by
  unfold p5U7ActualComponentCollarMass
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

theorem p5U7ActualSemiprimeCollar_le_joint (N : ℕ) (eta : ℝ) :
    ((p5U7ActualSemiprimeCollar N eta).card : ℝ) ≤ p5U7ActualComponentCollarMass N eta := by
  unfold p5U7ActualComponentCollarMass
  exact le_add_of_nonneg_left (Nat.cast_nonneg _)

/-- Fixed positive eta precedes the actual N limit. This concerns the
arithmetic collar itself, rather than a measure-zero analytic wall. -/
theorem tendsto_p5U7ActualComponentCollarMass_normalized (eta : ℝ) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*p5U7ActualComponentCollarMass N eta)
      atTop (𝓝 (p5U7InteriorOmegaIntegral 0-p5U7InteriorOmegaIntegral eta)) := by
  have h := tendsto_p5U7ActualFullSourceMass_normalized.sub
    (tendsto_p5U7ActualInteriorSourceMass_normalized eta heta)
  apply h.congr'
  filter_upwards [] with N
  rw [p5U7ActualComponentCollarMass_eq_sub]
  ring

/-- Ordered quantifiers: first every sufficiently small positive eta,
then an eventual N bound for its ACTUAL joint marked collar. -/
theorem p5U7ActualComponentCollar_eventually_small (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ eta : ℝ in 𝓝[Ioi (0 : ℝ)] 0, ∀ᶠ N : ℕ in atTop,
      0 ≤ (Real.log (N : ℝ)/(N : ℝ))*p5U7ActualComponentCollarMass N eta ∧
      (Real.log (N : ℝ)/(N : ℝ))*p5U7ActualComponentCollarMass N eta < epsilon := by
  have hI := tendsto_p5U7InteriorOmegaIntegral_eta_zero.mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hnear := hI.eventually (Ioi_mem_nhds
    (show p5U7InteriorOmegaIntegral 0-epsilon/2 < p5U7InteriorOmegaIntegral 0 by
      linarith only [he]))
  have hpos : ∀ᶠ eta : ℝ in 𝓝[Ioi (0 : ℝ)] 0, 0 < eta := self_mem_nhdsWithin
  filter_upwards [hpos,hnear] with eta heta hIntegral
  have hN := (tendsto_p5U7ActualComponentCollarMass_normalized eta heta).eventually
    (Iio_mem_nhds (show p5U7InteriorOmegaIntegral 0-p5U7InteriorOmegaIntegral eta < epsilon by
      linarith only [hIntegral,he]))
  filter_upwards [hN] with N hn
  exact ⟨mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
    (p5U7ActualComponentCollarMass_nonneg N eta),hn⟩

/-- Both actual component collars are paid by the same chosen eta and N.
The r=s terminal labels remain present in the semiprime filter. -/
theorem p5U7ActualComponentCollars_eventually_small (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ eta : ℝ in 𝓝[Ioi (0 : ℝ)] 0, ∀ᶠ N : ℕ in atTop,
      (Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualPrimeCollar N eta).card : ℝ) < epsilon ∧
      (Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualSemiprimeCollar N eta).card : ℝ) < epsilon := by
  filter_upwards [p5U7ActualComponentCollar_eventually_small epsilon he] with eta hEta
  filter_upwards [hEta] with N hN
  have hnorm : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  exact ⟨(mul_le_mul_of_nonneg_left (p5U7ActualPrimeCollar_le_joint N eta) hnorm).trans_lt hN.2,
    (mul_le_mul_of_nonneg_left (p5U7ActualSemiprimeCollar_le_joint N eta) hnorm).trans_lt hN.2⟩

end
end ImbalancedChen
