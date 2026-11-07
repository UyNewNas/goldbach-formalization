import ImbalancedChen.P5U7SemiprimeIntegralEtaZero
import ImbalancedChen.P5U7PrimeIntegralZeroDictionary

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Full actual prime and ordered-semiprime component means. Positive eta is
chosen FIRST from the genuine prime integral continuity and the ACTUAL
joint arithmetic collar budget. N is chosen only after that eta. The
separate semiprime mean is then full actual mean minus the correct actual
prime carrier. Every marked outer label and repeated terminal factor is
retained; no final component mean is a premise.
-/
namespace ImbalancedChen
noncomputable section
open Set Filter Topology
open scoped BigOperators
open Classical

/-- Independent nested ordered-semiprime constant identified with its
literal zero-cutoff kernel integral, using the genuine additive split. -/
theorem p5U7SemiprimeLeadingIntegral_zero_eq_component :
    p5U7SemiprimeLeadingIntegral 0 = p5U7ComponentSemiprimeIntegral := by
  rw [p5U7SemiprimeLeadingIntegral_eq_sub 0 (by norm_num),
    p5U7InteriorOmegaIntegral_zero_eq_original,p5U7PrimeLeadingIntegral_zero_eq_component]
  exact p5U7ComponentSemiprimeIntegral_eq_sub.symm

/-- The literal semiprime DCT also targets the independent genuine nested
ordered terminal-pair integral; this is purely an analytic dictionary. -/
theorem tendsto_p5U7SemiprimeLeadingIntegral_to_component :
    Tendsto p5U7SemiprimeLeadingIntegral (𝓝[Ici (0 : ℝ)] 0)
      (𝓝 p5U7ComponentSemiprimeIntegral) := by
  rw [← p5U7SemiprimeLeadingIntegral_zero_eq_component]
  exact tendsto_p5U7SemiprimeLeadingIntegral_eta_zero

/-- FULL actual target-excluding terminal-prime branch. The proof pays
its literal complementary arithmetic collar before removing positive eta. -/
theorem tendsto_p5U7ActualFullPrimeMass_normalized :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      ((p5U7ArithmeticThree N).card : ℝ)) atTop (𝓝 p5U7ComponentPrimeIntegral) := by
  apply Metric.tendsto_nhds.2
  intro epsilon he
  have he3 : 0 < epsilon/3 := by positivity
  have hI := tendsto_p5U7PrimeLeadingIntegral_to_component.mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hnear := Metric.tendsto_nhds.mp hI (epsilon/3) he3
  have hcollar := p5U7ActualComponentCollars_eventually_small (epsilon/3) he3
  have hpos : ∀ᶠ eta : ℝ in 𝓝[Ioi (0 : ℝ)] 0, 0 < eta := self_mem_nhdsWithin
  obtain ⟨eta,heta,hcollar,hnear⟩ := (hpos.and (hcollar.and hnear)).exists
  have hFixed := Metric.tendsto_nhds.mp
    (tendsto_p5U7ActualInteriorThree_normalized eta heta) (epsilon/3) he3
  filter_upwards [hcollar,hFixed] with N hCollar hFixed
  have hnorm : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hW : 0 ≤ (Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualPrimeCollar N eta).card : ℝ) :=
    mul_nonneg hnorm (Nat.cast_nonneg _)
  have heq : (Real.log (N : ℝ)/(N : ℝ))*((p5U7ArithmeticThree N).card : ℝ) -
      p5U7ComponentPrimeIntegral =
      ((Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualInteriorThree N eta).card : ℝ)-
        p5U7PrimeLeadingIntegral eta) +
      (Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualPrimeCollar N eta).card : ℝ) +
      (p5U7PrimeLeadingIntegral eta-p5U7ComponentPrimeIntegral) := by
    rw [p5U7ActualPrimeCollar_card_split N eta]
    ring
  rw [Real.dist_eq] at hFixed hnear ⊢
  rw [heq]
  calc
    _ ≤ |(Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualInteriorThree N eta).card : ℝ)-
          p5U7PrimeLeadingIntegral eta| +
        |(Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualPrimeCollar N eta).card : ℝ)| +
        |p5U7PrimeLeadingIntegral eta-p5U7ComponentPrimeIntegral| :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ < epsilon := by
      rw [abs_of_nonneg hW]
      linarith only [hFixed,hCollar.1,hnear]

/-- Exact arithmetic subtraction uses the actual three-label carrier.
It never reuses the full prime-plus-semiprime source as one component. -/
theorem p5U7ActualFullSemiprimeMass_eq_full_sub_prime (N : ℕ) :
    (Real.log (N : ℝ)/(N : ℝ))*((p5U7ArithmeticFour N).card : ℝ) =
      (Real.log (N : ℝ)/(N : ℝ))*p5U7ActualFullSourceMass N -
        (Real.log (N : ℝ)/(N : ℝ))*((p5U7ArithmeticThree N).card : ℝ) := by
  unfold p5U7ActualFullSourceMass
  ring

/-- FULL separate actual ordered-semiprime leading integral and limit.
The repeated terminal-prime wall is retained with coefficient one. The
full genuine mean is reduced by the independently proved actual prime mass. -/
theorem tendsto_p5U7ActualFullSemiprimeMass_normalized :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      ((p5U7ArithmeticFour N).card : ℝ)) atTop (𝓝 p5U7ComponentSemiprimeIntegral) := by
  have hFull : Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      p5U7ActualFullSourceMass N) atTop (𝓝 (p5U7OriginalOmegaIntegral 1)) := by
    simpa only [p5U7InteriorOmegaIntegral_zero_eq_original] using
      tendsto_p5U7ActualFullSourceMass_normalized
  have h := hFull.sub tendsto_p5U7ActualFullPrimeMass_normalized
  rw [p5U7ComponentSemiprimeIntegral_eq_sub]
  apply h.congr'
  filter_upwards [] with N
  exact (p5U7ActualFullSemiprimeMass_eq_full_sub_prime N).symm

/-- Same full arithmetic component limit in the literal eta-zero domain
integral form. Only the proved analytic dictionary changes the constant. -/
theorem tendsto_p5U7ActualFullSemiprimeMass_zeroIntegral :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      ((p5U7ArithmeticFour N).card : ℝ)) atTop (𝓝 (p5U7SemiprimeLeadingIntegral 0)) := by
  rw [p5U7SemiprimeLeadingIntegral_zero_eq_component]
  exact tendsto_p5U7ActualFullSemiprimeMass_normalized

/-- Requested error gives a literal full ordered-semiprime eventual N
threshold; all analytic and arithmetic margin choices have been supplied. -/
theorem p5U7ActualFullSemiprimeMass_eventually_abs (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      |(Real.log (N : ℝ)/(N : ℝ))*((p5U7ArithmeticFour N).card : ℝ)-
        p5U7ComponentSemiprimeIntegral| < epsilon := by
  simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
    tendsto_p5U7ActualFullSemiprimeMass_normalized epsilon he

end
end ImbalancedChen
