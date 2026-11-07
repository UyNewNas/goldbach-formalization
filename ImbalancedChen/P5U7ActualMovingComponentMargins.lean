import ImbalancedChen.P5U7ActualComponentProductCollarL1

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
A separate moving-margin consequence of the fixed-positive-eta-first-N
arithmetic theorems. Literal selector monotonicity bounds each moving
collar by one fixed positive collar selected before N. This does not
replace the quantifier order in the original fixed-margin strategy.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology Set
open scoped BigOperators
open Classical

/-- Larger eta imposes a stronger literal cap on the same original
marked pair. Arithmetic order and cap endpoints are retained exactly. -/
theorem p5U7InteriorSelector_margin_antitone {N : ℕ} (hN : 2 ≤ N)
    {theta eta : ℝ} (hle : theta ≤ eta) :
    p5U7InteriorSelector N eta ⊆ p5U7InteriorSelector N theta := by
  intro t ht
  obtain ⟨ht0,hreg⟩ := Finset.mem_filter.mp ht
  obtain ⟨ho,hcap⟩ := (p5U7InteriorRegion_iff eta _).mp hreg
  have hc := (Finset.mem_filter.mp ht0).1
  have hq := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  have hu : 0 < actualPrimeTupleLog N ![t.1,t.2] 1 := by
    change 0 < Real.log (t.2 : ℝ)/Real.log (N : ℝ)
    exact div_pos (Real.log_pos (by exact_mod_cast hq.one_lt))
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  refine Finset.mem_filter.mpr ⟨ht0,(p5U7InteriorRegion_iff theta _).mpr ⟨ho,?_⟩⟩
  have hm := mul_le_mul_of_nonneg_right hle hu.le
  nlinarith only [hm,hcap]

theorem p5U7ActualPrimeCollar_margin_mono {N : ℕ} (hN : 2 ≤ N)
    {theta eta : ℝ} (hle : theta ≤ eta) :
    p5U7ActualPrimeCollar N theta ⊆ p5U7ActualPrimeCollar N eta := by
  intro x hx
  obtain ⟨hx,hn⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx,fun hi => hn (p5U7InteriorSelector_margin_antitone hN hle hi)⟩

theorem p5U7ActualSemiprimeCollar_margin_mono {N : ℕ} (hN : 2 ≤ N)
    {theta eta : ℝ} (hle : theta ≤ eta) :
    p5U7ActualSemiprimeCollar N theta ⊆ p5U7ActualSemiprimeCollar N eta := by
  intro x hx
  obtain ⟨hx,hn⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx,fun hi => hn (p5U7InteriorSelector_margin_antitone hN hle hi)⟩

theorem p5U7ActualComponentCollarMass_margin_mono {N : ℕ} (hN : 2 ≤ N)
    {theta eta : ℝ} (hle : theta ≤ eta) :
    p5U7ActualComponentCollarMass N theta ≤ p5U7ActualComponentCollarMass N eta := by
  have hp : ((p5U7ActualPrimeCollar N theta).card : ℝ) ≤
      ((p5U7ActualPrimeCollar N eta).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (p5U7ActualPrimeCollar_margin_mono hN hle)
  have hs : ((p5U7ActualSemiprimeCollar N theta).card : ℝ) ≤
      ((p5U7ActualSemiprimeCollar N eta).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (p5U7ActualSemiprimeCollar_margin_mono hN hle)
  exact add_le_add hp hs

/-- For every eventually positive eta(N) tending to zero, choose one
fixed positive collar first and then dominate the moving collar for N
large enough. No uniform-in-eta arithmetic mean is assumed. -/
theorem tendsto_p5U7ActualMovingComponentCollar (eta : ℕ → ℝ)
    (heta : ∀ᶠ N : ℕ in atTop,0 < eta N) (hzero : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      p5U7ActualComponentCollarMass N (eta N)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro epsilon he
  have hpos : ∀ᶠ delta : ℝ in 𝓝[Ioi (0 : ℝ)] 0,0 < delta := self_mem_nhdsWithin
  obtain ⟨delta,hdelta,hcollar⟩ :=
    (hpos.and (p5U7ActualComponentCollar_eventually_small epsilon he)).exists
  have hbelow := hzero.eventually (Iio_mem_nhds hdelta)
  filter_upwards [hbelow,hcollar,heta,eventually_ge_atTop (2 : ℕ)] with N hn hc hp hN
  have hnorm : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hnonneg := mul_nonneg hnorm (p5U7ActualComponentCollarMass_nonneg N (eta N))
  have hbound := mul_le_mul_of_nonneg_left
    (p5U7ActualComponentCollarMass_margin_mono hN hn.le) hnorm
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  exact hbound.trans_lt hc.2

theorem tendsto_p5U7ActualMovingPrimeCollar (eta : ℕ → ℝ)
    (heta : ∀ᶠ N : ℕ in atTop,0 < eta N) (hzero : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      ((p5U7ActualPrimeCollar N (eta N)).card : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (tendsto_p5U7ActualMovingComponentCollar eta heta hzero)
  · filter_upwards [] with N
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · filter_upwards [] with N
    exact mul_le_mul_of_nonneg_left (p5U7ActualPrimeCollar_le_joint N (eta N))
      (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))

theorem tendsto_p5U7ActualMovingSemiprimeCollar (eta : ℕ → ℝ)
    (heta : ∀ᶠ N : ℕ in atTop,0 < eta N) (hzero : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      ((p5U7ActualSemiprimeCollar N (eta N)).card : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (tendsto_p5U7ActualMovingComponentCollar eta heta hzero)
  · filter_upwards [] with N
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · filter_upwards [] with N
    exact mul_le_mul_of_nonneg_left (p5U7ActualSemiprimeCollar_le_joint N (eta N))
      (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))

/-- Actual moving-cutoff physical measures converge in normalized L1
to their respective full arithmetic component measures. -/
theorem tendsto_p5U7ActualMovingPrimeProductWeight_L1 (eta : ℕ → ℝ)
    (heta : ∀ᶠ N : ℕ in atTop,0 < eta N) (hzero : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*(∑ m ∈ Finset.range N,
      |p5U7ActualPrimeProductWeight N m-p5U7ActualInteriorPrimeProductWeight N (eta N) m|))
      atTop (𝓝 0) := by
  simpa only [p5U7ActualPrimeProductWeight_collar_L1] using
    tendsto_p5U7ActualMovingPrimeCollar eta heta hzero

theorem tendsto_p5U7ActualMovingSemiprimeProductWeight_L1 (eta : ℕ → ℝ)
    (heta : ∀ᶠ N : ℕ in atTop,0 < eta N) (hzero : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*(∑ m ∈ Finset.range N,
      |p5U7ActualSemiprimeProductWeight N m-p5U7ActualInteriorSemiprimeProductWeight N (eta N) m|))
      atTop (𝓝 0) := by
  simpa only [p5U7ActualSemiprimeProductWeight_collar_L1] using
    tendsto_p5U7ActualMovingSemiprimeCollar eta heta hzero

/-- Moving-cutoff prime mass as a separate consequence, after the main
fixed-positive-eta-first-N argument has supplied the full arithmetic mean. -/
theorem tendsto_p5U7ActualMovingPrimeProductWeight_mass (eta : ℕ → ℝ)
    (heta : ∀ᶠ N : ℕ in atTop,0 < eta N) (hzero : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*(∑ m ∈ Finset.range N,
      p5U7ActualInteriorPrimeProductWeight N (eta N) m)) atTop (𝓝 p5U7ComponentPrimeIntegral) := by
  have h := tendsto_p5U7ActualFullPrimeMass_normalized.sub
    (tendsto_p5U7ActualMovingPrimeCollar eta heta hzero)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [p5U7ActualInteriorPrimeProductWeight_mass,p5U7ActualPrimeCollar_card_split N (eta N)]
  ring

/-- The moving ordered-semiprime mass retains its repeated terminal-prime
wall and converges to the same independent genuine nested integral. -/
theorem tendsto_p5U7ActualMovingSemiprimeProductWeight_mass (eta : ℕ → ℝ)
    (heta : ∀ᶠ N : ℕ in atTop,0 < eta N) (hzero : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*(∑ m ∈ Finset.range N,
      p5U7ActualInteriorSemiprimeProductWeight N (eta N) m)) atTop
        (𝓝 p5U7ComponentSemiprimeIntegral) := by
  have h := tendsto_p5U7ActualFullSemiprimeMass_normalized.sub
    (tendsto_p5U7ActualMovingSemiprimeCollar eta heta hzero)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [p5U7ActualInteriorSemiprimeProductWeight_mass,p5U7ActualSemiprimeCollar_card_split N (eta N)]
  ring

end
end ImbalancedChen
