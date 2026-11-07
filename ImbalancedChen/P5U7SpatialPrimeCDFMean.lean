import ImbalancedChen.P5U7SpatialPrimeMainTransport

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Actual prime physical-product CDF at mixed cutoff M(N), target N fixed.
The genuine uniform mixed-window PNT is summed on the original strict
interior; the independently proved mixed native main supplies its limit.
A literal product-cutoff collar is bounded by the already paid original
arithmetic collar. Positive eta is selected before N for the full CDF.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology Set
open scoped BigOperators
open Classical

def p5U7SpatialInteriorPrimeMass (N M : ℕ) (eta : ℝ) : ℝ :=
  (((p5U7SpatialThree N M).filter (fun x => x.1 ∈ p5U7InteriorSelector N eta)).card : ℝ)

theorem p5U7SpatialInteriorPrimeMass_eq_window_sum {N M : ℕ} (hMN : M ≤ N) (eta : ℝ) :
    p5U7SpatialInteriorPrimeMass N M eta =
      ∑ t ∈ p5U7InteriorSelector N eta,((p5U7MassPrimeWindow N M (t.1*t.2) t.2).card : ℝ) := by
  have hset : (p5U7SpatialThree N M).filter (fun x => x.1 ∈ p5U7InteriorSelector N eta) =
      (p5U7InteriorSelector N eta).sigma (fun t => p5U7MassPrimeWindow N M (t.1*t.2) t.2) := by
    rw [p5U7SpatialThree_eq_mixed_windows hMN]
    ext x
    constructor
    · intro hx
      obtain ⟨hx,hi⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_sigma.mpr ⟨hi,(Finset.mem_sigma.mp hx).2⟩
    · intro hx
      obtain ⟨hi,hq⟩ := Finset.mem_sigma.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨(Finset.mem_filter.mp hi).1,hq⟩,hi⟩
  rw [p5U7SpatialInteriorPrimeMass,hset]
  simp only [Finset.card_sigma,Nat.cast_sum]

/-- The ACTUAL spatial interior prime mass is compared to its own mixed
main, with one N threshold controlling every original marked pair. -/
theorem p5U7Spatial_eventually_interior_prime_relative_error (M : ℕ → ℕ) (beta eta epsilon : ℝ)
    (hb : 0 < beta) (heta : 0 < eta) (he : 0 < epsilon)
    (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    ∀ᶠ N : ℕ in atTop,
      |p5U7SpatialInteriorPrimeMass N (M N) eta-p5U7SpatialPrimeMain N (M N) eta| ≤
        epsilon*p5U7SpatialPrimeMain N (M N) eta := by
  filter_upwards [hMN,p5U7Spatial_eventually_actual_prime_window_error M beta eta epsilon
    hb heta he hMN hratio] with N hn hp
  rw [p5U7SpatialInteriorPrimeMass_eq_window_sum hn,p5U7SpatialPrimeMain,
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hp)

/-- Genuine fixed-positive-eta actual spatial prime mean, derived from
actual mixed-window counts rather than any spatial mean hypothesis. -/
theorem tendsto_p5U7SpatialInteriorPrimeMass_normalized (M : ℕ → ℕ) (beta eta : ℝ)
    (hb : 0 < beta) (heta : 0 < eta)
    (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorPrimeMass N (M N) eta)
      atTop (𝓝 (beta*p5U7PrimeLeadingIntegral eta)) := by
  have hB := tendsto_p5U7SpatialPrimeMain_normalized M beta eta hb heta hMN hratio
  apply Metric.tendsto_nhds.2
  intro epsilon he
  let C : ℝ := |beta*p5U7PrimeLeadingIntegral eta|+1
  have hC : 0 < C := by dsimp only [C]; positivity
  let delta : ℝ := epsilon/(4*C)
  have hd : 0 < delta := div_pos he (by positivity)
  have hbnd := hB.eventually (Iio_mem_nhds (show beta*p5U7PrimeLeadingIntegral eta<C by
    dsimp only [C]; linarith only [le_abs_self (beta*p5U7PrimeLeadingIntegral eta)]))
  have hnear := Metric.tendsto_nhds.mp hB (epsilon/2) (by positivity)
  filter_upwards [p5U7Spatial_eventually_interior_prime_relative_error M beta eta delta hb heta hd
    hMN hratio,hbnd,hnear] with N hw hbnd hn
  have hnorm : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hw hnorm
  have herr : |(Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorPrimeMass N (M N) eta-
      (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N (M N) eta| ≤
      delta*((Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N (M N) eta) := by
    rw [← mul_sub,abs_mul,abs_of_nonneg hnorm]
    nlinarith only [hm]
  have hsmall : delta*((Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N (M N) eta) < epsilon/4 := by
    have hm := mul_lt_mul_of_pos_left hbnd hd
    have hid : delta*C=epsilon/4 := by dsimp only [delta];field_simp [hC.ne'];ring
    exact hm.trans_eq hid
  rw [Real.dist_eq] at hn ⊢
  have htri : |(Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorPrimeMass N (M N) eta-
      beta*p5U7PrimeLeadingIntegral eta| ≤
      |(Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorPrimeMass N (M N) eta-
        (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N (M N) eta| +
      |(Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N (M N) eta-
        beta*p5U7PrimeLeadingIntegral eta| := by
    have hh := abs_add_le
      ((Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorPrimeMass N (M N) eta-
        (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N (M N) eta)
      ((Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N (M N) eta-
        beta*p5U7PrimeLeadingIntegral eta)
    convert hh using 1 <;> congr 1 <;> ring
  linarith only [herr,hsmall,hn,htri]

/-- The actual spatial product-cutoff collar is a literal subfamily of
the paid original arithmetic prime collar, with every endpoint unchanged. -/
theorem p5U7SpatialPrimeMass_interior_gap (N M : ℕ) (eta : ℝ) :
    0 ≤ ((p5U7SpatialThree N M).card : ℝ)-p5U7SpatialInteriorPrimeMass N M eta ∧
      ((p5U7SpatialThree N M).card : ℝ)-p5U7SpatialInteriorPrimeMass N M eta ≤
        ((p5U7ActualPrimeCollar N eta).card : ℝ) := by
  let K := (p5U7SpatialThree N M).filter (fun x => x.1 ∉ p5U7InteriorSelector N eta)
  have hsplit := Finset.card_filter_add_card_filter_not (s := p5U7SpatialThree N M)
    (p := fun x => x.1 ∈ p5U7InteriorSelector N eta)
  have hsplitR : p5U7SpatialInteriorPrimeMass N M eta+(K.card : ℝ) =
      ((p5U7SpatialThree N M).card : ℝ) := by exact_mod_cast hsplit
  have hsub : K ⊆ p5U7ActualPrimeCollar N eta := by
    intro x hx
    obtain ⟨hx,hn⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hn⟩
  have hcard : (K.card : ℝ) ≤ ((p5U7ActualPrimeCollar N eta).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact ⟨by linarith only [hsplitR,Nat.cast_nonneg K.card],by linarith only [hsplitR,hcard]⟩

/-- Spatial prime CDF: if M(N)/N tends to beta>0 and M(N)≤N eventually,
the ACTUAL target-N marked physical product weight has leading mass
beta times its genuine full prime integral. Eta is selected before N. -/
theorem tendsto_p5U7SpatialPrimeCDF_normalized (M : ℕ → ℕ) (beta : ℝ) (hb : 0 < beta)
    (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      (∑ m ∈ Finset.range (M N),p5U7ActualPrimeProductWeight N m)) atTop
        (𝓝 (beta*p5U7ComponentPrimeIntegral)) := by
  simp_rw [p5U7SpatialPrimeProductWeight_mass]
  apply Metric.tendsto_nhds.2
  intro epsilon he
  have he3 : 0 < epsilon/3 := by positivity
  have hI := (tendsto_p5U7PrimeLeadingIntegral_to_component.const_mul beta).mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hnear := Metric.tendsto_nhds.mp hI (epsilon/3) he3
  have hcollar := p5U7ActualComponentCollars_eventually_small (epsilon/3) he3
  have hpos : ∀ᶠ eta : ℝ in 𝓝[Ioi (0 : ℝ)] 0,0 < eta := self_mem_nhdsWithin
  obtain ⟨eta,heta,hcollar,hnear⟩ := (hpos.and (hcollar.and hnear)).exists
  have hFixed := Metric.tendsto_nhds.mp
    (tendsto_p5U7SpatialInteriorPrimeMass_normalized M beta eta hb heta hMN hratio) (epsilon/3) he3
  filter_upwards [hcollar,hFixed] with N hc hf
  have hnorm : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hgap := p5U7SpatialPrimeMass_interior_gap N (M N) eta
  have hgap0 := mul_nonneg hnorm hgap.1
  have hgap1 := (mul_le_mul_of_nonneg_left hgap.2 hnorm).trans_lt hc.1
  rw [Real.dist_eq] at hf hnear ⊢
  have heq : (Real.log (N : ℝ)/(N : ℝ))*((p5U7SpatialThree N (M N)).card : ℝ)-
      beta*p5U7ComponentPrimeIntegral =
      (Real.log (N : ℝ)/(N : ℝ))*
        (((p5U7SpatialThree N (M N)).card : ℝ)-p5U7SpatialInteriorPrimeMass N (M N) eta)+
      ((Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorPrimeMass N (M N) eta-
        beta*p5U7PrimeLeadingIntegral eta)+
      (beta*p5U7PrimeLeadingIntegral eta-beta*p5U7ComponentPrimeIntegral) := by ring
  rw [heq]
  calc
    _ ≤ |(Real.log (N : ℝ)/(N : ℝ))*
          (((p5U7SpatialThree N (M N)).card : ℝ)-p5U7SpatialInteriorPrimeMass N (M N) eta)|+
        |(Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorPrimeMass N (M N) eta-
          beta*p5U7PrimeLeadingIntegral eta|+
        |beta*p5U7PrimeLeadingIntegral eta-beta*p5U7ComponentPrimeIntegral| :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ < epsilon := by
      rw [abs_of_nonneg hgap0]
      linarith only [hgap1,hf,hnear]

end
end ImbalancedChen
