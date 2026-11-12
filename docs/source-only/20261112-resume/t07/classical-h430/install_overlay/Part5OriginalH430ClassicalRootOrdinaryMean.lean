import ImbalancedChen.Part5OriginalH430ClassicalRootPriceGeometry
import ImbalancedChen.Part5OriginalH430SeedChildRosserDictionary

/-! Two-sided ordinary main term on the real original classical roots.
The carrier of the compact density theorem is M=pN. Its parameter is
log(Q/p)/log M, and its natural strict Rosser level equals the old
floor-plus-one precisely because p is a target-coprime prime. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalRootOrdinaryMean
noncomputable section
open Set Finset Filter Real Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418 (logarithmicIntegral)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport (rootQ rootLevel)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OwnedRootCounts Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430SameQCanonicalMains (model)
open Part5OriginalH430ClassicalRootPriceGeometry (actual_classical_queries)
open Part5OriginalH430SeedChildRosserDictionary (true_child_ceil)

private theorem same_prime_density {N n p : ℕ} {τ : ℝ} (hp : p.Prime) (hc : p.Coprime N)
    (z : ℝ) : let Q := rootQ N n .U3 τ p
    actualSmallRosserPlusDensity (p*N) ⌈z⌉₊ z (Q/p) =
      ordinaryRosserMainSum true N p (P2ActualMarkedCountState.rootLevel Q p) z := by
  let Q := rootQ N n .U3 τ p
  have hQ : 0 ≤ Q := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hceil : ⌈Q/(p:ℝ)⌉₊ = P2ActualMarkedCountState.rootLevel Q p := by
    simpa only [P2EnhancedNegativeChildRosser.childLevel, one_mul, Q] using
      true_child_ceil (N := N) (p := p) (n := n) .U3 τ (d := 1) hp hc zero_lt_one hQ
  have hpr : actualSmallPrimeFinset (p*N) ⌈z⌉₊ z = primeWindow (p*N) 0 z := by
    ext q
    rw [mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil z), mem_primeWindow]
    constructor
    · rintro ⟨hq,hn,hz⟩
      exact ⟨hq,hq.coprime_iff_not_dvd.mpr hn,Nat.cast_nonneg _,hz⟩
    · rintro ⟨hq,hc',_,hz⟩
      exact ⟨hq,hq.coprime_iff_not_dvd.mp hc',hz⟩
  have hprod : actualSmallPrimeProduct (p*N) ⌈z⌉₊ z = ordinarySievePrimeProduct (p*N) z := by
    unfold actualSmallPrimeProduct ordinarySievePrimeProduct
    rw [hpr] <;> rfl
  change (∑ e ∈ (actualSmallPrimeProduct (p*N) ⌈z⌉₊ z).divisors,
    actualSmallRosserPlus (p*N) ⌈z⌉₊ z (Q/p) e / (Nat.totient e:ℝ)) = _
  unfold actualSmallRosserPlus ActualSmallRosserProvider.upperWeight ordinaryRosserMainSum ordinaryRosserWeight
  rw [MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_eq_producer, hprod, hceil]
  <;> rfl

private theorem beta_bounds {N n p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    Real.log (rootQ N n .U3 τ p / (p:ℝ)) / Real.log ((p*N:ℕ):ℝ) ∈ Icc (11/768:ℝ) 1 := by
  have hb := (Finset.mem_filter.mp hp).1
  have hgeo := original_band_geometry hN hb
  have hpp := (original_band_prime hb).1
  have hNr : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpr : (0:ℝ) < p := Nat.cast_pos.mpr hpp.pos
  let t := physicalPrime N p
  let L := rootLevel N n .U3 τ p - t
  have hr : 11/384 ≤ L ∧ L ≤ 1/2 := by
    simpa only [frozenRoot_residual, rootLevel, L, t] using frozenRoot_residual_bounds hτ hτ' hgeo hn
  have hR : (N:ℝ)^L = rootQ N n .U3 τ p / (p:ℝ) :=
    residual_rpow_level_div _ _ _ hNr hpr
  have hlog := Real.log_pos hNr
  have hM : Real.log ((p*N:ℕ):ℝ) = (1+t)*Real.log (N:ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hpr.ne' (zero_lt_one.trans hNr).ne']
    dsimp [t, physicalPrime]
    field_simp [hlog.ne'] <;> ring
  have ht0 : 0 ≤ t := div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) hlog.le
  have ht1 : t ≤ 1 := hgeo.2.trans (by norm_num : (1/3:ℝ) ≤ 1)
  have hdiv : Real.log (rootQ N n .U3 τ p / (p:ℝ)) / Real.log ((p*N:ℕ):ℝ) =
      L/(1+t) := by
    rw [← hR, Real.log_rpow (zero_lt_one.trans hNr), hM]
    field_simp [hlog.ne', (by linarith : 1+t≠0)] <;> ring
  rw [hdiv]
  exact ⟨(le_div_iff₀ (by linarith : 0<1+t)).mpr (by linarith [hr.1]),
    (div_le_iff₀ (by linarith : 0<1+t)).mpr (by linarith [hr.2])⟩

/-- The true ordinary main on every p is Θ_p+o(Θ_p), from both sides.
The threshold precedes N, both meshes, τ, p and every actual cell query. -/
theorem classical_root_main_close {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (n m : ℕ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 → ∀ p ∈ classicalBand N,
      let Q := rootQ N n .U3 τ p
      |model true N Q p (cutoffAt N n m p τ) - thetaAtom N Q p| ≤ ε*thetaAtom N Q p := by
  let f : ℝ × ℝ → ℝ × ℝ := fun x => (x.1,x.1*x.2)
  let T := f '' ((Icc (11/768:ℝ) 1) ×ˢ (Icc (1/3:ℝ) (1/2)))
  have hc : IsCompact T := (isCompact_Icc.prod isCompact_Icc).image
    (continuous_fst.prodMk (continuous_fst.mul continuous_snd))
  have hpar : ∀ x ∈ T, 0 < x.2 ∧ x.2 < x.1 ∧ x.1 ≤ 3*x.2 := by
    rintro _ ⟨⟨b,v⟩, hx, rfl⟩
    obtain ⟨hb, hv⟩ := hx
    have hb' : 0 < b := lt_of_lt_of_le (by norm_num : (0:ℝ)<11/768) hb.1
    have hv' : 0 < v := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/3) hv.1
    change 0 < b*v ∧ b*v < b ∧ b ≤ 3*(b*v)
    refine ⟨mul_pos hb' hv', mul_lt_of_lt_one_right hb' (hv.2.trans_lt (by norm_num)), ?_⟩
    linarith only [mul_le_mul_of_nonneg_left hv.1 hb'.le]
  obtain ⟨N₀, _, hf⟩ := exists_actualSmallRosserPlusDensity_initial_compact_normalized_threshold
    T hc hpar ε he
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (4:ℕ)] with N hcut hN
  intro hEven n m τ hτ hτ' hn p hp
  let M := p*N
  let Q := rootQ N n .U3 τ p
  let R := Q/(p:ℝ)
  let w := queryAt (keyAt N n m .U3 τ p)
  let z := cutoffAt N n m p τ
  let b := Real.log R / Real.log (M:ℝ)
  have h2 : 2 ≤ N := by omega
  have hpp := original_band_prime (Finset.mem_filter.mp hp).1
  have hNM : N ≤ M := Nat.le_mul_of_pos_left N hpp.1.pos
  have hMr : (1:ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hNr : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hR : 1 < R := (classical_geometry (m := m) h2 hτ hτ' hn hp).1
  have hb : b ∈ Icc (11/768:ℝ) 1 := beta_bounds h2 hτ hτ' hn hp
  obtain ⟨hs, _, hsw, hw⟩ := actual_classical_queries (m := m) h2 hτ hτ' hn hp
  have hw2 : 2 ≤ w := hs.trans hsw
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw2
  have hv : 1/w ∈ Icc (1/3:ℝ) (1/2) :=
    ⟨(le_div_iff₀ hw0).mpr (by linarith only [hw]), (div_le_iff₀ hw0).mpr (by linarith)⟩
  have hbt : (b,b*(1/w)) ∈ T := ⟨(b,1/w), ⟨hb,hv⟩, rfl⟩
  have hpow : (M:ℝ)^b = R := residual_rpow_log_div _ _ hMr (zero_lt_one.trans hR)
  have hz : (M:ℝ)^(b*(1/w)) = z := by
    rw [Real.rpow_mul (Nat.cast_nonneg M), hpow] <;> rfl
  let d := actualSmallRosserPlusDensity M ⌈z⌉₊ z R
  have hd : |d*Real.log (M:ℝ)/singularSeries M - 4/b| < ε := by
    have hh := hf M (hcut.trans hNM) (hEven.mul_left p) (b,b*(1/w)) hbt ⌈z⌉₊
      (by simpa only [hz] using Nat.le_ceil z)
    simpa only [hz, hpow, d] using hh
  have heq : d = ordinaryRosserMainSum true N p (P2ActualMarkedCountState.rootLevel Q p) z :=
    same_prime_density hpp.1 hpp.2 z
  have hφ : 0 < (Nat.totient p:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hpp.1.pos)
  have hlogN := Real.log_pos hNr
  have hli : 0 < logarithmicIntegral N :=
    (by positivity : (0:ℝ)<N/(2*Real.log (N:ℝ))).trans_le (box_trueLi_lower hN)
  have hlog := Real.log_pos hMr
  have hS := singularSeries_pos M
  have hW : wuSingularSeries M = singularSeries M := by
    rw [wuSingularSeries_eq_liu M (by omega), currentChen_singularSeries_eq_liuSingularSeries]
  let K := (logarithmicIntegral N/(Nat.totient p:ℝ))*(singularSeries M/Real.log (M:ℝ))
  have hK : 0 < K := mul_pos (div_pos hli hφ) (div_pos hS hlog)
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num : (0:ℝ)<11/768) hb.1
  have hbl : b*Real.log (M:ℝ) = Real.log R := div_mul_cancel₀ _ hlog.ne'
  have h1 : K*(4/b) = thetaAtom N Q p := by
    change _ = 4*logarithmicIntegral N*(wuSingularSeries M/((Nat.totient p:ℝ)*Real.log R))
    rw [hW, ← hbl]
    dsimp only [K]
    field_simp [hb0.ne', hφ.ne', hlog.ne'] <;> ring
  have h2' : K*(d*Real.log (M:ℝ)/singularSeries M) = model true N Q p z := by
    unfold model
    rw [← heq]
    dsimp only [K]
    field_simp [hφ.ne', hlog.ne', hS.ne'] <;> ring
  have hKθ : K ≤ thetaAtom N Q p := by
    rw [← h1]
    apply le_mul_of_one_le_right hK.le
    exact (le_div_iff₀ hb0).mpr (by linarith [hb.2])
  change |model true N Q p z - thetaAtom N Q p| ≤ ε*thetaAtom N Q p
  rw [← h2', ← h1, ← mul_sub, abs_mul, abs_of_pos hK]
  calc
    _ ≤ K*ε := mul_le_mul_of_nonneg_left hd.le hK.le
    _ = ε*K := mul_comm _ _
    _ ≤ _ := by rw [h1]; exact mul_le_mul_of_nonneg_left hKθ he.le

end
end ImbalancedChen.Part5OriginalH430ClassicalRootOrdinaryMean
