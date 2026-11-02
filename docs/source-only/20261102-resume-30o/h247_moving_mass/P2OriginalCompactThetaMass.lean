import ImbalancedChen.P2OriginalCompactScaledPrimeMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Uniformity in the residual exponent is proved before permitting prefixes,
actions or marks to depend on N.  Exact fresh/repeated local factors are
still those of P2OriginalChildPhysicalNormalization.
-/
namespace ImbalancedChen.P2OriginalCompactThetaMass

noncomputable section
open MeasureTheory Filter Set
open P5OriginalActionMassBound P2OriginalChildPhysicalNormalization
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalCompactScaledPrimeMass
open scoped Classical BigOperators Topology

/-- Uniform replacement error uses N^(Lmin/10), not a moving threshold.
The enlarged box is fixed before N and has a genuine existing mass limit. -/
theorem compact_multiplier_error {k : ℕ} {Lmin Lmax C epsilon : ℝ}
    (hmin : 0<Lmin) (hmax : Lmin≤Lmax) (hC : 0≤C) (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀L∈Icc Lmin Lmax,
      4≤(N:ℝ)^(L/10) ∧
      (C/(N:ℝ)^(L/10))*
        actualPrimeBoxMass N (fun _ : Fin k => L/10) (fun _ => 3*L/5)<epsilon := by
  have hi := tendsto_nat_log_pow_div_rpow 0 (show 0<Lmin/10 by positivity)
  simp only [pow_zero] at hi
  have hm := tendsto_actualPrimeBoxMass (fun _ : Fin k => Lmin/20) (fun _ => Lmax)
    (fun _ => by positivity) (fun _ => by linarith)
  have he : Tendsto (fun N : ℕ => (C/(N:ℝ)^(Lmin/10))*
      actualPrimeBoxMass N (fun _ : Fin k => Lmin/20) (fun _ => Lmax)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,mul_one_div] using (hi.const_mul C).mul hm
  have hp : Tendsto (fun N : ℕ => (N:ℝ)^(Lmin/10)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0<Lmin/10)).comp tendsto_natCast_atTop_atTop
  have hh : ∀ᶠN : ℕ in atTop,∀L∈Icc Lmin Lmax,
      4≤(N:ℝ)^(L/10) ∧ (C/(N:ℝ)^(L/10))*
        actualPrimeBoxMass N (fun _ : Fin k => L/10) (fun _ => 3*L/5)<epsilon := by
    filter_upwards [eventually_ge_atTop (2:ℕ),hp.eventually (eventually_ge_atTop (4:ℝ)),
      he.eventually (gt_mem_nhds hepsilon)] with N hN hpower herror L hL
    have hNL : 1<N := by omega
    have hpow : (N:ℝ)^(Lmin/10)≤(N:ℝ)^(L/10) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
        (by linarith [hL.1])
    have hsmall : 0<(N:ℝ)^(Lmin/10) := by positivity
    have hdiv := div_le_div_of_nonneg_left hC hsmall hpow
    have hmass := moving_box_mass_le_ambient (d:=k) hNL hmin hL
    have hmove := actualPrimeBoxMass_nonneg N (fun _ : Fin k => L/10) (fun _ => 3*L/5)
    have hcoef : 0≤C/(N:ℝ)^(Lmin/10) := by positivity
    exact ⟨hpower.trans hpow,(mul_le_mul hdiv hmass hmove hcoef).trans_lt herror⟩
  exact eventually_atTop.mp hh

theorem compact_uniform_true_single {Lmin Lmax lo hi epsilon : ℝ}
    (hmin : 0<Lmin) (hmax : Lmin≤Lmax) (hepsilon : 0<epsilon)
    (hlo : (1/5:ℝ)≤lo) (hhi : hi≤1/2) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀L∈Icc Lmin Lmax,∀d : ℕ,
      |trueSingleMass N L d lo hi-
        (∫x in singleDomain lo hi,1/(x 0*(1-x 0)))|<epsilon := by
  obtain ⟨Tp,hTp⟩ := compact_uniform_scaled_affine hmin hmax (by norm_num : (0:ℝ)≤10)
    (by positivity : 0<epsilon/2) singleForms (singleBounds lo hi) singleForms_ne
    (by rw [← single_as_affine]; exact single_in_cube hlo hhi)
    residualSingle residualSingle_continuous (fun x => by
      rw [abs_of_nonneg (residualSingle_bounds x).1]; exact (residualSingle_bounds x).2)
  obtain ⟨Te,hTe⟩ := compact_multiplier_error (k:=1) hmin hmax (by norm_num : (0:ℝ)≤20)
    (by positivity : 0<epsilon/2)
  refine ⟨max Tp Te,?_⟩
  intro N hN L hL d
  have hp := hTp N (by omega) L hL
  rw [← single_as_affine] at hp
  have hk : (∫x in singleDomain lo hi,residualSingle x*(∏i,1/x i)) =
      ∫x in singleDomain lo hi,1/(x 0*(1-x 0)) := by
    apply setIntegral_congr_fun
    · rw [single_as_affine]; exact measurableSet_primeAffineGateRegion _ _
    · intro x hx; exact single_kernel hhi hx
  rw [hk] at hp
  obtain ⟨hA,he⟩ := hTe N (by omega) L hL
  have hd := single_mass_difference d lo hi hA
  have ht := abs_sub_le (trueSingleMass N L d lo hi)
    (scaledPrimeSum N L (singleDomain lo hi) residualSingle)
    (∫x in singleDomain lo hi,1/(x 0*(1-x 0)))
  linarith

theorem compact_uniform_true_pair {Lmin Lmax epsilon : ℝ}
    (hmin : 0<Lmin) (hmax : Lmin≤Lmax) (hepsilon : 0<epsilon)
    (a : W2Parameters) (ha : W2Geometry a) (k : Fin 4) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀L∈Icc Lmin Lmax,∀d : ℕ,
      |truePairMass N L d a k-
        (∫x in W2PairDomain a k,1/(x 0*x 1*(1-x 0-x 1)))|<epsilon := by
  obtain ⟨Tp,hTp⟩ := compact_uniform_scaled_affine hmin hmax (by norm_num : (0:ℝ)≤10)
    (by positivity : 0<epsilon/2) (pairForms k) (pairBounds a k) (pairForms_ne k)
    (by rw [← pair_as_affine]; exact pair_in_cube ha k)
    residualPair residualPair_continuous (fun x => by
      rw [abs_of_nonneg (residualPair_bounds x).1]; exact (residualPair_bounds x).2)
  obtain ⟨Te,hTe⟩ := compact_multiplier_error (k:=2) hmin hmax (by norm_num : (0:ℝ)≤60)
    (by positivity : 0<epsilon/2)
  refine ⟨max Tp Te,?_⟩
  intro N hN L hL d
  have hp := hTp N (by omega) L hL
  rw [← pair_as_affine] at hp
  have hk : (∫x in W2PairDomain a k,residualPair x*(∏i,1/x i)) =
      ∫x in W2PairDomain a k,1/(x 0*x 1*(1-x 0-x 1)) := by
    apply setIntegral_congr_fun
    · rw [pair_as_affine]; exact measurableSet_primeAffineGateRegion _ _
    · intro x hx; exact pair_kernel ha k hx
  rw [hk] at hp
  obtain ⟨hA,he⟩ := hTe N (by omega) L hL
  have hd := pair_mass_difference d a k hA
  have ht := abs_sub_le (truePairMass N L d a k)
    (W2PairPrimeMass N L a k)
    (∫x in W2PairDomain a k,1/(x 0*x 1*(1-x 0-x 1)))
  change |scaledPrimeSum N L (W2PairDomain a k) residualPair-_|<epsilon/2 at hp
  dsimp only [W2PairPrimeMass] at hd ht
  linarith

/-- All 70 windows share a single threshold before N, L and d. -/
theorem all70_compact_uniform_single_mass {Lmin Lmax epsilon : ℝ}
    (hmin : 0<Lmin) (hmax : Lmin≤Lmax) (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀L∈Icc Lmin Lmax,∀d : ℕ,∀i : Fin 7,∀j : Fin 10,
      |trueSingleMass N L d (1/W1Anchor j) (1/W1Target i)-
        (∫u in W1Domain i j,1/(u*(1-u)))|<epsilon := by
  have hfixed (ij : Fin 7 × Fin 10) : ∀ᶠN : ℕ in atTop,∀L∈Icc Lmin Lmax,∀d : ℕ,
      |trueSingleMass N L d (1/W1Anchor ij.2) (1/W1Target ij.1)-
        (∫u in W1Domain ij.1 ij.2,1/(u*(1-u)))|<epsilon := by
    have hj : (ij.2.val:ℝ)≤9 := by exact_mod_cast (show ij.2.val≤9 by omega)
    have hlo : (1/5:ℝ)≤1/W1Anchor ij.2 :=
      one_div_le_one_div_of_le (by unfold W1Anchor; positivity) (by unfold W1Anchor; linarith)
    have hhi : 1/W1Target ij.1≤(1/2:ℝ) := by
      apply one_div_le_one_div_of_le (by norm_num)
      unfold W1Target
      linarith [show (0:ℝ)≤ij.1.val from Nat.cast_nonneg _]
    obtain ⟨T,hT⟩ := compact_uniform_true_single hmin hmax hepsilon hlo hhi
    filter_upwards [eventually_ge_atTop T] with N hN L hL d
    have hh := hT N hN L hL d
    rw [single_integral_coordinates] at hh
    exact hh
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_all.mpr hfixed)
  exact ⟨T,fun N hN L hL d i j => hT N hN (i,j) L hL d⟩

theorem all36_compact_uniform_singleton_mass {Lmin Lmax epsilon : ℝ}
    (hmin : 0<Lmin) (hmax : Lmin≤Lmax) (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀L∈Icc Lmin Lmax,∀d : ℕ,∀j : Fin 36,∀k : Fin 3,
      |trueSingleMass N L d (a0 (originalW2At j)) (singletonTop (originalW2At j) k)-
        (∫u in W2SingletonDomain (originalW2At j) k,1/(u*(1-u)))|<epsilon := by
  have hfixed (jk : Fin 36 × Fin 3) : ∀ᶠN : ℕ in atTop,∀L∈Icc Lmin Lmax,∀d : ℕ,
      |trueSingleMass N L d (a0 (originalW2At jk.1)) (singletonTop (originalW2At jk.1) jk.2)-
        (∫u in W2SingletonDomain (originalW2At jk.1) jk.2,1/(u*(1-u)))|<epsilon := by
    have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem jk.1)
    have hhi : singletonTop (originalW2At jk.1) jk.2≤(1/2:ℝ) := by
      rcases hg with ⟨h0,h01,h12,h23,h3,hb,hg6,hg7,hg8⟩
      rcases jk with ⟨j,k⟩
      fin_cases k <;> simp only [singletonTop,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two] <;> linarith
    obtain ⟨T,hT⟩ := compact_uniform_true_single hmin hmax hepsilon hg.1 hhi
    filter_upwards [eventually_ge_atTop T] with N hN L hL d
    have hh := hT N hN L hL d
    rw [single_integral_coordinates] at hh
    have he : Ioo (a0 (originalW2At jk.1)) (singletonTop (originalW2At jk.1) jk.2)=
        W2SingletonDomain (originalW2At jk.1) jk.2 := by
      rcases jk with ⟨j,k⟩; fin_cases k <;> rfl
    rwa [he] at hh
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_all.mpr hfixed)
  exact ⟨T,fun N hN L hL d j k => hT N hN (j,k) L hL d⟩

theorem all36_compact_uniform_pair_mass {Lmin Lmax epsilon : ℝ}
    (hmin : 0<Lmin) (hmax : Lmin≤Lmax) (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀L∈Icc Lmin Lmax,∀d : ℕ,∀j : Fin 36,∀k : Fin 4,
      |truePairMass N L d (originalW2At j) k-
        (∫x in W2PairDomain (originalW2At j) k,1/(x 0*x 1*(1-x 0-x 1)))|<epsilon := by
  have hfixed (jk : Fin 36 × Fin 4) : ∀ᶠN : ℕ in atTop,∀L∈Icc Lmin Lmax,∀d : ℕ,
      |truePairMass N L d (originalW2At jk.1) jk.2-
        (∫x in W2PairDomain (originalW2At jk.1) jk.2,1/(x 0*x 1*(1-x 0-x 1)))|<epsilon := by
    obtain ⟨T,hT⟩ := compact_uniform_true_pair hmin hmax hepsilon (originalW2At jk.1)
      (originalRepairedW2Bank_geometry _ (originalW2At_mem jk.1)) jk.2
    exact (eventually_ge_atTop T).mono (fun N hN => hT N hN)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_all.mpr hfixed)
  exact ⟨T,fun N hN L hL d j k => hT N hN (j,k) L hL d⟩

/-- Simultaneous original bank statement: one threshold is chosen before
every residual, every prefix and all 70/36 action labels. -/
theorem bank_compact_uniform_masses {Lmin Lmax epsilon : ℝ}
    (hmin : 0<Lmin) (hmax : Lmin≤Lmax) (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀L∈Icc Lmin Lmax,∀d : ℕ,
      (∀i : Fin 7,∀j : Fin 10,
        |trueSingleMass N L d (1/W1Anchor j) (1/W1Target i)-
          (∫u in W1Domain i j,1/(u*(1-u)))|<epsilon) ∧
      (∀j : Fin 36,∀k : Fin 3,
        |trueSingleMass N L d (a0 (originalW2At j)) (singletonTop (originalW2At j) k)-
          (∫u in W2SingletonDomain (originalW2At j) k,1/(u*(1-u)))|<epsilon) ∧
      (∀j : Fin 36,∀k : Fin 4,
        |truePairMass N L d (originalW2At j) k-
          (∫x in W2PairDomain (originalW2At j) k,1/(x 0*x 1*(1-x 0-x 1)))|<epsilon) := by
  obtain ⟨T1,h1⟩ := all70_compact_uniform_single_mass hmin hmax hepsilon
  obtain ⟨T2,h2⟩ := all36_compact_uniform_singleton_mass hmin hmax hepsilon
  obtain ⟨T3,h3⟩ := all36_compact_uniform_pair_mass hmin hmax hepsilon
  exact ⟨max T1 (max T2 T3),fun N hN L hL d =>
    ⟨h1 N (by omega) L hL d,h2 N (by omega) L hL d,h3 N (by omega) L hL d⟩⟩

end
end ImbalancedChen.P2OriginalCompactThetaMass
