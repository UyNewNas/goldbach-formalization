import ImbalancedChen.P4BOriginalRosserDensityOrder
import ImbalancedChen.P4AOriginalFiniteAll22FineDensity
import ImbalancedChen.P4BCurrentSmoothBadUpperSuppliers

/-! Install the Fine density in the literal attached-coefficient consumer.
The rectangle and the original first-exit rule have their own modulus
sets and signed coefficients. The transfer here concerns density only. -/
namespace ImbalancedChen.P4BOriginalFineAttachedUpper

noncomputable section
open Filter Topology
open P4AOriginalFull87HistoryCore (width)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteAll22FineDensity (modulusFamily coefficientFamily)
open P4AAll22OriginalKLedger20261024zSourceOnly (compilerReserve densityReserve)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)

abbrev retention (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :=
  F (bank m) (width r) n (data e q a) omega N

abbrev meshWidth (m : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ) :=
  alignedWidth (jointIndex (bank m) (data e q a).m) k

abbrev compiledDensity (m r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta : ℝ) (k N : ℕ) :=
  physicalDensitySum (modulusFamily nu beta 0 N)
    (coefficientFamily m r n e q a nu beta k 0 N)

abbrev attachedDensity (m r n : ℕ) (e : ℚ) (q : ℕ) (a nu v beta : ℝ) (N : ℕ) :=
  physicalDensitySum
    (attachedUpperModuli nu v beta (retention m r n e q a (nu * beta ^ 2)) id N)
    (attachedUpperCoefficient nu v beta (retention m r n e q a (nu * beta ^ 2)) id N)

/-- Bundle the already ordered Fine witness and its actual pointwise
receipts. The sharpened entry compares the two displayed native sums. -/
structure Selection (m r n : ℕ) (e : ℚ) (q : ℕ) (a nu v etaPP betaMax extra : ℝ)
    (fineTolerance : ℝ → ℝ) where
  beta : ℝ
  pos : 0 < beta
  lt_eighth : beta < 1 / 8
  lt_ceiling : beta < betaMax
  square_lt : beta ^ 2 < v
  omega_lt : nu * beta ^ 2 < a
  small_lt : nu * beta < 1 / 1000
  small_pp : nu * beta < etaPP / 32
  small_extra : nu * beta < extra / 32
  k : ℕ
  mesh_fine : meshWidth m e q a k ≤ fineTolerance beta
  mesh_pp : meshWidth m e q a k * ((P4AHeldTaggedCompilerSupport.J0 (nu * beta ^ 2) : ℝ) + 1) ≤ etaPP
  mesh_extra : meshWidth m e q a k * ((P4AHeldTaggedCompilerSupport.J0 (nu * beta ^ 2) : ℝ) + 1) ≤ extra
  N0 : ℕ
  two_le : 2 ≤ N0
  receipt : ∀ N ≥ N0, Even N →
    let omega := nu * beta ^ 2
    let tau := meshWidth m e q a k
    let w := (N : ℝ) ^ omega
    let z := cutoff N
    let L := (N : ℝ) ^ (nu * beta)
    let f := retention m r n e q a omega N
    let Q := modulusFamily nu beta 0 N
    let rho := coefficientFamily m r n e q a nu beta k 0 N
    let upper := P4AOriginalFiniteAll22CofinalCoefficient.upper m r n e q a omega (densityReserve / 2) N
    attachedDensity m r n e q a nu v beta N ≤ compiledDensity m r n e q a nu beta k N ∧
    P4AOriginalFiniteFallbackAllHighAtoms.HighAtoms m n N (width r) omega tau (nu * beta) etaPP (data e q a) ∧
    ((N : ℝ) / Real.log (N : ℝ)) *
      P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L <
        compilerReserve * singularNormalization N ∧
    physicalDensitySum Q rho < upper ∧
    physicalDensitySum Q rho ≤ currentK * (singularSeries N / Real.log (N : ℝ)) ∧
    (∀ d : ℕ, rho d ≠ 0 → (d : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) ∧
    ∀ b T : ℝ, 0 < b → b < 1 → 0 < T → (Nat.ceil z : ℝ) ≤ T ^ (b / (1 + b)) →
      (RealB b N : ℝ) ≤ ((realHalfProductSource b N T).card : ℝ) * upper +
        realPhysicalDistributionError b N T Q rho + (Nat.ceil z : ℝ) + (T + 1)

theorem exists_fine_selection (eMax : ℝ) (heMax : 0 < eMax) :
    ∃ m0 : ℕ, ∀ m ≥ m0, ∃ r0 : ℕ, ∀ r ≥ r0, ∃ n0 : ℕ, ∀ n ≥ n0,
    ∃ E : ℝ, 0 < E ∧ E ≤ eMax ∧ ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < E →
    ∀ a : ℝ, 0 < a → a ≤ 1 / 800 → ∀ qMin mMin : ℕ,
    ∃ q : ℕ, qMin ≤ q ∧ 0 < q ∧ 256 ∣ q ∧ mMin ≤ refinedMesh q ∧
    ∀ etaPP : ℝ, 0 < etaPP → etaPP ≤ P4AOriginalFiniteFallbackCommonGroups.gap m (data e q a) →
    ∀ nu v betaMax extra : ℝ, 0 < nu → 0 < v → nu * v = 19 / 96 → 0 < betaMax → 0 < extra →
    ∀ fineTolerance : ℝ → ℝ, (∀ x : ℝ, 0 < x → 0 < fineTolerance x) →
      Nonempty (Selection m r n e q a nu v etaPP betaMax extra fineTolerance) := by
  obtain ⟨B, hB, hOrder⟩ := P4BOriginalRosserDensityOrder.exists_eventual_raw_le_compiled
  obtain ⟨m0, hm0⟩ := P4AOriginalFiniteAll22FineDensity.exists_fine_same_rho_hdensity eMax heMax
  refine ⟨m0, ?_⟩
  intro m hm
  obtain ⟨r0, hr0⟩ := hm0 m hm
  refine ⟨r0, ?_⟩
  intro r hr
  obtain ⟨n0, hn0⟩ := hr0 r hr
  refine ⟨n0, ?_⟩
  intro n hn
  obtain ⟨E, hE, hEmax, hEarly⟩ := hn0 n hn
  refine ⟨E, hE, hEmax, ?_⟩
  intro e he heE a ha haMax qMin mMin
  obtain ⟨q, hqMin, hq, hdiv, hmesh, hFine⟩ := hEarly e he heE a ha haMax qMin mMin
  refine ⟨q, hqMin, hq, hdiv, hmesh, ?_⟩
  intro etaPP hPP hgap nu v betaMax extra hnu hv hcut hMax hExtra ft hft
  obtain ⟨beta, hb, hb8, hbMax, hbSq, hw, hsmall, hbPP, hbExtra, k, hfine, hmPP, hmExtra,
      _, N0, hN0, hOld⟩ :=
    hFine etaPP hPP hgap nu v (min betaMax B) extra hnu hv hcut (lt_min hMax hB) hExtra ft hft
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp
    (hOrder nu beta hnu hb hb8 (hbMax.trans_le (min_le_right _ _)))
  refine ⟨⟨beta, hb, hb8, hbMax.trans_le (min_le_left _ _), hbSq, hw, hsmall, hbPP,
    hbExtra, k, hfine, hmPP, hmExtra, max N0 N1, hN0.trans (le_max_left _ _), ?_⟩⟩
  intro N hN hEven
  refine ⟨?_, hOld N ((le_max_left _ _).trans hN) hEven⟩
  have ho := hN1 N ((le_max_right _ _).trans hN) hEven N
    (retention m r n e q a (nu * beta ^ 2) N) (fun _ => []) (cutoff N) (meshWidth m e q a k)
  change p4aReservePhysicalDensity (retention m r n e q a (nu * beta ^ 2) N) N N
    ((N : ℝ) ^ (nu * beta ^ 2)) ((N : ℝ) ^ (nu * v)) ((N : ℝ) ^ (nu * beta)) ≤ _
  rw [hcut]
  exact ho

/-- Realize every selection needed by the two upper receivers, including
the numerical `e` and `q` gates in the original short-medium count.
The original cofinal denominator and grid requests are still available. -/
theorem exists_counting_selection (a zeta betaMax : ℝ) (ha : 0 < a) (haMax : a ≤ 1 / 800)
    (hz : 0 < zeta) (hb : 0 < betaMax) (ft : ℝ → ℝ) (hft : ∀ x : ℝ, 0 < x → 0 < ft x)
    (qMin mMin : ℕ) :
    ∃ (m r n : ℕ) (e : ℚ) (q : ℕ) (etaPP : ℝ),
      0 < e ∧ (e : ℝ) < 1 / 2048 ∧ qMin ≤ q ∧ 0 < q ∧ 256 ∣ q ∧ mMin ≤ refinedMesh q ∧
      0 < etaPP ∧ etaPP ≤ P4AOriginalFiniteFallbackCommonGroups.gap m (data e q a) ∧
      Nonempty (Selection m r n e q a 1 (19 / 96) etaPP betaMax zeta ft) := by
  obtain ⟨m, hm⟩ := exists_fine_selection (1 / 2048) (by norm_num)
  obtain ⟨r, hr⟩ := hm m le_rfl
  obtain ⟨n, hn⟩ := hr r le_rfl
  obtain ⟨E, hE, hEmax, hEarly⟩ := hn n le_rfl
  obtain ⟨e, he, heE⟩ := exists_rat_btwn hE
  have heQ : (0 : ℚ) < e := by exact_mod_cast he
  obtain ⟨q, hqMin, hq, hd, hmesh, hChoose⟩ := hEarly e he heE a ha haMax qMin mMin
  let g := P4AOriginalFiniteFallbackCommonGroups.gap m (data e q a)
  have hg : 0 < g := P4AOriginalFiniteFallbackCommonGroups.gap_pos m (data e q a) heQ
  refine ⟨m, r, n, e, q, g, heQ, heE.trans_le hEmax, hqMin, hq, hd, hmesh, hg, le_rfl, ?_⟩
  exact hChoose g hg le_rfl 1 (19 / 96) betaMax zeta zero_lt_one (by norm_num)
    (by norm_num) hb hz ft hft

namespace Selection

variable {m r n q : ℕ} {e : ℚ} {a nu v etaPP betaMax extra : ℝ} {ft : ℝ → ℝ}

theorem compiled_K (s : Selection m r n e q a nu v etaPP betaMax extra ft) :
    ∀ᶠ N : ℕ in atTop, Even N → compiledDensity m r n e q a nu s.beta s.k N ≤
      currentK * (singularSeries N / Real.log (N : ℝ)) := by
  filter_upwards [eventually_ge_atTop s.N0] with N hN
  intro hEven
  exact (s.receipt N hN hEven).2.2.2.2.1

theorem attached_K (s : Selection m r n e q a nu v etaPP betaMax extra ft) :
    ∀ᶠ N : ℕ in atTop, Even N → attachedDensity m r n e q a nu v s.beta N ≤
      currentK * (singularSeries N / Real.log (N : ℝ)) := by
  filter_upwards [eventually_ge_atTop s.N0] with N hN
  intro hEven
  have h := s.receipt N hN hEven
  exact h.1.trans h.2.2.2.2.1

/-- The existing all-width consumer now takes only its actual signed PP
input. Every precision uses this fixed beta, retention and integral cap. -/
theorem upper_of_attached_PP (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    {b kappa : ℝ} (hb : (1 / 2 : ℝ) < b) (hb1 : b < 1) (hk : 0 < kappa)
    (hk1 : kappa < 1) (hnu : 0 < nu) (hv : 0 < v) (hcut : nu * v = 19 / 96)
    (hgap : nu * v < (1 - kappa) * b / (1 + b))
    (hPP : ∀ physicalWidth : ℝ, 0 < physicalWidth →
      2 * physicalWidth ≤ (1 - kappa) * b / (1 + b) - nu * v →
      Part3.UniformPrimeProductTarget (ι := Unit) 2 id
        (attachedUpperModuli nu v s.beta (retention m r n e q a (nu * s.beta ^ 2)) id)
        (attachedUpperCoefficient nu v s.beta (retention m r n e q a (nu * s.beta ^ 2)) id)
        (fun N _ => P4B.smoothPhysicalPairOuterRamp b N
          (manuscriptHalfProductCutoff kappa N) physicalWidth)) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤ (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  apply P4BCurrentSmoothBadUpperSuppliers.current_realBad_upper_of_actual_density_and_uniform_smooth_PP
    hb hb1 hk hk1 hnu hv hgap (fun _ => s.beta)
    (fun _ => retention m r n e q a (nu * s.beta ^ 2)) (fun _ => id)
  · intro _ _
    exact ⟨s.pos, s.lt_eighth.le.trans (by norm_num), s.square_lt.le⟩
  · intro _ _
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [hcut]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hone (show (19 / 96 : ℝ) ≤ 1 by norm_num)
  · intro delta hdelta
    filter_upwards [s.attached_K, eventually_ge_atTop (2 : ℕ)] with N hd hN
    intro hEven
    exact (hd hEven).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hdelta.le) (densityScale_pos hN).le)
  · intro _ _
    exact hPP

end Selection
end
end ImbalancedChen.P4BOriginalFineAttachedUpper
