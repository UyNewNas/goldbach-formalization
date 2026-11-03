import ImbalancedChen.P2GammaU5PlateauMass

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Consume the actual positive-mass plateau supplier, not a caller hmass.
This gives real relative-Theta endpoints on a concrete original U5 fibre,
with one threshold before every later constant amplitude. The compact
policy, original physical modulus carrier, rank remainder and empty lane
are unchanged. No claim about the source outside this fibre is made.
-/
namespace ImbalancedChen.P2GammaU5PlateauRelative
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaU5PlateauGeometry P2GammaU5PlateauMass
open P2GammaSelectedPhysicalTheta P2GammaSelectedRelativeLogSaving
open P2GammaRootFiberRelative P2GammaRankScaledUpperSource
open P2GammaActualUpperLowRankReduction

/-- The actual root fibre has its mass supplied. No mass floor, root-level
identification, positivity of Theta or count limit is a theorem premise. -/
theorem eventually_plateau_rank_relative (A : ℕ) (kappa : ℝ)
    (hk0 : 0 < kappa) (hk : kappa < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,∀ nu epsilon : ℝ,0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (height : ℝ),0 < height →
      |rankResidual N kappa nu epsilon retain cap k (plateauFiber N) (fun _ => height)| ≤
        eta*selectedTheta N (plateauQ N) (plateauFiber N) (fun _ => height)/
          (Real.log (N : ℝ))^A := by
  filter_upwards [eventually_rootFiber_rank_relative A 0 massFloor massFloor_pos
      kappa hk0 hk eta heta,eventually_plateau_constant_mass] with N hrel hm
  intro k nu epsilon hnu hgap retain cap height hh
  apply hrel k nu epsilon hnu hgap retain cap (plateauQ N) height hh
    (fun _ => True) (fun _ => height) (fun _ _ => ⟨hh.le,le_refl _⟩)
  exact Or.inr (by simpa only [pow_zero,div_one,plateauFiber] using hm height hh.le)

/-- Stable masked extension: it is enough to dominate the actual box
pointwise. Its reciprocal mass and physical root identity are supplied.
This does not assert that the missing global causal keep mask dominates it. -/
theorem eventually_plateau_dominated_relative (A : ℕ)
    (fraction : ℝ) (hf : 0 < fraction) (kappa : ℝ)
    (hk0 : 0 < kappa) (hk : kappa < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,∀ nu epsilon : ℝ,0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (height : ℝ),0 < height →
      ∀ sigma : Pair → ℝ,
      (∀ t ∈ plateauFiber N,0 ≤ sigma t ∧ sigma t ≤ height) →
      (∀ t ∈ rectangle N,fraction*height ≤ sigma t) →
      |rankResidual N kappa nu epsilon retain cap k (plateauFiber N) sigma| ≤
        eta*selectedTheta N (plateauQ N) (plateauFiber N) sigma/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_rootFiber_rank_relative A 0 (fraction*massFloor)
      (mul_pos hf massFloor_pos) kappa hk0 hk eta heta,
    eventually_plateau_dominated_mass fraction hf.le] with N hrel hm
  intro k nu epsilon hnu hgap retain cap height hh sigma hs hrect
  apply hrel k nu epsilon hnu hgap retain cap (plateauQ N) height hh
    (fun _ => True) sigma hs
  exact Or.inr (by simpa only [pow_zero,div_one,plateauFiber] using
    hm height hh.le sigma (fun t ht => (hs t ht).1) hrect)

/-- Actual compact source, all terms on its original physical moduli.
The high-rank and empty-word terms stay explicit; this theorem pays only
the already-constructed nonempty rank lane on the real plateau fibre. -/
theorem eventually_actualCompact_plateau_relative (A : ℕ) (kappa : ℝ)
    (hk0 : 0 < kappa) (hk : kappa < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,∀ nu epsilon : ℝ,0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (e h : ℝ) (m cap : ℕ) (height : ℝ),0 < height →
      let retain := actualExtendedThirdCompactUpperPolicy e h m N false
      let moduli := physicalUpperModuli N nu epsilon retain cap
      let S := plateauFiber N
      |selectedGamma N moduli (fullUpperRho N nu epsilon retain cap) S (fun _ => height) -
        selectedGamma N moduli (rankRemainder N nu epsilon retain cap k) S (fun _ => height) -
        selectedEmpty N moduli (rankUpperRho N nu epsilon retain cap k)
          ((N : ℝ)^(1-kappa)) S (fun _ => height)| ≤
        eta*selectedTheta N (plateauQ N) S (fun _ => height)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_actualCompact_rootFiber_relative A 0 massFloor massFloor_pos
      kappa hk0 hk eta heta,eventually_plateau_constant_mass] with N hrel hm
  intro k nu epsilon hnu hgap e h m cap height hh
  apply hrel k nu epsilon hnu hgap e h m cap (plateauQ N) height hh
    (fun _ => True) (fun _ => height) (fun _ _ => ⟨hh.le,le_refl _⟩)
  exact Or.inr (by simpa only [pow_zero,div_one,plateauFiber] using hm height hh.le)

/-- Numerical coefficient data are supplied too: choose nu to be the
ACTUAL plateau root exponent and k=3. This is a concrete admissible upper
coefficient, not an assertion that it equals the final full87 coefficient.
The common threshold precedes epsilon, compact parameters and height. -/
theorem eventually_actualCompact_plateau_rank_three (A : ℕ) (kappa : ℝ)
    (hk0 : 0 < kappa) (hk : kappa ≤ 1/100) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ epsilon : ℝ,0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (e h : ℝ) (m cap : ℕ) (height : ℝ),0 < height →
      let retain := actualExtendedThirdCompactUpperPolicy e h m N false
      let moduli := physicalUpperModuli N plateauLevel epsilon retain cap
      let S := plateauFiber N
      |selectedGamma N moduli (fullUpperRho N plateauLevel epsilon retain cap) S
          (fun _ => height) -
        selectedGamma N moduli (rankRemainder N plateauLevel epsilon retain cap 3) S
          (fun _ => height) -
        selectedEmpty N moduli (rankUpperRho N plateauLevel epsilon retain cap 3)
          ((N : ℝ)^(1-kappa)) S (fun _ => height)| ≤
        eta*selectedTheta N (plateauQ N) S (fun _ => height)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_actualCompact_plateau_relative A kappa hk0
    (by linarith : kappa < 1) eta heta] with N hN
  intro epsilon he0 he e h m cap height hh
  have hnu : (0 : ℝ) ≤ plateauLevel := by rw [plateauLevel_exact]; norm_num
  have hnucap : plateauLevel ≤ (37/50 : ℝ) := by rw [plateauLevel_exact]; norm_num
  exact hN 3 plateauLevel epsilon hnu (rank_three_gap hnu hnucap he hk)
    e h m cap height hh

/-- The untouched complementary original source is always displayed. -/
theorem plateau_residual_partition (N : ℕ) (moduli : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℝ) (sigma : Pair → ℝ) :
    selectedResidual N moduli rho T (P5OriginalU5CausalFinite.pairSupport N) sigma =
      selectedResidual N moduli rho T (plateauFiber N) sigma +
      selectedResidual N moduli rho T
        (P5OriginalU5CausalFinite.pairSupport N \ plateauFiber N) sigma :=
  rootFiber_residual_partition N (plateauQ N) (fun _ => True) moduli rho T sigma

end
end ImbalancedChen.P2GammaU5PlateauRelative
