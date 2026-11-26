import ImbalancedChen.P1OriginalSingletonPhysicalSupport
import ImbalancedChen.Part3TwoLongActualHBShortMass
import ImbalancedChen.P1OriginalSingletonTwoLongFiniteGeometry
import ImbalancedChen.RestrictedResidueScale
import ImbalancedChen.P1OriginalHistoricalMiddlePointwiseData

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

X0 is the product of all original block lower endpoints. It is fixed by
the rectangle, independently of its actual integer tuple, short product,
modulus, coefficient and Fourier mode. The two supplied occurrence indices
are retained; neither is selected again as m or q varies.

The old dyadic product window supplies the support of EVERY rectangle
point and fixed-m long fibre. A single actual nonzero profile is used only
to compare the fixed X0 with physical N. The existing general manuscript
threshold is instantiated with c = 1/64 and C = 2. No tuple-local scale is
asserted to be constant throughout a rectangle or a fibre.

The modulus expression is exactly historicalModuli unfolded, using its
canonical remainingModuli/trueD support definitions. There is no import
of HistoricalTwoLongP2, PhysicalLevel, LongComplement or the missing fixed-M
core through those providers. Inherited unresolved Fourier source imports
remain documented; no complete transitive source closure is claimed.
-/

namespace ImbalancedChen.P1OriginalSingletonFixedRectangleScale
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)
open P5Z.ActualLowerNormalizedBlockGeometry (blockIntegers mem_blockIntegers rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile)
open Part3.TwoLongActualHBShortMass
  (ShortPositions shortRectangle shortScale shortProduct shortSupport
    shortProduct_window product_two_positions)
open P4BOriginalNoMediumPairRows (short_card)
open P1OriginalSingletonPhysicalLevel (scalarProfile_complete_support)
open P1Full87HistoricalMiddleSmoothing (remainingModuli)
open P1Full87TrueDPolicyDelta (trueDDeltaSupport)

/-- The original finite rectangle and its fixed-short-product fibres share
one block scale. Short-product collisions, units and repeated occurrence
values are retained. The supplied i,k are fixed before every m,u,v. -/
theorem fixed_rectangle_fibre_window {r : ℕ} (bs : Fin r → Block)
    (i k : Fin r) (hik : i ≠ k) :
    let M := shortScale (fun a : ShortPositions i k => bs a.val)
    shortScale bs = lower (bs i) * lower (bs k) * M ∧
      Fintype.card (ShortPositions i k) + 2 = r ∧
      (∀ ns ∈ rectangle bs,
        shortScale bs ≤ completeProduct ns ∧
          completeProduct ns ≤ 2^r * shortScale bs) ∧
      ∀ m ∈ shortSupport (fun a : ShortPositions i k => bs a.val),
        0 < m ∧ M ≤ m ∧ m ≤ 2 ^ Fintype.card (ShortPositions i k) * M ∧
          ∀ u ∈ blockIntegers (bs i), ∀ v ∈ blockIntegers (bs k),
            shortScale bs ≤ m*u*v ∧ m*u*v ≤ 2^r * shortScale bs := by
  let M := shortScale (fun a : ShortPositions i k => bs a.val)
  have hscale : shortScale bs = lower (bs i) * lower (bs k) * M :=
    product_two_positions i k hik (fun a => lower (bs a))
  have hcard := short_card i k hik
  refine ⟨hscale, hcard, ?_, ?_⟩
  · intro ns hns
    simpa only [shortProduct, completeProduct, Fintype.card_fin] using
      shortProduct_window bs (show ns ∈ shortRectangle bs from hns)
  · intro m hm
    obtain ⟨s, hs, hsm⟩ := Finset.mem_image.mp hm
    have hw := shortProduct_window (fun a : ShortPositions i k => bs a.val) hs
    have hM0 : 0 < M := Finset.prod_pos (fun a _ => lower_pos (bs a.val))
    have hml : M ≤ m := by simpa only [hsm] using hw.1
    have hmu : m ≤ 2 ^ Fintype.card (ShortPositions i k) * M := by
      simpa only [hsm] using hw.2
    refine ⟨hM0.trans_le hml, hml, hmu, ?_⟩
    intro u hu v hv
    have hub := owns_bounds ((mem_blockIntegers _ _).mp hu)
    have hvb := owns_bounds ((mem_blockIntegers _ _).mp hv)
    constructor
    · calc
        shortScale bs = M * lower (bs i) * lower (bs k) := by rw [hscale]; ring
        _ ≤ m*u*v := Nat.mul_le_mul (Nat.mul_le_mul hml hub.1) hvb.1
    · calc
        m*u*v ≤ (2 ^ Fintype.card (ShortPositions i k) * M) *
            (2 * lower (bs i)) * (2 * lower (bs k)) :=
          Nat.mul_le_mul (Nat.mul_le_mul hmu hub.2) hvb.2
        _ = (2 ^ Fintype.card (ShortPositions i k) * 4) * shortScale bs := by
          rw [hscale]
          ring
        _ = 2 ^ (Fintype.card (ShortPositions i k) + 2) * shortScale bs := by
          rw [pow_add]
          norm_num
        _ = 2^r * shortScale bs := by rw [hcard]

/-- A fixed rectangle-scale invoice for one genuine active singleton point.
The original dictionary supplies ns, bs and the fixed i,k; this theorem
does not reselect them or assume activity of an aggregate or full rectangle.

Only the active point pays the physical-N comparison. The uniform support
of all other rectangle points and fixed-m fibres is finite dyadic geometry.
The physical threshold precedes every chart/row/tuple and all historical
coefficient parameters. The Q expression is the original historical one. -/
theorem eventually_actual_singleton_fixed_rectangle_level
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 400)
    (htrim : kap0 < kappa / (4 * (1 + kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (B cj j : ℕ) (bs : Fin (2*(j+1)) → Block)
        (ns : Fin (2*(j+1)) → ℕ) (i k : Fin (2*(j+1))),
      j ∈ Finset.range 3 → i ≠ k → ns ∈ rectangle bs →
      scalarProfile kap B N cj kap0 (completeProduct ns) ≠ 0 →
      let X0 : ℝ := shortScale bs
      let M := shortScale (fun a : ShortPositions i k => bs a.val)
      2*(j+1) ≤ 6 ∧ Fintype.card (ShortPositions i k) ≤ 4 ∧
        X0 = (M : ℝ) * (lower (bs i) : ℝ) * (lower (bs k) : ℝ) ∧
        (1 / 64 : ℝ) * (N : ℝ) ^ (1 - kap0) < X0 ∧ X0 ≤ 2 * (N : ℝ) ∧
        1 < X0 ∧ (1 / 2 : ℝ) * X0 ≤ N ∧ (N : ℝ) ≤ X0 ^ (1 + kappa) ∧
        (∀ ys ∈ rectangle bs,
          X0 ≤ (completeProduct ys : ℝ) ∧ (completeProduct ys : ℝ) ≤ 64 * X0) ∧
        (∀ m ∈ shortSupport (fun a : ShortPositions i k => bs a.val),
          0 < m ∧ M ≤ m ∧ m ≤ 16 * M ∧
            ∀ u ∈ blockIntegers (bs i), ∀ v ∈ blockIntegers (bs k),
              X0 ≤ ((m*u*v : ℕ) : ℝ) ∧ ((m*u*v : ℕ) : ℝ) ≤ 64 * X0) ∧
        ∀ (levelB : ℝ) (old fresh : List ℕ → Bool)
          (cap : ℕ) (w z : ℝ) (q : ℕ),
          q ∈ remainingModuli levelB N (trueDDeltaSupport old fresh N cap w z) →
          (q : ℝ) < X0 ^ (1199 / 2000 : ℝ) ∧ q ≤ ⌊X0 ^ (1199 / 2000 : ℝ)⌋₊ := by
  obtain ⟨_, N0, hN0, H⟩ := exists_manuscript_restrictedResidueScale_threshold
    (c := (1 / 64 : ℝ)) (C := (2 : ℝ)) (κ := kappa) (κ₀ := kap0)
    (by norm_num) (by norm_num) hkappa htrim
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro kap hkap B cj j bs ns i k hj hik hns hactive
  let X0 : ℝ := shortScale bs
  let M := shortScale (fun a : ShortPositions i k => bs a.val)
  have hr : 2*(j+1) ≤ 6 := by have hj' := Finset.mem_range.mp hj; omega
  have hpow : 2^(2*(j+1)) ≤ 64 := by
    calc
      _ ≤ (2 : ℕ)^6 := Nat.pow_le_pow_right (by norm_num) hr
      _ = 64 := by norm_num
  obtain ⟨hscale, hcard, hrectangle, hfibre⟩ := fixed_rectangle_fibre_window bs i k hik
  have hfour : Fintype.card (ShortPositions i k) ≤ 4 := by omega
  have hshortPow : 2 ^ Fintype.card (ShortPositions i k) ≤ 16 := by
    calc
      _ ≤ (2 : ℕ)^4 := Nat.pow_le_pow_right (by norm_num) hfour
      _ = 16 := by norm_num
  have hwindow (ys : Fin (2*(j+1)) → ℕ) (hys : ys ∈ rectangle bs) :
      shortScale bs ≤ completeProduct ys ∧ completeProduct ys ≤ 64 * shortScale bs :=
    ⟨(hrectangle ys hys).1,
      (hrectangle ys hys).2.trans (Nat.mul_le_mul_right _ hpow)⟩
  obtain ⟨hactiveLow, hactiveHigh⟩ := scalarProfile_complete_support kap hkap B N cj kap0
    (by omega) hactive
  have hlow : X0 ≤ (completeProduct ns : ℝ) := by exact_mod_cast (hwindow ns hns).1
  have hhigh : (completeProduct ns : ℝ) ≤ 64 * X0 := by exact_mod_cast (hwindow ns hns).2
  have htrimX : (1 / 64 : ℝ) * (N : ℝ) ^ (1 - kap0) < X0 := by
    linarith only [hactiveLow, hhigh]
  have hcapX : X0 ≤ 2 * (N : ℝ) := hlow.trans hactiveHigh
  obtain ⟨hx, hxN, hNx⟩ := H N hN X0 htrimX.le hcapX
  have hscaleR : X0 = (M : ℝ) * (lower (bs i) : ℝ) * (lower (bs k) : ℝ) := by
    calc
      X0 = (lower (bs i) : ℝ) * (lower (bs k) : ℝ) * (M : ℝ) := by
        exact_mod_cast hscale
      _ = _ := by ring
  refine ⟨hr, hfour, hscaleR, htrimX, hcapX, hx, by simpa only [one_div] using hxN,
    hNx, ?_, ?_, ?_⟩
  · intro ys hys
    constructor
    · exact_mod_cast (hwindow ys hys).1
    · exact_mod_cast (hwindow ys hys).2
  · intro m hm
    obtain ⟨hm0, hml, hmu, huv⟩ := hfibre m hm
    refine ⟨hm0, hml, hmu.trans (Nat.mul_le_mul_right _ hshortPow), ?_⟩
    intro u hu v hv
    constructor
    · exact_mod_cast (huv u hu v hv).1
    · exact_mod_cast (huv u hu v hv).2.trans (Nat.mul_le_mul_right _ hpow)
  · intro levelB old fresh cap w z q hq
    have hqN : (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) :=
      (Finset.mem_filter.mp hq).2.2
    have hpower : (1 + kappa) * (599 / 1000 : ℝ) ≤ 1199 / 2000 := by
      linarith only [hsmall, hzeta]
    have hqX : (q : ℝ) < X0 ^ (1199 / 2000 : ℝ) := by
      calc
        (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := hqN
        _ ≤ (X0 ^ (1 + kappa)) ^ (599 / 1000 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (by norm_num)
        _ = X0 ^ ((1 + kappa) * (599 / 1000 : ℝ)) :=
          (Real.rpow_mul (zero_lt_one.trans hx).le _ _).symm
        _ ≤ X0 ^ (1199 / 2000 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx.le hpower
    exact ⟨hqX, Nat.le_floor hqX.le⟩

end
end ImbalancedChen.P1OriginalSingletonFixedRectangleScale
