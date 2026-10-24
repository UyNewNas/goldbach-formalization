import ImbalancedChen.P4BSupportedRampStripUnion
import ImbalancedChen.P4BOrderBoundaryMass
import ImbalancedChen.P4BLowerProductStripMass

/-!
# Actual jointly supported ordering-strip mass reserve

YELLOW / SOURCE ONLY / UNCOMPILED. Imports are intended staged names of
the sibling source-only drafts. The counted object is exactly the public
physicalSupportedStrip at wall 0. The proof uses its order collar and its
joint upper-product support. Other gates remain in the actual set, but
need not be discarded by changing its definition. No strip-smallness or
mass-limit hypothesis is assumed. All claims are unweighted cardinalities.
-/

namespace ImbalancedChen.P4BSupportedOrderStripMass

noncomputable section

open Filter Topology
open ImbalancedChen.Part3 ImbalancedChen.P4B
open ImbalancedChen.P4BLabelledPairDictionary
open ImbalancedChen.P4BOrderBoundaryMass

theorem supported_order_strip_mono {small large b T : ℝ} {N : ℕ}
    (hle : small ≤ large) :
    physicalSupportedStrip small b N T 0 ⊆ physicalSupportedStrip large b N T 0 := by
  intro t ht
  obtain ⟨hprime, hstrip, hsoft⟩ := mem_physicalSupportedStrip.mp ht
  apply mem_physicalSupportedStrip.mpr
  refine ⟨hprime, ⟨?_, hstrip.2⟩, ?_⟩
  · linarith only [hle, hstrip.1]
  · intro j
    have hj := hsoft j
    linarith only [hle, hj]

/-- Joint physical support puts products below exp(width)*N<=2N.
The order collar becomes a closed absolute-width collar at M=2N,
since its denominator log M is at least log N. -/
theorem supported_order_geometry {width b T : ℝ} {N : ℕ}
    (hN : 2 ≤ N) (hwidth : 0 < width) (hwidth2 : width ≤ Real.log 2)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ physicalSupportedStrip width b N T 0) :
    Nat.Prime (tuplePair t).1 ∧ Nat.Prime (tuplePair t).2 ∧
      (tuplePair t).1 * (tuplePair t).2 ≤ 2 * N ∧
      |normalizedLog (2 * N) (tuplePair t).1 -
        normalizedLog (2 * N) (tuplePair t).2| ≤ width := by
  obtain ⟨htPrime, hstrip, hsoft⟩ := mem_physicalSupportedStrip.mp ht
  have hp : ∀ i : Fin 2, Nat.Prime (t i).val := (Finset.mem_filter.mp htPrime).2
  let r : ℕ := (tuplePair t).1
  let q : ℕ := (tuplePair t).2
  have hr : Nat.Prime r := hp 0
  have hq : Nat.Prime q := hp 1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans hN1
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hNM : N ≤ 2 * N := by omega
  have hM : 2 ≤ 2 * N := by omega
  have hM1 : (1 : ℝ) < (2 * N : ℕ) := by
    exact_mod_cast (show 1 < 2 * N by omega)
  have hlogM : 0 < Real.log (2 * N : ℕ) := Real.log_pos hM1
  have hlogs : Real.log (N : ℝ) ≤ Real.log (2 * N : ℕ) :=
    Real.log_le_log hNpos (Nat.cast_le.mpr hNM)
  have horder : -width < normalizedLog N q - normalizedLog N r ∧
      normalizedLog N q - normalizedLog N r ≤ 0 := by
    simpa [physicalPairMargins, physicalProductWallScale, actualPairMargins,
      P4BLabelledLogGeometry.logPoint, normalizedLog, r, q, tuplePair] using hstrip
  dsimp only [normalizedLog] at horder
  have hnorm0 : 0 ≤ (Real.log (r : ℝ) - Real.log (q : ℝ)) / Real.log (N : ℝ) := by
    rw [sub_div]
    linarith only [horder.2]
  have hnormLt : (Real.log (r : ℝ) - Real.log (q : ℝ)) / Real.log (N : ℝ) < width := by
    rw [sub_div]
    linarith only [horder.1]
  have hdiff0 : 0 ≤ Real.log (r : ℝ) - Real.log (q : ℝ) := by
    simpa only [zero_mul] using (le_div_iff₀ hlogN).mp hnorm0
  have hdiffN : Real.log (r : ℝ) - Real.log (q : ℝ) < width * Real.log (N : ℝ) :=
    (div_lt_iff₀ hlogN).mp hnormLt
  have hdiffM : Real.log (r : ℝ) - Real.log (q : ℝ) ≤ width * Real.log (2 * N : ℕ) :=
    hdiffN.le.trans (mul_le_mul_of_nonneg_left hlogs hwidth.le)
  have habs : |normalizedLog (2 * N) r - normalizedLog (2 * N) q| ≤ width := by
    dsimp only [normalizedLog]
    rw [← sub_div, abs_of_nonneg (div_nonneg hdiff0 hlogM.le)]
    exact (div_le_iff₀ hlogM).mpr hdiffM
  have hsoft3 := hsoft (3 : Fin 4)
  rw [physicalPairMargins_upper_eq_log_gap b T hN1 t] at hsoft3
  have hproductExp : ((r * q : ℕ) : ℝ) < Real.exp width * (N : ℝ) := by
    rw [Nat.cast_mul]
    apply (Real.log_lt_log_iff (mul_pos hrR hqR)
      (mul_pos (Real.exp_pos width) hNpos)).mp
    rw [Real.log_mul hrR.ne' hqR.ne',
      Real.log_mul (Real.exp_pos width).ne' hNpos.ne', Real.log_exp]
    change -width < Real.log (N : ℝ) - Real.log (r : ℝ) - Real.log (q : ℝ) at hsoft3
    linarith only [hsoft3]
  have hexp : Real.exp width ≤ 2 := by
    calc
      Real.exp width ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hwidth2
      _ = 2 := Real.exp_log (by norm_num)
  have hproductReal : ((r * q : ℕ) : ℝ) ≤ 2 * (N : ℝ) :=
    hproductExp.le.trans (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg N))
  have hproduct : r * q ≤ 2 * N := by exact_mod_cast hproductReal
  exact ⟨hr, hq, hproduct, habs⟩

/-- Split only at the actual product cutoff for M=2N. The high part
injects into the order strip there; all low products are paid by their
genuine two-orientations product count, without a lower-collar premise. -/
theorem supported_order_card_le_orderStrip_add_two_ceil {kappa width b T : ℝ} {N : ℕ}
    (hN : 2 ≤ N) (hwidth : 0 < width) (hwidth2 : width ≤ Real.log 2) :
    (physicalSupportedStrip width b N T 0).card ≤
      (orderStrip kappa width (2 * N)).card +
        2 * Nat.ceil (manuscriptHalfProductCutoff kappa (2 * N)) := by
  classical
  let S := physicalSupportedStrip width b N T 0
  let U := manuscriptHalfProductCutoff kappa (2 * N)
  let H := S.filter (fun t => U ≤ ((tuplePair t).1 * (tuplePair t).2 : ℕ))
  let L := S.filter (fun t => ¬U ≤ ((tuplePair t).1 * (tuplePair t).2 : ℕ))
  have hhigh : H.card ≤ (orderStrip kappa width (2 * N)).card := by
    apply Finset.card_le_card_of_injOn (fun t => tuplePair t)
    · intro t ht
      obtain ⟨htS, hcut⟩ := Finset.mem_filter.mp ht
      obtain ⟨hr, hq, hprod, habs⟩ := supported_order_geometry hN hwidth hwidth2 htS
      exact mem_orderStrip.mpr ⟨hr, hq, hcut, hprod, habs⟩
    · intro t ht u hu heq
      exact tuplePair_injective N heq
  let lowPairs := L.image (fun t => tuplePair t)
  have himage : lowPairs.card = L.card :=
    Finset.card_image_of_injective _ (tuplePair_injective N)
  have hlowPairs : lowPairs.card ≤ 2 * Nat.ceil U := by
    apply P4BLowerProductStripMass.prime_pairs_card_le_two_ceil lowPairs U
    · intro p hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      have htS := (Finset.mem_filter.mp ht).1
      have htPrime := (mem_physicalSupportedStrip.mp htS).1
      have hprime : ∀ i : Fin 2, Nat.Prime (t i).val :=
        (Finset.mem_filter.mp htPrime).2
      exact ⟨hprime 0, hprime 1⟩
    · intro p hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      exact (lt_of_not_ge (Finset.mem_filter.mp ht).2).le
  have hlow : L.card ≤ 2 * Nat.ceil U := by
    rw [← himage]
    exact hlowPairs
  have hsplit : H.card + L.card = S.card :=
    Finset.card_filter_add_card_filter_not S
      (fun t => U ≤ ((tuplePair t).1 * (tuplePair t).2 : ℕ))
  change S.card ≤ (orderStrip kappa width (2 * N)).card + 2 * Nat.ceil U
  omega

theorem orderStrip_mono {kappa small large : ℝ} {N : ℕ} (hle : small ≤ large) :
    orderStrip kappa small N ⊆ orderStrip kappa large N := by
  rintro ⟨r, q⟩ ht
  obtain ⟨hr, hq, hcut, hprod, hstrip⟩ := mem_orderStrip.mp ht
  exact mem_orderStrip.mpr ⟨hr, hq, hcut, hprod, hstrip.trans hle⟩

/-- Doubling the integer target costs at most a factor two in N/log N. -/
theorem massScale_two_mul_le_two_massScale {N : ℕ} (hN : 2 ≤ N) :
    ((2 * N : ℕ) : ℝ) / Real.log (2 * N : ℕ) ≤
      2 * ((N : ℝ) / Real.log (N : ℝ)) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hlogs : Real.log (N : ℝ) ≤ Real.log (2 * N : ℕ) :=
    Real.log_le_log (zero_lt_one.trans hN1)
      (Nat.cast_le.mpr (show N ≤ 2 * N by omega))
  calc
    ((2 * N : ℕ) : ℝ) / Real.log (2 * N : ℕ) ≤
        ((2 * N : ℕ) : ℝ) / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlogN hlogs
    _ = 2 * ((N : ℝ) / Real.log (N : ℝ)) := by
      push_cast
      ring

/-- A positive supported-order reserve below any prescribed width cap.
One width and one threshold work for all actual b and T. -/
theorem exists_supported_order_strip_mass_reserve {kappa eta widthMax : ℝ}
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (heta : 0 < eta) (hwidthMax : 0 < widthMax) :
    ∃ width : ℝ, 0 < width ∧ width ≤ widthMax ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ b T : ℝ,
        ((physicalSupportedStrip width b N T 0).card : ℝ) ≤
          eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨c, hc, hc1, hlogc, delta, hdeltaPos, hdelta, K, hK, horder⟩ :=
    exists_orderStrip_mass_reserve hkappa hkappa1 (show 0 < eta / 4 by linarith)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let width : ℝ := min widthMax (min delta (Real.log 2))
  have hwidth : 0 < width := lt_min hwidthMax (lt_min hdeltaPos hlog2)
  have hwidthMaxLe : width ≤ widthMax := min_le_left _ _
  have hwidthDelta : width ≤ delta :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hwidth2 : width ≤ Real.log 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hcut := eventually_manuscriptHalfProductCutoff_add_one_le_massScale
    hkappa (eta / 8) (show 0 < eta / 8 by linarith)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hcut
  let N0 : ℕ := max 2 (max K J)
  have hN0 : 2 ≤ N0 := le_max_left _ _
  refine ⟨width, hwidth, hwidthMaxLe, N0, hN0, ?_⟩
  intro N hNN0 b T
  have hN : 2 ≤ N := hN0.trans hNN0
  have hKN : K ≤ N := (le_trans (le_max_left K J) (le_max_right 2 (max K J))).trans hNN0
  have hJN : J ≤ N := (le_trans (le_max_right K J) (le_max_right 2 (max K J))).trans hNN0
  have hNM : N ≤ 2 * N := by omega
  have hhigh : ((orderStrip kappa width (2 * N)).card : ℝ) ≤
      (eta / 4) * (((2 * N : ℕ) : ℝ) / Real.log (2 * N : ℕ)) := by
    have hmono : (orderStrip kappa width (2 * N)).card ≤
        (orderStrip kappa delta (2 * N)).card :=
      Finset.card_le_card (orderStrip_mono hwidthDelta)
    exact (Nat.cast_le.mpr hmono).trans (horder (2 * N) (hKN.trans hNM))
  have hcutM := hJ (2 * N) (hJN.trans hNM)
  have hceil : (Nat.ceil (manuscriptHalfProductCutoff kappa (2 * N)) : ℝ) ≤
      manuscriptHalfProductCutoff kappa (2 * N) + 1 :=
    (Nat.ceil_lt_add_one (manuscriptHalfProductCutoff_nonneg kappa (2 * N))).le
  have hfinite : ((physicalSupportedStrip width b N T 0).card : ℝ) ≤
      ((orderStrip kappa width (2 * N)).card : ℝ) +
        2 * (Nat.ceil (manuscriptHalfProductCutoff kappa (2 * N)) : ℝ) := by
    exact_mod_cast supported_order_card_le_orderStrip_add_two_ceil
      (kappa := kappa) (b := b) (T := T) hN hwidth hwidth2
  have hscale := massScale_two_mul_le_two_massScale hN
  have hscaleEta := mul_le_mul_of_nonneg_left hscale (show 0 ≤ eta / 2 by linarith)
  nlinarith only [hfinite, hhigh, hceil, hcutM, hscaleEta]

end

end ImbalancedChen.P4BSupportedOrderStripMass
