import ImbalancedChen.P4BNormalizedImbalanceStripMass
import ImbalancedChen.RealHalfProductMassSuppliers
import Mathlib.Tactic.Linarith

/-!
# Actual prime-pair ordering-wall reserve (P4B, source-only)

YELLOW / UNCOMPILED. The sibling P4B import is its intended staged module
name. The strip has both labelled orders and includes its width endpoints.
The product cutoff is literal. The factor two below is solely the passage
from both prime-pair orders to one ordered source; it is not a factor in
RealB or in the manuscript normalization. Squares remain present once in
the strip and belong only to the r<=q part of the disjoint order split.
-/

namespace ImbalancedChen.P4BOrderBoundaryMass

noncomputable section

open Filter Topology

def normalizedLog (N p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log (N : ℝ)

/-- Ordinary prime pairs with independent labelled slots, without an
ordering condition. Both normalized width endpoints are included. -/
def orderStrip (kappa delta : ℝ) (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter fun a =>
    Nat.Prime a.1 ∧ Nat.Prime a.2 ∧
      manuscriptHalfProductCutoff kappa N ≤ (a.1 * a.2 : ℕ) ∧ a.1 * a.2 ≤ N ∧
      |normalizedLog N a.1 - normalizedLog N a.2| ≤ delta

@[simp] theorem mem_orderStrip {kappa delta : ℝ} {N r q : ℕ} :
    (r, q) ∈ orderStrip kappa delta N ↔
      Nat.Prime r ∧ Nat.Prime q ∧
        manuscriptHalfProductCutoff kappa N ≤ (r * q : ℕ) ∧ r * q ≤ N ∧
        |normalizedLog N r - normalizedLog N q| ≤ delta := by
  classical
  unfold orderStrip
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · rintro ⟨hr, hq, hcut, hprod, hstrip⟩
    have hrN : r ≤ N := by
      calc
        r = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * q := Nat.mul_le_mul_left r hq.one_le
        _ ≤ N := hprod
    have hqN : q ≤ N := by
      calc
        q = 1 * q := (Nat.one_mul q).symm
        _ ≤ r * q := Nat.mul_le_mul_right q hr.one_le
        _ ≤ N := hprod
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hrN),
        Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hqN)⟩,
      hr, hq, hcut, hprod, hstrip⟩

theorem swap_mem_orderStrip {kappa delta : ℝ} {N r q : ℕ}
    (hm : (r, q) ∈ orderStrip kappa delta N) :
    (q, r) ∈ orderStrip kappa delta N := by
  obtain ⟨hr, hq, hcut, hprod, hstrip⟩ := mem_orderStrip.mp hm
  apply mem_orderStrip.mpr
  refine ⟨hq, hr, ?_, ?_, ?_⟩
  · simpa only [Nat.mul_comm q r] using hcut
  · simpa only [Nat.mul_comm q r] using hprod
  · simpa only [abs_sub_comm] using hstrip

/-- With s=(1-kappa)/2, the larger factor has normalized logarithm at
least s. Choosing delta<s*(1-c) puts the closed strip strictly inside
the c-power source, including the order diagonal and width endpoints. -/
theorem ordered_strip_mem_pairs {c kappa delta : ℝ} {N r q : ℕ}
    (hc1 : c < 1) (hN : 2 ≤ N)
    (hdelta : delta < ((1 - kappa) / 2) * (1 - c))
    (hm : (r, q) ∈ orderStrip kappa delta N) (hrq : r ≤ q) :
    (r, q) ∈ realHalfProductPairs c N (manuscriptHalfProductCutoff kappa N) := by
  obtain ⟨hr, hq, hcut, hprod, hstrip⟩ := mem_orderStrip.mp hm
  have hy : (1 - kappa) / 2 ≤ normalizedLog N q :=
    P4BNormalizedImbalanceStripMass.logq_div_logN_lower hN hr hq hrq hcut
  have hwidth : delta < (1 - c) * normalizedLog N q := by
    have hmul := mul_le_mul_of_nonneg_right hy (sub_pos.mpr hc1).le
    exact hdelta.trans_le (by simpa only [mul_comm] using hmul)
  have hleft := (abs_le.mp hstrip).1
  have hpowerLog : c * normalizedLog N q < normalizedLog N r := by
    nlinarith only [hleft, hwidth]
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hpower : (q : ℝ) ^ c < (r : ℝ) :=
    (P4BLabelledLogGeometry.power_iff_normalized_logs c hN1 hrR hqR).mpr hpowerLog
  exact mem_realHalfProductPairs.mpr ⟨hr, hq, hrq, hpower, hcut, hprod⟩

/-- A disjoint split r<=q versus q<r, with swapping only on the latter.
Squares occur in the first piece only. Each piece injects into the same
ordered source, so no factorization-witness multiplicity is introduced. -/
theorem orderStrip_card_le_twice_source {c kappa delta : ℝ} {N : ℕ}
    (hc1 : c < 1) (hN : 2 ≤ N)
    (hdelta : delta < ((1 - kappa) / 2) * (1 - c)) :
    (orderStrip kappa delta N).card ≤
      2 * (realHalfProductSource c N (manuscriptHalfProductCutoff kappa N)).card := by
  classical
  let A := orderStrip kappa delta N
  let P := realHalfProductPairs c N (manuscriptHalfProductCutoff kappa N)
  have hordered : (A.filter (fun a => a.1 ≤ a.2)).card ≤ P.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨haA, haOrder⟩ := Finset.mem_filter.mp ha
    exact ordered_strip_mem_pairs hc1 hN hdelta haA haOrder
  have hreversed : (A.filter (fun a => ¬a.1 ≤ a.2)).card ≤ P.card := by
    apply Finset.card_le_card_of_injOn (fun a : ℕ × ℕ => (a.2, a.1))
    · rintro ⟨r, q⟩ ha
      obtain ⟨haA, haOrder⟩ := Finset.mem_filter.mp ha
      exact ordered_strip_mem_pairs hc1 hN hdelta
        (swap_mem_orderStrip haA) (le_of_lt (lt_of_not_ge haOrder))
    · intro a ha t ht heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  calc
    A.card = (A.filter (fun a => a.1 ≤ a.2)).card +
        (A.filter (fun a => ¬a.1 ≤ a.2)).card :=
      (Finset.card_filter_add_card_filter_not (s := A)
        (fun a => a.1 ≤ a.2)).symm
    _ ≤ P.card + P.card := Nat.add_le_add hordered hreversed
    _ = 2 * (realHalfProductSource c N
        (manuscriptHalfProductCutoff kappa N)).card := by
      dsimp only [P]
      simp only [realHalfProductPairs_card_eq]
      omega

/-- Squares are present in exactly one half of the order split. -/
theorem square_mem_ordered_half_iff {kappa delta : ℝ} {N p : ℕ} :
    (p, p) ∈ (orderStrip kappa delta N).filter (fun a => a.1 ≤ a.2) ↔
      (p, p) ∈ orderStrip kappa delta N := by
  classical
  simp only [Finset.mem_filter, le_refl, and_true]

theorem square_not_mem_reversed_half (kappa delta : ℝ) (N p : ℕ) :
    (p, p) ∉ (orderStrip kappa delta N).filter (fun a => ¬a.1 ≤ a.2) := by
  classical
  simp only [Finset.mem_filter, le_refl, not_true_eq_false, and_false, not_false_eq_true]

/-- Choose the exponent close to one using continuity of the actual
coefficient log(1/c), then apply the proved source mass limit. No strip
mass limit or independent collar estimate is assumed. The width and
exponent are fixed before the single integer threshold. -/
theorem exists_orderStrip_mass_reserve {kappa eta : ℝ}
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (heta : 0 < eta) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ Real.log (1 / c) < eta / 4 ∧
      ∃ delta : ℝ, 0 < delta ∧
        delta < ((1 - kappa) / 2) * (1 - c) ∧
        ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
          ((orderStrip kappa delta N).card : ℝ) ≤
            eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨c, hcHalf, hc1, hgap⟩ :=
    P4BImbalanceBoundaryMass.exists_lower_parameter_log_gap
      (b := 1) (by norm_num) (show 0 < eta / 4 by linarith)
  have hc : 0 < c := by linarith
  have hlogc : Real.log (1 / c) < eta / 4 := by
    simpa only [div_one, Real.log_one, sub_zero] using hgap
  let B : ℝ := ((1 - kappa) / 2) * (1 - c)
  have hB : 0 < B := mul_pos (by linarith) (sub_pos.mpr hc1)
  let delta : ℝ := B / 2
  have hdeltaPos : 0 < delta := half_pos hB
  have hdelta : delta < ((1 - kappa) / 2) * (1 - c) := by
    change B / 2 < B
    linarith
  have hsourceLimit :=
    tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers hc hc1 hkappa
  have hmass : ∀ᶠ N : ℕ in atTop,
      ((realHalfProductSource c N (manuscriptHalfProductCutoff kappa N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) < eta / 2 :=
    hsourceLimit.eventually (gt_mem_nhds (by linarith : Real.log (1 / c) < eta / 2))
  have hbound : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧
      ((orderStrip kappa delta N).card : ℝ) ≤
        eta * ((N : ℝ) / Real.log (N : ℝ)) := by
    filter_upwards [hmass, eventually_ge_atTop (2 : ℕ)] with N hmassN hN
    have hN1 : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
      div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
    have hsource :
        ((realHalfProductSource c N (manuscriptHalfProductCutoff kappa N)).card : ℝ) <
          (eta / 2) * ((N : ℝ) / Real.log (N : ℝ)) :=
      (div_lt_iff₀ hscale).mp hmassN
    have hfinite : ((orderStrip kappa delta N).card : ℝ) ≤
        2 * ((realHalfProductSource c N
          (manuscriptHalfProductCutoff kappa N)).card : ℝ) := by
      exact_mod_cast orderStrip_card_le_twice_source hc1 hN hdelta
    refine ⟨hN, ?_⟩
    nlinarith only [hfinite, hsource]
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨c, hc, hc1, hlogc, delta, hdeltaPos, hdelta, N0,
    (hN0 N0 le_rfl).1, ?_⟩
  intro N hNN0
  exact (hN0 N hNN0).2

end

end ImbalancedChen.P4BOrderBoundaryMass
