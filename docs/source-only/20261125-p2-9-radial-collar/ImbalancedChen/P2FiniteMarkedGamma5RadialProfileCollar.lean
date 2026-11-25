import ImbalancedChen.P2FiniteMarkedGamma5RadialTupleCount
import ImbalancedChen.P2FiniteMarkedGamma5IntegerSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The outer physical-product collar of one existing Gamma5 profile. Width
is log(1+h), so nonzero support has complete product < (1+h)N < 2N.
The integer box is derived from positivity and the complete product; no
coordinate is discarded, identified with another slot, or assigned an
extra arithmetic filter. Empty old and rough blocks are retained.

The ordinary sum below uses exactly finPhysicalProfile, whose weights
already lie in [0,1]. It is a single fixed-split ambient sum, not the sum
of all history marks, a J identification, or a prime-product estimate.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5RadialProfileCollar
noncomputable section
open Filter Finset Real Wu2008DoubleSieve
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor)
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open P2FiniteMarkedGamma5PhysicalExtension
open P2FiniteMarkedGamma5EulerWordBudget
open P2FiniteMarkedGamma5IntegerSupport
open P2FiniteMarkedGamma5RadialRoughMass
open P2FiniteMarkedGamma5RadialTupleCount
open scoped Classical Topology BigOperators

def radialWidth (h : ℝ) : ℝ := log (1 + h)

theorem radialWidth_pos {h : ℝ} (hp : 0 < h) : 0 < radialWidth h :=
  log_pos (by linarith only [hp])

theorem radialWidth_le_one {h : ℝ} (hp : 0 < h) (h8 : h ≤ 1 / 8) :
    radialWidth h ≤ 1 := by
  have hh := log_le_sub_one_of_pos (show 0 < 1 + h by linarith only [hp])
  dsimp only [radialWidth]
  linarith only [hh, h8]

theorem exp_radialWidth {h : ℝ} (hp : 0 < h) :
    exp (radialWidth h) = 1 + h :=
  exp_log (by linarith only [hp])

theorem exp_radialWidth_lt_two {h : ℝ} (hp : 0 < h) (h8 : h ≤ 1 / 8) :
    exp (radialWidth h) < 2 := by
  rw [exp_radialWidth hp]
  linarith only [h8]

/-- Every natural nonzero-support coordinate lies in the same finite
box. This uses the complete positive product, not distinctness of primes. -/
theorem profile_integer_box {N k r : ℕ} {logQ h : ℝ}
    {u : Fin (k + (2 + r)) → ℕ} (hN : 0 < N)
    (hp : 0 < h) (h8 : h ≤ 1 / 8)
    (hne : finPhysicalProfile logQ (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => (u i : ℝ)) ≠ 0) :
    ∀ i, u i ≤ 2 * N := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hfloor := rpow_pos_of_pos hN0 frozenLeafCutoffFloor
  have hu := finPhysicalProfile_integer_pos hfloor hne
  have hprod : 0 < ∏ i, u i := Finset.prod_pos (fun i _ => hu i)
  have hcap := finPhysicalProfile_integer_product_lt hfloor hN0 (radialWidth_pos hp) hne
  have hlt : (∏ i, u i : ℕ) < 2 * N := by
    exact_mod_cast hcap.trans
      (mul_lt_mul_of_pos_right (exp_radialWidth_lt_two hp h8) hN0)
  intro i
  exact (Nat.le_of_dvd hprod (Finset.dvd_prod_of_mem u (mem_univ i))).trans hlt.le

def profileOuterTuples (N k r : ℕ) (logQ h : ℝ) :
    Finset (Fin (k + (2 + r)) → Fin (2 * N + 1)) :=
  (Part3.labelledPrimeTuples (k + (2 + r)) (2 * N)).filter (fun t =>
    finPhysicalProfile logQ (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((t i).val : ℝ)) ≠ 0 ∧
      (N : ℝ) < (Part3.labelledProduct t : ℝ))

def profileOuterMass (N k r : ℕ) (logQ h : ℝ) : ℝ :=
  ∑ t ∈ profileOuterTuples N k r logQ h,
    finPhysicalProfile logQ (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((t i).val : ℝ))

/-- The Fin box enumerates every prime natural tuple on the nonzero
outer support, preserving its exact coordinates and order. -/
theorem profile_outer_integer_enumeration {N k r : ℕ} {logQ h : ℝ}
    {u : Fin (k + (2 + r)) → ℕ} (hN : 0 < N)
    (hp : 0 < h) (h8 : h ≤ 1 / 8) (hprime : ∀ i, (u i).Prime)
    (hne : finPhysicalProfile logQ (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => (u i : ℝ)) ≠ 0)
    (houter : (N : ℝ) < ((∏ i, u i : ℕ) : ℝ)) :
    ∃ t ∈ profileOuterTuples N k r logQ h, ∀ i, (t i).val = u i := by
  have hbox := profile_integer_box hN hp h8 hne
  let t : Fin (k + (2 + r)) → Fin (2 * N + 1) :=
    fun i => ⟨u i, Nat.lt_succ_of_le (hbox i)⟩
  refine ⟨t, ?_, fun i => rfl⟩
  refine mem_filter.mpr ⟨?_, hne, houter⟩
  exact mem_filter.mpr ⟨mem_univ _, hprime⟩

theorem profile_outer_subset {N k r : ℕ} {logQ h : ℝ}
    (hN : 0 < N) (hp : 0 < h)
    (hcut : cut N ≤ (N : ℝ) ^ frozenLeafCutoffFloor / 2) :
    profileOuterTuples N k r logQ h ⊆
      bandTuples N (k + (2 + r)) (1 - 2 * h) (1 + 2 * h) := by
  intro t ht
  obtain ⟨hprime, hne, houter⟩ := mem_filter.mp ht
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  obtain ⟨hfloor, hcap⟩ := finPhysicalProfile_nonzero_support
    (rpow_pos_of_pos hN0 frozenLeafCutoffFloor) hN0 (radialWidth_pos hp) hne
  have hcap' : (Part3.labelledProduct t : ℝ) < (1 + h) * (N : ℝ) := by
    simpa only [Part3.labelledProduct, Nat.cast_prod, exp_radialWidth hp] using hcap
  refine mem_filter.mpr ⟨hprime, (fun i => hcut.trans (hfloor i).le), ?_, ?_⟩
  · have hh : (1 - 2 * h) * (N : ℝ) ≤ (N : ℝ) := by
      nlinarith only [hp, hN0]
    exact hh.trans_lt houter
  · exact hcap'.le.trans
      (mul_le_mul_of_nonneg_right (by linarith only [hp]) hN0.le)

theorem profileOuterMass_le_card (N k r : ℕ) (logQ h : ℝ) :
    profileOuterMass N k r logQ h ≤ ((profileOuterTuples N k r logQ h).card : ℝ) := by
  calc
    _ ≤ ∑ _t ∈ profileOuterTuples N k r logQ h, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      exact (physicalProfile_bounds logQ (N : ℝ) (radialWidth h)
        ((N : ℝ) ^ frozenLeafCutoffFloor)
        (finToPhysical k r (fun i => ((t i).val : ℝ)))).2
    _ = _ := by simp

/-- The fixed h and physical width are chosen before every scale,
logQ and old/rough split. This pays only the radial exterior of one
ambient profile with the original frozen rank ceiling. -/
theorem absolute_profile_outer_payment {ε : ℝ} (he : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧
      0 < radialWidth h ∧ radialWidth h ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (k r : ℕ) (logQ : ℝ),
        k + 2 + r ≤ frozenSourceRankBound →
        P2FiniteMarkedGamma5RadialRoughMass.norm N *
          profileOuterMass N k r logQ h ≤ ε := by
  obtain ⟨h, hp, h8, H⟩ := absolute_radial_payment he
  refine ⟨h, hp, h8, radialWidth_pos hp, radialWidth_le_one hp h8, ?_⟩
  filter_upwards [H, eventually_cut_le_half_floor, eventually_gt_atTop (1 : ℕ)]
    with N hpaid hcut hlarge
  intro k r logQ hkr
  have hN : 0 < N := by omega
  have hcard : ((profileOuterTuples N k r logQ h).card : ℝ) ≤
      boundaryCount N (1 - 2 * h) (1 + 2 * h) := by
    apply (Nat.cast_le.mpr (Finset.card_le_card (profile_outer_subset hN hp hcut))).trans
    exact rank_card_le_boundaryCount N (k + (2 + r)) _ _ (by omega)
  have hnorm : 0 ≤ P2FiniteMarkedGamma5RadialRoughMass.norm N :=
    div_nonneg (log_nonneg (by exact_mod_cast hlarge.le)) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left
    ((profileOuterMass_le_card N k r logQ h).trans hcard) hnorm).trans hpaid

end
end ImbalancedChen.P2FiniteMarkedGamma5RadialProfileCollar
