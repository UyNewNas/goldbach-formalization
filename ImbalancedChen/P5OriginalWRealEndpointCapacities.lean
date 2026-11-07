import ImbalancedChen.P5OriginalNearCapRealEndpointGeometry

/-!
# Actual W certificate: real first-two and late-slot capacities
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The capacities are the ORIGINAL N-scale W capacities at the literal
near-cap nu/delta. The input seed is a REAL upper endpoint vector, with
paid padding certified by7ce1. No arithmetic prime tuple, integer factor,
Dwell support or desired completed allocation is supplied.
PrimeBox owns the computed real initial bins and subsequent word partition.
-/

namespace ImbalancedChen.P5Z.OriginalWRealEndpointCapacities
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenNearCapBoxProfiles
open OriginalNearCapRealEndpointGeometry

def middleCapacity (B : Box) (eta : ℚ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (2 * (nu wPolicy B eta : ℝ) - 1)

def rightCapacity (B : Box) (eta : ℚ) (N : ℕ) (A : ℝ) : ℝ :=
  (N : ℝ) ^ (1 - (nu wPolicy B eta : ℝ) - 2 * (delta wPolicy B eta : ℝ)) / A

def runCapacity (B : Box) (eta : ℚ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ ((nu wPolicy B eta : ℝ) - 2 * (delta wPolicy B eta : ℝ))

/-- Exact real-capacity prerequisites for the ORIGINAL W algorithm.
The A interval is the full original [1,N^(1/3)], not a delta-tightened
interval. Late upper slots retain the moving-alpha member of the min. -/
theorem actual_W_real_capacity_inputs {N : ℕ} (hN : 1 < N)
    (B : Box) (eta : ℚ) (hv : B.Valid) (hw : 0 < B.lo 3)
    (hc : wholeBoxEligibleTest wPolicy B = true) (heta : 0 < eta)
    (u : LogFour) (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta)
    (hu2 : 0 ≤ u 2) (hu10 : u 1 ≤ u 0)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    {kappa : ℝ} (hk0 : 0 ≤ kappa) (hk : kappa ≤ (delta wPolicy B eta : ℝ) / 64) :
    1 ≤ middleCapacity B eta N ∧ 1 ≤ rightCapacity B eta N A ∧
      A * middleCapacity B eta N * rightCapacity B eta N A = runCapacity B eta N ∧
      (N : ℝ) ^ u 0 ≤ middleCapacity B eta N ∧
      ((N : ℝ) ^ u 1) ^ 2 ≤ A * rightCapacity B eta N A ∧
      ∀ late : ℝ, late ≤ u 2 →
        middleCapacity B eta N * (N : ℝ) ^ late ≤
          (N : ℝ) ^ (actualSelectedSubproductUpper (1 + 3 * kappa)
            (nu wPolicy B eta : ℝ) - (delta wPolicy B eta : ℝ)) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hn
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hd : (0 : ℝ) < (delta wPolicy B eta : ℝ) := by
    exact_mod_cast (rational_parameters wPolicy B eta hv hw hc heta).2.2.1
  let hi : LogFour := fun i => (B.hi i : ℝ)
  have hhiB : hi ∈ B.region := ⟨fun i => by exact_mod_cast hv i, fun i => le_rfl⟩
  have hm := whole_box_nearcap_margins wPolicy B eta hv hw hc heta hi hhiB
  obtain ⟨hnu, hfirst, hsecond, hthird, hlate, hwall⟩ :=
    W_endpoint_initialization B eta hv hw hc heta u hlo hhi hu2 hu10 hk0 hk
  have hB : 1 ≤ middleCapacity B eta N :=
    Real.one_le_rpow hn.le (by linarith [hm.1])
  have hAP : A ≤ (N : ℝ) ^
      (1 - (nu wPolicy B eta : ℝ) - 2 * (delta wPolicy B eta : ℝ)) :=
    hAupper.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith [hm.2.1]))
  have hC : 1 ≤ rightCapacity B eta N A := by
    apply (le_div_iff₀ hAp).mpr
    simpa only [one_mul] using hAP
  have hAC : A * rightCapacity B eta N A =
      (N : ℝ) ^ (1 - (nu wPolicy B eta : ℝ) - 2 * (delta wPolicy B eta : ℝ)) := by
    dsimp [rightCapacity]
    field_simp [hAp.ne'] <;> ring
  refine ⟨hB, hC, ?_, ?_, ?_, ?_⟩
  · calc
      A * middleCapacity B eta N * rightCapacity B eta N A =
          middleCapacity B eta N * (A * rightCapacity B eta N A) := by ring
      _ = middleCapacity B eta N *
          (N : ℝ) ^ (1 - (nu wPolicy B eta : ℝ) - 2 * (delta wPolicy B eta : ℝ)) := by rw [hAC]
      _ = runCapacity B eta N := by
        dsimp [middleCapacity, runCapacity]
        rw [← Real.rpow_add hNp]
        congr 1
        ring
  · exact Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)
  · rw [hAC, ← Real.rpow_mul_natCast hNp.le]
    exact Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)
  · intro late hle
    dsimp [middleCapacity]
    rw [← Real.rpow_add hNp]
    exact Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)

end
end ImbalancedChen.P5Z.OriginalWRealEndpointCapacities
