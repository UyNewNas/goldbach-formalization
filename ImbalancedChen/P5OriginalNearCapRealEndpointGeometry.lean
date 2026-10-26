import ImbalancedChen.P5ZU1011OriginalSixteenNearCapBoxProfiles
import ImbalancedChen.P5ZU1011OriginalFifteenJointKappaMonomials

/-!
# Literal all16 near-cap certificates license padded REAL upper endpoints
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The four prefix endpoints remain separate from the rough residual word.
Only actual rational certificates and paid geometric padding are inputs.
The ORIGINAL physical residual nu-Tplus-20delta and run level nu-2delta
are unchanged. Full/selected squares and residual attachment are derived
at real upper endpoints, with strict reserves; no integer factorization,
Dwell support, Medium gate, or arithmetic representative is assumed.
The W padding also pays its genuine strict25/128 wall, whose distance
is not controlled by delta alone.
-/

namespace ImbalancedChen.P5Z.OriginalNearCapRealEndpointGeometry
noncomputable section
open Classical Set
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenNearCapBoxProfiles

def endpointPadding (p : Policy) (B : Box) (eta : ℚ) : ℝ :=
  min ((delta p B eta : ℝ) / 32)
    (if p.val < 15 then (delta p B eta : ℝ) / 32 else
      ((25 / 128 : ℝ) - (B.hi 0 : ℝ)) / 2)

theorem endpointPadding_positive (p : Policy) (B : Box) (eta : ℚ)
    (hv : B.Valid) (hw : 0 < B.lo 3) (hc : wholeBoxEligibleTest p B = true)
    (heta : 0 < eta) :
    0 < endpointPadding p B eta ∧ endpointPadding p B eta ≤ (delta p B eta : ℝ) / 32 := by
  have hd : (0 : ℝ) < (delta p B eta : ℝ) := by
    exact_mod_cast (rational_parameters p B eta hv hw hc heta).2.2.1
  refine ⟨?_, min_le_left _ _⟩
  unfold endpointPadding
  apply lt_min (by positivity)
  by_cases hp : p.val < 15
  · simp only [if_pos hp]
    positivity
  · simp only [if_neg hp]
    have ht : WholeBoxEligible p B := of_decide_eq_true hc
    have hwallQ : B.hi 0 < (25 / 128 : ℚ) := by
      have h : wExtraPiece.upper B.lo B.hi < capLower p B ∧ B.hi 0 < (25 / 128 : ℚ) := by
        simpa only [if_neg hp] using ht.2.2
      exact h.2
    have hwall : (B.hi 0 : ℝ) < 25 / 128 := by exact_mod_cast hwallQ
    linarith

private theorem masked_upper (P : Fin 4 → Prop) [DecidablePred P]
    (u v : LogFour) {h : ℝ} (hh : 0 ≤ h) (hu : ∀ i, u i ≤ v i + h) :
    (∑ i : Fin 4, if P i then u i else 0) ≤
      (∑ i : Fin 4, if P i then v i else 0) + 4 * h := by
  have hs : (∑ i : Fin 4, if P i then u i else 0) ≤
      ∑ i : Fin 4, ((if P i then v i else 0) + h) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hp : P i <;> simp only [hp, if_true, if_false] <;> linarith [hu i]
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hs

private theorem masked_lower (P : Fin 4 → Prop) [DecidablePred P]
    (u v : LogFour) (hu : ∀ i, v i ≤ u i) :
    (∑ i : Fin 4, if P i then v i else 0) ≤
      (∑ i : Fin 4, if P i then u i else 0) := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hp : P i <;> simp only [hp, if_true, if_false] <;> linarith [hu i]

private theorem full_upper (u v : LogFour) {h : ℝ} (hh : 0 ≤ h)
    (hu : ∀ i, u i ≤ v i + h) (j : Fin 4) : fullSquare j u ≤ fullSquare j v + 6 * h := by
  have hs := masked_upper (fun i => i.val < j.val) u v hh hu
  unfold fullSquare
  linarith [hu j]

private theorem selected_upper (p : Policy) (u v : LogFour) {h : ℝ}
    (hh : 0 ≤ h) (hu : ∀ i, u i ≤ v i + h) (j : Fin 4) :
    selectedSquare p j u ≤ selectedSquare p j v + 10 * h := by
  have hs := masked_upper (Selected p) u v hh hu
  have hr := masked_upper (fun i => i.val < j.val ∧ ¬ Selected p i) u v hh hu
  unfold selectedSquare selectedMass
  linarith [hu j]

/-- All actual fixed-cell circuits retain strict reserves at real padded
upper endpoints. Rough cover inflation is separately paid from20delta;
the original physical residual is kept literally in the conclusion. -/
theorem actual_padded_endpoint_reserves (p : Policy) (B : Box) (eta : ℚ)
    (hv : B.Valid) (hw : 0 < B.lo 3) (hc : wholeBoxEligibleTest p B = true)
    (heta : 0 < eta) (u : LogFour)
    (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding p B eta)
    {roughWidth : ℝ} (hrw : roughWidth ≤ (delta p B eta : ℝ)) :
    (nu p B eta : ℝ) + 60 * (delta p B eta : ℝ) < cap p u ∧
      (∀ j : Fin 4, fullSquare j u + 60 * (delta p B eta : ℝ) < (nu p B eta : ℝ)) ∧
      ((∑ i : Fin 4, u i) + (physicalResidual p B eta : ℝ) + roughWidth +
        16 * (delta p B eta : ℝ) < (nu p B eta : ℝ)) ∧
      (if p.val < 15 then ∀ j : Fin 4, ¬ Selected p j →
        selectedSquare p j u + 60 * (delta p B eta : ℝ) < (nu p B eta : ℝ)
      else (1 + u 0) / 2 + 60 * (delta p B eta : ℝ) < (nu p B eta : ℝ) ∧
        u 0 < (25 / 128 : ℝ)) := by
  let hi : LogFour := fun i => (B.hi i : ℝ)
  let lo : LogFour := fun i => (B.lo i : ℝ)
  have hhiB : hi ∈ B.region := ⟨fun i => by exact_mod_cast hv i, fun i => le_rfl⟩
  have hloB : lo ∈ B.region := ⟨fun i => le_rfl, fun i => by exact_mod_cast hv i⟩
  have mh := whole_box_nearcap_margins p B eta hv hw hc heta hi hhiB
  have ml := whole_box_nearcap_margins p B eta hv hw hc heta lo hloB
  have hd : (0 : ℝ) < (delta p B eta : ℝ) := by
    exact_mod_cast (rational_parameters p B eta hv hw hc heta).2.2.1
  obtain ⟨hpad, hpadBound⟩ := endpointPadding_positive p B eta hv hw hc heta
  have hmassHi : selectedMass p u ≤ selectedMass p hi + 4 * endpointPadding p B eta :=
    masked_upper (Selected p) u hi hpad.le hhi
  have hmassLo : selectedMass p lo ≤ selectedMass p u := masked_lower (Selected p) u lo hlo
  have hcap : (nu p B eta : ℝ) + 60 * (delta p B eta : ℝ) < cap p u := by
    by_cases hp : p.val < 15
    · have hl := ml.2.2.1
      have hh := mh.2.2.1
      simp only [cap, if_pos hp] at hl hh ⊢
      have hla := hl.trans (min_le_left _ _)
      have hhc := hh.trans (min_le_right _ _)
      apply lt_min <;> linarith
    · have hh := mh.2.2.1
      simp only [cap, if_neg hp] at hh ⊢
      have hcoord := hhi 2
      change u 2 ≤ hi 2 + endpointPadding p B eta at hcoord
      linarith
  have hfull : ∀ j : Fin 4, fullSquare j u + 60 * (delta p B eta : ℝ) < (nu p B eta : ℝ) := by
    intro j
    have hs := full_upper u hi hpad.le hhi j
    linarith [mh.2.2.2.1 j]
  have hsum : (∑ i : Fin 4, u i) ≤ (Tplus B : ℝ) + 4 * endpointPadding p B eta := by
    have hs := masked_upper (fun _ : Fin 4 => True) u hi hpad.le hhi
    have ht : (Tplus B : ℝ) = ∑ i : Fin 4, hi i := by
      rw [Tplus_eq_sum, Rat.cast_sum]
      rfl
    simpa only [if_true, ← ht] using hs
  have hR : (physicalResidual p B eta : ℝ) =
      (nu p B eta : ℝ) - (Tplus B : ℝ) - 20 * (delta p B eta : ℝ) := by
    simp [physicalResidual]
  refine ⟨hcap, hfull, by rw [hR]; linarith, ?_⟩
  by_cases hp : p.val < 15
  · simp only [if_pos hp] at mh ⊢
    intro j hj
    have hs := selected_upper p u hi hpad.le hhi j
    linarith [mh.2.2.2.2 j hj]
  · simp only [if_neg hp] at mh ⊢
    constructor
    · have hu := hhi 0
      change u 0 ≤ hi 0 + endpointPadding p B eta at hu
      linarith [mh.2.2.2.2.1]
    · have hwall := mh.2.2.2.2.2
      have hwallQ : (B.hi 0 : ℝ) < 25 / 128 := hwall
      have hpadWall : endpointPadding p B eta ≤ ((25 / 128 : ℝ) - (B.hi 0 : ℝ)) / 2 := by
        simpa only [endpointPadding, if_neg hp] using
          (min_le_right ((delta p B eta : ℝ) / 32)
            (((25 / 128 : ℝ) - (B.hi 0 : ℝ)) / 2))
      linarith [hhi 0]

/-- Real selected-middle bounds are paid by the ORIGINAL cap certificate,
including the alpha-dependent spectral member of the min after padding. -/
theorem ordinary_selected_endpoint_critical (p : Policy) (hp : p.val < 15)
    (B : Box) (eta : ℚ) (hv : B.Valid) (hw : 0 < B.lo 3)
    (hc : wholeBoxEligibleTest p B = true) (heta : 0 < eta) (u : LogFour)
    (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding p B eta)
    {kappa : ℝ} (hk0 : 0 ≤ kappa) (hk : kappa ≤ (delta p B eta : ℝ) / 64) :
    (nu p B eta : ℝ) ≤ 153 / 256 ∧
      2 * (nu p B eta : ℝ) - 1 + 100 * (delta p B eta : ℝ) ≤ selectedMass p u ∧
      selectedMass p u + 16 * (delta p B eta : ℝ) ≤
        actualSelectedSubproductUpper (1 + 3 * kappa) (nu p B eta : ℝ) := by
  have hd : (0 : ℝ) < (delta p B eta : ℝ) := by
    exact_mod_cast (rational_parameters p B eta hv hw hc heta).2.2.1
  have hbase := (actual_padded_endpoint_reserves p B eta hv hw hc heta u hlo hhi hd.le).1
  have hmax : cap p u ≤ (153 / 256 : ℝ) := by
    unfold cap
    rw [if_pos hp]
    by_cases hs : selectedMass p u ≤ (25 / 128 : ℝ)
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have hn : (nu p B eta : ℝ) ≤ 153 / 256 := by linarith
  simp only [cap, if_pos hp] at hbase
  have hleft := hbase.trans_le (min_le_left _ _)
  have hright := hbase.trans_le (min_le_right _ _)
  refine ⟨hn, by linarith, ?_⟩
  unfold actualSelectedSubproductUpper
  apply le_min <;> linarith

/-- W has its own first-two-slot initialization and late-slot min. These
are REAL upper endpoint statements. Nonnegative third endpoint and upper
label order are primitive geometry; no actual prime tuple is supplied. -/
theorem W_endpoint_initialization (B : Box) (eta : ℚ)
    (hv : B.Valid) (hw : 0 < B.lo 3) (hc : wholeBoxEligibleTest wPolicy B = true)
    (heta : 0 < eta) (u : LogFour)
    (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta)
    (hu2 : 0 ≤ u 2) (hu10 : u 1 ≤ u 0)
    {kappa : ℝ} (hk0 : 0 ≤ kappa) (hk : kappa ≤ (delta wPolicy B eta : ℝ) / 64) :
    (nu wPolicy B eta : ℝ) ≤ 153 / 256 ∧
      u 0 ≤ 2 * (nu wPolicy B eta : ℝ) - 1 - (delta wPolicy B eta : ℝ) ∧
      2 * u 1 ≤ 1 - (nu wPolicy B eta : ℝ) - 2 * (delta wPolicy B eta : ℝ) ∧
      u 2 < (51 / 32 : ℝ) - (8 / 3 : ℝ) * (nu wPolicy B eta : ℝ) ∧
      u 2 + (2 * (nu wPolicy B eta : ℝ) - 1) + (delta wPolicy B eta : ℝ) ≤
        actualSelectedSubproductUpper (1 + 3 * kappa) (nu wPolicy B eta : ℝ) ∧
      u 0 < (25 / 128 : ℝ) := by
  have hd : (0 : ℝ) < (delta wPolicy B eta : ℝ) := by
    exact_mod_cast (rational_parameters wPolicy B eta hv hw hc heta).2.2.1
  have hbase := actual_padded_endpoint_reserves wPolicy B eta hv hw hc heta u hlo hhi hd.le
  have hcap := hbase.1
  have hext := hbase.2.2.2
  have hp : ¬ wPolicy.val < 15 := by dsimp [wPolicy]; omega
  simp only [cap, if_neg hp] at hcap
  simp only [if_neg hp] at hext
  have hn : (nu wPolicy B eta : ℝ) ≤ 153 / 256 := by linarith
  refine ⟨hn, by linarith [hext.1], by linarith [hext.1], by linarith, ?_, hext.2⟩
  unfold actualSelectedSubproductUpper
  apply le_min <;> linarith

end
end ImbalancedChen.P5Z.OriginalNearCapRealEndpointGeometry
