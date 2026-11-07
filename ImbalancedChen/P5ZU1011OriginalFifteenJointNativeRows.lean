import ImbalancedChen.P5ZU1011OriginalSixteenStaticNativeCompiler

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual ordinary15 fixed native rows on the ORIGINAL JOINT U10/U11 source.
The low fourth-prime band is unmasked and the high band retains E. This
does not place D10 inside D11. Actual Z is lowered below p1 before the
coprime reciprocal-totient main is used; the original p2 cutoff is never
declared coprime. W joint native rows are separately owned. No H248/native
density, AP, PP, count or analytic mean license is assumed.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenJointNativeRows
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalFifteenNativeGridCells P5U1011JointOverlap

theorem joint_coordinates_cube {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) : coordinates N t∈cube := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hb := joint_band_and_mask ht
  have ha := (slots_strictAnti ht).antitone
  apply mem_logPrimeBox.mpr
  intro i
  have hsmall : (t.1.1:ℝ)≤(slots t i:ℝ) := by
    have h := ha (show i≤(3:Fin 4) by omega)
    have hr : (slots t 3:ℝ)≤(slots t i:ℝ) := by exact_mod_cast h
    simpa only [slots,Matrix.cons_val_three] using hr
  have hlarge : (slots t i:ℝ)≤(t.2.2:ℝ) := by
    have h := ha (show (0:Fin 4)≤i by omega)
    have hr : (slots t i:ℝ)≤(slots t 0:ℝ) := by exact_mod_cast h
    simpa only [slots,Matrix.cons_val_zero] using hr
  have hlo : (N:ℝ)^(lower:ℝ)≤(slots t i:ℝ) := by simpa [lower] using hb.1.trans hsmall
  have hhi : (slots t i:ℝ)<(N:ℝ)^(upper:ℝ) := by simpa [upper] using hlarge.trans_lt hb.2.2.1
  rw [←slot_rpow hN ht i] at hlo hhi
  exact ⟨(Real.rpow_le_rpow_left_iff hn).mp hlo,(Real.rpow_lt_rpow_left_iff hn).mp hhi⟩

theorem joint_count_identity {N : ℕ} (hN : 1<N) (E : ℕ×ℕ→Prop) :
    currentChenUpsilon10 N+currentChenUpsilon11 N E=∑t∈jointSelector N E,U11Adaptive.weight N t :=
  currentChenUpsilon10_add_11_eq_joint_source N E (by exact_mod_cast (Nat.le_of_lt hN))

/-- Genuine joint arithmetic legality for the existing fixed native
parameters; no high-band source premise is needed. -/
theorem joint_native_legality {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (hp : p.val<15) (B : Box)
    (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) :
    0<U1011OriginalFifteenFixedCellNative.Z p B N ∧
      1<U1011OriginalFifteenFixedCellNative.D p B N ∧
      U1011OriginalFifteenFixedCellNative.Z p B N≤(t.1.1:ℝ) ∧
      U1011OriginalFifteenFixedCellNative.Z p B N≤U1011OriginalFifteenFixedCellNative.D p B N := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := zero_lt_one.trans hn
  have h := U1011OriginalFifteenFixedCellNative.rational_parameters p hp B hv hw hc
  have hr : (0:ℝ)<(U1011OriginalFifteenFixedCellNative.residualExponent p B:ℝ) := by exact_mod_cast h.2.2.2.2.2.1
  have hρ : (0:ℝ)<(U1011OriginalFifteenFixedCellNative.rho p B:ℝ) := by exact_mod_cast h.2.2.2.2.1
  have hcQ : U1011OriginalFifteenFixedCellNative.cutoffExponent p B≤
      U1011OriginalFifteenFixedCellNative.residualExponent p B/(2+U1011OriginalFifteenFixedCellNative.rho p B) := min_le_right _ _
  have hcR : (U1011OriginalFifteenFixedCellNative.cutoffExponent p B:ℝ)≤
      (U1011OriginalFifteenFixedCellNative.residualExponent p B:ℝ)/(2+(U1011OriginalFifteenFixedCellNative.rho p B:ℝ)) := by exact_mod_cast hcQ
  have hquot : (U1011OriginalFifteenFixedCellNative.residualExponent p B:ℝ)/(2+(U1011OriginalFifteenFixedCellNative.rho p B:ℝ))≤
      (U1011OriginalFifteenFixedCellNative.residualExponent p B:ℝ) := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
  have hfirst : U1011OriginalFifteenFixedCellNative.Z p B N≤(t.1.1:ℝ) := by
    have hx : (0:ℝ)≤(U1011OriginalFifteenFixedCellNative.xi p B:ℝ) := by exact_mod_cast h.2.2.2.1.le
    have hmQ : U1011OriginalFifteenFixedCellNative.cutoffExponent p B≤B.lo 3-U1011OriginalFifteenFixedCellNative.xi p B := min_le_left _ _
    have hmR : (U1011OriginalFifteenFixedCellNative.cutoffExponent p B:ℝ)≤(B.lo 3:ℝ)-(U1011OriginalFifteenFixedCellNative.xi p B:ℝ) := by exact_mod_cast hmQ
    have hle : (U1011OriginalFifteenFixedCellNative.cutoffExponent p B:ℝ)≤coordinates N t 3 := by linarith [hb.1 3]
    have hpow := Real.rpow_le_rpow_of_exponent_le hn.le hle
    simpa only [U1011OriginalFifteenFixedCellNative.Z,slots,Matrix.cons_val_three] using hpow.trans_eq (slot_rpow hN ht 3)
  exact ⟨Real.rpow_pos_of_pos hn0 _,Real.one_lt_rpow hn hr,hfirst,Real.rpow_le_rpow_of_exponent_le hn.le (hcR.trans hquot)⟩

theorem joint_estimator_identity {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (hp : p.val<15) (B : Box)
    (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) :
    U1011OriginalFifteenFixedCellNative.estimator p B N t=
      U1011OriginalFifteenFixedCellNative.main p B N t+U1011OriginalFifteenFixedCellNative.signedAP p B N t-
      U1011OriginalFifteenFixedCellNative.signedCentre p B N t := by
  have hl := joint_native_legality hN ht p hp B hv hw hc hb
  have hz : U1011OriginalFifteenFixedCellNative.Z p B N≤(slots t 3:ℝ) := by simpa only [slots,Matrix.cons_val_three] using hl.2.2.1
  have hcop := fullPrefix_coprime_lowered_sieve ht hz
  exact currentChen_quotient_actualRosser_plus_main_and_errors N (fullPrefix t)
    (Nat.ceil (U1011OriginalFifteenFixedCellNative.Z p B N))
    (U1011OriginalFifteenFixedCellNative.Z p B N) (U1011OriginalFifteenFixedCellNative.D p B N) (Nat.le_ceil _) hcop

theorem joint_native_row_upper {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (hp : p.val<15) (B : Box)
    (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) :
    U11Adaptive.weight N t≤U1011OriginalFifteenFixedCellNative.main p B N t+
      U1011OriginalFifteenFixedCellNative.signedAP p B N t-U1011OriginalFifteenFixedCellNative.signedCentre p B N t := by
  have hl := joint_native_legality hN ht p hp B hv hw hc hb
  have h12 := (joint_carrier_order ht).2.2.2.2.1
  have hz2 : U1011OriginalFifteenFixedCellNative.Z p B N≤(t.1.2:ℝ) := hl.2.2.1.trans (by exact_mod_cast h12.le)
  have heq : U11Adaptive.weight N t=((chenSiftedQuotientPrimeSource N (fullPrefix t) (t.1.2:ℝ)).card:ℝ) := by
    rw [fullPrefix_eq_multiplier]
    rfl
  have hcount : U11Adaptive.weight N t≤((chenSiftedQuotientPrimeSource N (fullPrefix t)
      (U1011OriginalFifteenFixedCellNative.Z p B N)).card:ℝ) := by
    rw [heq]
    exact_mod_cast Finset.card_le_card (U11LoweredRosser.siftedSource_subset_lowered N _ _ _ hz2)
  have hu := currentChen_quotient_actualRosser_upper N (fullPrefix t)
    (Nat.ceil (U1011OriginalFifteenFixedCellNative.Z p B N))
    (U1011OriginalFifteenFixedCellNative.Z p B N) (U1011OriginalFifteenFixedCellNative.D p B N)
    (Nat.le_ceil _) hl.2.1 hl.2.2.2
  exact (hcount.trans hu).trans_eq (joint_estimator_identity hN ht p hp B hv hw hc hb)

end
end ImbalancedChen.P5Z.U1011OriginalFifteenJointNativeRows
