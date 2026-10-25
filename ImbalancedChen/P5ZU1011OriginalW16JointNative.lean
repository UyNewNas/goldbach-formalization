import ImbalancedChen.P5ZU1011OriginalW16NearCapSmallBeta

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Original W16 native rows for the REAL JOINT U10/U11 source, including its
low p4 band. Membership in the U11 high-band source is never asserted.
Prime order, positivity and target coprimality come from jointSelector.
The old midpoint and near-cap rational W cells both receive their literal
original support/coefficient/level. A low-band tuple uses the same actual
quotient count at p2, with cutoff lowered to Z<=p1 before any coprime
density is used. No AP estimate, W density or H248 licence is assumed.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16JointNative
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalW16FixedCellNative (Tplus)
open P5U1011JointOverlap

def physicalResidual (B : Box) (nu delta : ℚ) : ℚ := nu-Tplus B-20*delta
def physicalCutoff (B : Box) (nu delta xi rho : ℚ) : ℚ :=
  min (B.lo 3-xi) (physicalResidual B nu delta/(2+rho))

/-- Only elementary parameter inequalities and the actual JOINT log
box are used. This helper has no high-band membership input. -/
theorem joint_physical_legality {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (nu delta xi rho : ℚ)
    (hxi : 0≤xi) (hrho : 0<rho) (hres : 0<physicalResidual B nu delta)
    (hbox : coordinates N t∈B.region) :
    0<(N:ℝ)^(physicalCutoff B nu delta xi rho:ℝ) ∧
      1<(N:ℝ)^(physicalResidual B nu delta:ℝ) ∧
      (N:ℝ)^(physicalCutoff B nu delta xi rho:ℝ)≤(t.1.1:ℝ) ∧
      (N:ℝ)^(physicalCutoff B nu delta xi rho:ℝ)≤(N:ℝ)^(physicalResidual B nu delta:ℝ) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hre : (0:ℝ)<(physicalResidual B nu delta:ℝ) := by exact_mod_cast hres
  have hr : (0:ℝ)<(rho:ℝ) := by exact_mod_cast hrho
  have hx : (0:ℝ)≤(xi:ℝ) := by exact_mod_cast hxi
  have hcutle : (physicalCutoff B nu delta xi rho:ℝ)≤(physicalResidual B nu delta:ℝ) := by
    have hdiv : (physicalResidual B nu delta:ℝ)/(2+(rho:ℝ))≤(physicalResidual B nu delta:ℝ) := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    have hq : physicalCutoff B nu delta xi rho≤physicalResidual B nu delta/(2+rho) := min_le_right _ _
    have hh : (physicalCutoff B nu delta xi rho:ℝ)≤(physicalResidual B nu delta:ℝ)/(2+(rho:ℝ)) := by exact_mod_cast hq
    exact hh.trans hdiv
  have hfirst : (N:ℝ)^(physicalCutoff B nu delta xi rho:ℝ)≤(t.1.1:ℝ) := by
    have hq : physicalCutoff B nu delta xi rho≤B.lo 3-xi := min_le_left _ _
    have hh : (physicalCutoff B nu delta xi rho:ℝ)≤(B.lo 3:ℝ)-(xi:ℝ) := by exact_mod_cast hq
    have hpow := slot_rpow hN ht (3:Fin 4)
    have h := Real.rpow_le_rpow_of_exponent_le hn.le
      (show (physicalCutoff B nu delta xi rho:ℝ)≤coordinates N t 3 by linarith [hbox.1 3])
    simpa only [slots,Matrix.cons_val_three] using h.trans_eq hpow
  exact ⟨Real.rpow_pos_of_pos hp _,Real.one_lt_rpow hn hre,hfirst,
    Real.rpow_le_rpow_of_exponent_le hn.le hcutle⟩

/-- The existing midpoint W native level, now on genuine joint tuples. -/
theorem midpoint_legality {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region) :
    0<U1011OriginalW16FixedCellNative.Z B N ∧ 1<U1011OriginalW16FixedCellNative.D B N ∧
      U1011OriginalW16FixedCellNative.Z B N≤(t.1.1:ℝ) ∧
      U1011OriginalW16FixedCellNative.Z B N≤U1011OriginalW16FixedCellNative.D B N := by
  have hp := U1011OriginalW16FixedCellNative.rational_parameters B hvalid hpositive htest
  exact joint_physical_legality hN ht B (U1011OriginalW16FixedCellNative.nu B)
    (U1011OriginalW16FixedCellNative.delta B) (U1011OriginalW16FixedCellNative.xi B)
    (U1011OriginalW16FixedCellNative.rho B) hp.2.2.2.1.le hp.2.2.2.2.1 hp.2.2.2.2.2.1 hbox

/-- The precision eta is fixed before N/tuple on both JOINT bands. -/
theorem near_cap_legality {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest wPolicy B=true)
    (hbox : coordinates N t∈B.region) :
    0<U1011OriginalW16NearCapNative.Z B eta N ∧ 1<U1011OriginalW16NearCapNative.D B eta N ∧
      U1011OriginalW16NearCapNative.Z B eta N≤(t.1.1:ℝ) ∧
      U1011OriginalW16NearCapNative.Z B eta N≤U1011OriginalW16NearCapNative.D B eta N := by
  have hp := U1011OriginalW16NearCapNative.rational_parameters B eta heta hvalid hpositive htest
  exact joint_physical_legality hN ht B (U1011OriginalW16NearCapNative.nu B eta)
    (U1011OriginalW16NearCapNative.delta B eta) (U1011OriginalW16NearCapNative.xi B eta)
    (U1011OriginalW16NearCapNative.rho B eta) hp.2.2.2.1.le hp.2.2.2.2.1 hp.2.2.2.2.2.1 hbox

/-- The literal quotient row shared by low/high bands. The function is
defined on every tuple and imposes no fictitious high-band predicate. -/
def jointWeight (N : ℕ) (t : Four) : ℝ :=
  ((chenSiftedQuotientPrimeSource N (fullPrefix t) (t.1.2:ℝ)).card:ℝ)

theorem joint_row_upper {N : ℕ} {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (Z R : ℝ) (hZ : Z≤(t.1.1:ℝ)) (hR : 1<R) (hZR : Z≤R) :
    jointWeight N t≤U11LoweredRosser.mainTerm N t Z R+
      U11LoweredRosser.signedAP N t Z R-U11LoweredRosser.signedCentre N t Z R := by
  have h12 := (joint_carrier_order ht).2.2.2.2.1
  have hZ2 : Z≤(t.1.2:ℝ) := hZ.trans (by exact_mod_cast h12.le)
  have hcop : Nat.Coprime (fullPrefix t) (sieveProduct N (Nat.ceil Z)) :=
    fullPrefix_coprime_lowered_sieve ht (by simpa [slots] using hZ)
  have hcount : jointWeight N t≤((chenSiftedQuotientPrimeSource N (fullPrefix t) Z).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (U11LoweredRosser.siftedSource_subset_lowered N (fullPrefix t) Z _ hZ2)
  have hupper := currentChen_quotient_actualRosser_density_upper N (fullPrefix t) (Nat.ceil Z)
    Z R (Nat.le_ceil Z) hcop hR hZR
  exact (hcount.trans hupper).trans_eq (by
    rw [fullPrefix_eq_multiplier]
    rfl)

theorem midpoint_row_upper {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region) :
    jointWeight N t≤U1011OriginalW16FixedCellNative.main B N t+
      U1011OriginalW16FixedCellNative.signedAP B N t-U1011OriginalW16FixedCellNative.signedCentre B N t := by
  have hleg := midpoint_legality hN ht B hvalid hpositive htest hbox
  exact joint_row_upper ht _ _ hleg.2.2.1 hleg.2.1 hleg.2.2.2

theorem near_cap_row_upper {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest wPolicy B=true)
    (hbox : coordinates N t∈B.region) :
    jointWeight N t≤U1011OriginalW16NearCapNative.main B eta N t+
      U1011OriginalW16NearCapNative.signedAP B eta N t-U1011OriginalW16NearCapNative.signedCentre B eta N t := by
  have hleg := near_cap_legality hN ht B eta heta hvalid hpositive htest hbox
  exact joint_row_upper ht _ _ hleg.2.2.1 hleg.2.1 hleg.2.2.2

/-- Near-cap data remain immutable and contain no derived row/licence. -/
abbrev JointWNativeData := U1011OriginalW16NearCapNative.NativeData

theorem JointWNativeData.row_upper (d : JointWNativeData) {N : ℕ} (hN : 1<N)
    {E : ℕ×ℕ → Prop} {t : Four} (ht : t∈jointSelector N E) (hbox : coordinates N t∈d.B.region) :
    jointWeight N t≤U1011OriginalW16NearCapNative.main d.B d.eta N t+
      U1011OriginalW16NearCapNative.signedAP d.B d.eta N t-U1011OriginalW16NearCapNative.signedCentre d.B d.eta N t :=
  near_cap_row_upper hN ht d.B d.eta d.heta d.hvalid d.hpositive d.htest hbox

end
end ImbalancedChen.P5Z.U1011OriginalW16JointNative
