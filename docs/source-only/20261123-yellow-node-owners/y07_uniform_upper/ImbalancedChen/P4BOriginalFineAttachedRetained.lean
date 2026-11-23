import ImbalancedChen.P4BOriginalFineAttachedUpper
import ImbalancedChen.P4BOriginalUpperFourierTailPaid
import ImbalancedChen.P4BActualUpperTrimPayment
import ImbalancedChen.P4BActualUpperRoughPrimeReserveZero

/-! Recover the whole smooth, rank-two attached PP family from its literal
retained arithmetic rows. The moving band, proper powers, two original
groups, nonzero signed coefficients and coprime means stay in the sum. -/
namespace ImbalancedChen.P4BOriginalFineAttachedRetained

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P4BOriginalFineAttachedUpper (Selection retention)
open P4AOriginalNewFifthUnion (data)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFull87HistoryCore (width_pos)
open P4BOuterRampRoughness (baseline)
open P4BArbitraryWidthUpperPairProfile (licence)
open P4BArbitraryWidthUpperPostModulusTail (Supported)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le target_le_countingScale)
open P4BOriginalUpperFourierTailPaid (retainedUpperAtlas retainedRowBank)
open P4BActualSmoothHyperbolaCorrection (actualActiveUpperCap)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (trimReserve properPowerReserve roughPrimeReserve)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)

variable {m r n q : ℕ} {e : ℚ} {a nu v etaPP betaMax extra : ℝ} {ft : ℝ → ℝ}

/-- The *raw* first-exit arm has its own strict physical bound.  This
uses the actual selected ancestor rule on the actual rough factor. -/
theorem attached_support (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) (hnu : 0 < nu) {N : ℕ} (hN : 2 ≤ N) {d : ℕ}
    (hd : attachedUpperCoefficient nu v s.beta
      (retention m r n e q a (nu * s.beta ^ 2)) id N d ≠ 0) :
    (d : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  let omega := nu * s.beta ^ 2
  let ell := nu * s.beta
  let f := retention m r n e q a omega N
  obtain ⟨u, _, t, ht, hprod, hu, _⟩ :=
    actualSmallRoughRho_ne_zero_factors f N N ((N : ℝ) ^ omega)
      ((N : ℝ) ^ (nu * v)) ((N : ℝ) ^ ell) hd
  have hraw := (P4AOriginalFiniteFallbackRange.raw_range (bank m)
    (P4AOriginalFiniteFallbackCanonical.bounded m) (P4AOriginalFull87HistoryCore.width r)
    (width_pos r) n (data e q a) he omega N N hN omega ((N : ℝ) ^ (nu * v))
    (mul_pos hnu (sq_pos_of_pos s.pos)) ht).2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hN1
  calc
    (d : ℝ) = (u : ℝ) * (t : ℝ) := by rw [hprod, Nat.cast_mul]
    _ ≤ (N : ℝ) ^ ell * (t : ℝ) := mul_le_mul_of_nonneg_right hu.le (Nat.cast_nonneg _)
    _ < (N : ℝ) ^ ell * (N : ℝ) ^ (299 / 500 : ℝ) :=
      mul_lt_mul_of_pos_left hraw (Real.rpow_pos_of_pos hNp _)
    _ = (N : ℝ) ^ (ell + 299 / 500) := (Real.rpow_add hNp _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1
      (by dsimp only [ell]; linarith only [s.small_lt])

private theorem active_cap (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) (hnu : 0 < nu) {N : ℕ} (hN : 2 ≤ N) :
    (actualActiveUpperCap nu v s.beta (retention m r n e q a (nu * s.beta ^ 2)) id N : ℝ)
      ≤ (N : ℝ) ^ (599 / 1000 : ℝ) := by
  have hpow := Real.rpow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (599 / 1000 : ℝ)
  have hcap : actualActiveUpperCap nu v s.beta (retention m r n e q a (nu * s.beta ^ 2)) id N ≤
      Nat.floor ((N : ℝ) ^ (599 / 1000 : ℝ)) := by
    apply Finset.sup_le
    intro d hd
    exact (Nat.le_floor_iff hpow).mpr (attached_support s he hnu hN (Finset.mem_filter.mp hd).2).le
  exact (Nat.cast_le.mpr hcap).trans (Nat.floor_le hpow)

def remainingRows {b kappa nu v w : ℝ} (hb : 0 < b) (hnu : 0 < nu) (hv : 0 < v)
    (hw : 0 < w) (hg : 2 * w ≤ baseline b kappa - nu * v)
    (N K p : ℕ) (kap0 beta : ℝ) (f : ℕ → List ℕ → Bool) : ℂ :=
  ∑ js ∈ chartBank N 2,
    (retainedRowBank b kappa w N K (js.getD 0 0) (js.getD 1 0) kap0 nu v beta f id p -
      properPowerReserve (licence hb hnu hv hw hg N) K N N kap0
        (attachedUpperModuli nu v beta f id N)
        (fun d => (attachedUpperCoefficient nu v beta f id N d : ℂ)) js)

/-- The accuracy and threshold precede every admissible width. For
fixed width the first term has its explicit inverse-width cost. -/
theorem exists_attached_recovery (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) {b kappa kap0 : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hk : 0 < kappa)
    (hnu : 0 < nu) (hv : 0 < v) (ht : 0 < kap0) (ht1 : kap0 < 1)
    (K : ℕ) (hK : 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, ∀ᶠ N : ℕ in atTop,
    ∀ (w : ℝ) (hw : 0 < w) (hg : 2 * w ≤ baseline b kappa - nu * v),
      let f := retention m r n e q a (nu * s.beta ^ 2)
      let E := Part3.primeProductSignedError 2 N N (attachedUpperModuli nu v s.beta f id N)
        (attachedUpperCoefficient nu v s.beta f id N)
        (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) w)
      ‖(E : ℂ) - remainingRows hb hnu hv hw hg N K p kap0 s.beta f‖ ≤
        (C / w ^ 24) * N / logScale (countingScale N) ^ (p + 3) +
          (N : ℝ) / (Real.log (N : ℝ)) ^ p := by
  obtain ⟨C, hC, hTail⟩ := P4BOriginalUpperFourierTailPaid.exists_eventual_original_upper_fourier_tail_paid
    (599 / 1000 : ℝ) (by norm_num)
  obtain ⟨Nr, hRough⟩ := P4BActualUpperRoughPrimeReserveZero.exists_actual_upper_roughPrimeReserve_zero
    (kappa := kappa) K hK hb hnu hv
  refine ⟨C, hC, ?_⟩
  intro p
  filter_upwards [hTail b kappa nu v hb hb1 hk hnu hv,
    P4BActualUpperTrimPayment.eventually_actual_upper_trim_logAccuracy kap0 ht ht1
      (599 / 1000 : ℝ) (by norm_num) p 1 (by norm_num),
    eventually_ge_atTop Nr, eventually_ge_atTop (2 : ℕ)] with N hT hTr hNr hN
  intro w hw hg
  let f := retention m r n e q a (nu * s.beta ^ 2)
  let Q := attachedUpperModuli nu v s.beta f id N
  let rho := attachedUpperCoefficient nu v s.beta f id N
  let E := Part3.primeProductSignedError 2 N N Q rho
    (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) w)
  let F := retainedUpperAtlas hb hnu hv hw hg N K kap0 s.beta f id p
  let R := remainingRows hb hnu hv hw hg N K p kap0 s.beta f
  let T := trimReserve (licence hb hnu hv hw hg N) N N kap0 Q (fun d => (rho d : ℂ))
  let D := Nat.floor ((N : ℝ) ^ (599 / 1000 : ℝ))
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow := Real.one_le_rpow hN1 (show (0 : ℝ) ≤ 599 / 1000 by norm_num)
  have hD : 1 ≤ D := (Nat.le_floor_iff (zero_le_one.trans hpow)).mpr (by simpa using hpow)
  have hSupport : Supported nu v s.beta f id N D := by
    intro d _ hd
    exact (Nat.le_floor_iff (zero_le_one.trans hpow)).mpr (attached_support s he hnu hN hd).le
  have hFourier : ‖(E : ℂ) - F‖ ≤ (C / w ^ 24) * N / logScale (countingScale N) ^ (p + 3) :=
    hT w hw hg K D p kap0 s.beta f id hD (Nat.floor_le (zero_le_one.trans hpow)) hSupport
  have hTrim : ‖T‖ ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ p := by
    simpa only [one_mul] using hTr b kappa nu v w hb hnu hv hw hg s.beta f id (active_cap s he hnu hN)
  have hEq : F = T + R := by
    unfold F retainedUpperAtlas R remainingRows
    apply congrArg (fun z : ℂ => T + z)
    apply Finset.sum_congr rfl
    intro js hjs
    rw [hRough N hNr w hw hg kap0 Q (fun d => (rho d : ℂ)) js hjs, add_zero]
  change ‖(E : ℂ) - R‖ ≤ _
  calc
    ‖(E : ℂ) - R‖ = ‖((E : ℂ) - F) + T‖ := by rw [hEq]; congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hFourier hTrim)

/-- A native arithmetic statement for the upstream high-rank supplier.
The band is fixed by the requested integer accuracy p; the signed
proper-power term still occurs on its original labelled charts. -/
theorem uniformPP_of_remainingRows (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) {b kappa kap0 w : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hk : 0 < kappa)
    (hnu : 0 < nu) (hv : 0 < v) (ht : 0 < kap0) (ht1 : kap0 < 1)
    (K : ℕ) (hK : 2 ≤ K) (hw : 0 < w) (hg : 2 * w ≤ baseline b kappa - nu * v)
    (hRows : ∀ p : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ‖remainingRows hb hnu hv hw hg N K p kap0 s.beta (retention m r n e q a (nu * s.beta ^ 2))‖ ≤
        D * (N : ℝ) / (Real.log (N : ℝ)) ^ p) :
    Part3.UniformPrimeProductTarget (ι := Unit) 2 id
      (attachedUpperModuli nu v s.beta (retention m r n e q a (nu * s.beta ^ 2)) id)
      (attachedUpperCoefficient nu v s.beta (retention m r n e q a (nu * s.beta ^ 2)) id)
      (fun N _ => P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) w) := by
  obtain ⟨C, hC, hrec⟩ := exists_attached_recovery s he hb hb1 hk hnu hv ht ht1 K hK
  intro A _
  let p := Nat.ceil A
  obtain ⟨D, hD, hlocal⟩ := hRows p
  have hcost : 0 ≤ C / w ^ 24 := div_nonneg hC (pow_nonneg hw.le _)
  let c := C / w ^ 24 + 1 + D
  have hc : 0 < c := by dsimp only [c]; linarith
  refine ⟨c, hc, eventually_atTop.mp ?_⟩
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hrec p, hlocal, hlog.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)]
    with N hR hD' hl hN
  intro hEven _
  let f := retention m r n e q a (nu * s.beta ^ 2)
  let R := remainingRows hb hnu hv hw hg N K p kap0 s.beta f
  let E := Part3.primeProductSignedError 2 N N (attachedUpperModuli nu v s.beta f id N)
    (attachedUpperCoefficient nu v s.beta f id N)
    (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) w)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl1 : 1 ≤ Real.log (N : ℝ) := hl
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hl1
  have hlX : Real.log (N : ℝ) ≤ logScale (countingScale N) := by
    have hX := target_le_countingScale N
    have hx := countingScale_one_le (show 0 < N by omega)
    have h := Real.log_le_log hNp (show (N : ℝ) ≤ 7 * countingScale N by linarith)
    unfold logScale
    linarith
  have hpow : (Real.log (N : ℝ)) ^ p ≤ logScale (countingScale N) ^ (p + 3) :=
    (pow_le_pow_left₀ hl0.le hlX p).trans (pow_le_pow_right₀ (hl1.trans hlX) (by omega))
  have htail := div_le_div_of_nonneg_left (mul_nonneg hcost hNp.le) (pow_pos hl0 p) hpow
  have hR' := (hR w hw hg).trans (add_le_add_right htail _)
  have hA : (Real.log (N : ℝ)) ^ A ≤ (Real.log (N : ℝ)) ^ p := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hl1 (Nat.le_ceil A)
  calc
    |E| = ‖((E : ℂ) - R) + R‖ := by rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ((C / w ^ 24) * N / (Real.log (N : ℝ)) ^ p + (N : ℝ) / (Real.log (N : ℝ)) ^ p) +
          D * N / (Real.log (N : ℝ)) ^ p :=
      (norm_add_le _ _).trans (add_le_add hR' (hD' hEven))
    _ = c * N / (Real.log (N : ℝ)) ^ p := by dsimp only [c]; ring
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hc.le hNp.le) (Real.rpow_pos_of_pos hl0 _) hA

/-- Direct call contract from the physical retained rows to the original
real upper count. Each allowable width may have its own D and N0.
Selection, policy, beta, aligned k and the enumeration cap are fixed. -/
theorem upper_of_remainingRows_for_all_widths (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) {b kappa kap0 : ℝ} (hb : (1 / 2 : ℝ) < b) (hb1 : b < 1)
    (hk : 0 < kappa) (hk1 : kappa < 1) (ht : 0 < kap0) (ht1 : kap0 < 1)
    (hnu : 0 < nu) (hv : 0 < v) (hcut : nu * v = 19 / 96)
    (hgate : nu * v < baseline b kappa) (K : ℕ) (hK : 2 ≤ K)
    (hRows : ∀ (w : ℝ) (hw : 0 < w) (hg : 2 * w ≤ baseline b kappa - nu * v),
      ∀ p : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ‖remainingRows (by linarith : 0 < b) hnu hv hw hg N K p kap0 s.beta
        (retention m r n e q a (nu * s.beta ^ 2))‖ ≤ D * (N : ℝ) / (Real.log (N : ℝ)) ^ p) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤ (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  apply s.upper_of_attached_PP hb hb1 hk hk1 hnu hv hcut hgate
  intro w hw hg
  exact uniformPP_of_remainingRows s he (by linarith) hb1.le hk hnu hv ht ht1 K hK hw hg (hRows w hw hg)

/-- One realized policy works in the receiver for every `1/2 < b < 1`.
The counting and trim cutoffs and the HB order are fixed here, so the
physical row estimate is the sole remaining analytic input. -/
theorem exists_policy_for_every_b (a zeta betaMax : ℝ) (ha : 0 < a) (haMax : a ≤ 1 / 800)
    (hz : 0 < zeta) (hbMax : 0 < betaMax) (ft : ℝ → ℝ) (hft : ∀ x : ℝ, 0 < x → 0 < ft x)
    (qMin mMin : ℕ) :
    ∃ (m r n : ℕ) (e : ℚ) (q : ℕ) (etaPP : ℝ)
      (s : Selection m r n e q a 1 (19 / 96) etaPP betaMax zeta ft),
    qMin ≤ q ∧ mMin ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q ∧
    ∀ (b : ℝ) (hb : (1 / 2 : ℝ) < b), b < 1 →
      (∀ (w : ℝ) (hw : 0 < w) (hg : 2 * w ≤ baseline b (1 / 4) - 1 * (19 / 96)),
       ∀ p : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ N : ℕ in atTop, Even N →
         ‖remainingRows (by linarith : 0 < b) zero_lt_one (by norm_num : (0 : ℝ) < 19 / 96)
           hw hg N 2 p (1 / 8) s.beta (retention m r n e q a (1 * s.beta ^ 2))‖ ≤
           D * (N : ℝ) / (Real.log (N : ℝ)) ^ p) →
      ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
        (RealB b N : ℝ) ≤ (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  obtain ⟨m, r, n, e, q, etaPP, he, _, hqMin, _, _, hmesh, _, _, ⟨s⟩⟩ :=
    P4BOriginalFineAttachedUpper.exists_counting_selection a zeta betaMax ha haMax hz hbMax ft hft qMin mMin
  refine ⟨m, r, n, e, q, etaPP, s, hqMin, hmesh, ?_⟩
  intro b hb hb1 hRows
  have hgate : (1 : ℝ) * (19 / 96) < baseline b (1 / 4) := by
    unfold baseline
    apply (lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + b)).mpr
    linarith only [hb]
  exact upper_of_remainingRows_for_all_widths s he.le hb hb1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) zero_lt_one (by norm_num) (by norm_num) hgate 2 (by norm_num) hRows

end
end ImbalancedChen.P4BOriginalFineAttachedRetained
