import ImbalancedChen.P4BOriginalAllWidthProperPowers
import ImbalancedChen.P4BOriginalFineAttachedRetained

/-! Compare two literal retained row sums for one realized Fine selection.
This permits a small analytic trim on the arithmetic side of the fixed
1/8 reporting convention. -/
namespace ImbalancedChen.P4BOriginalFineRetainedCalibration

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P4BOriginalFineAttachedUpper (Selection retention)
open P4BOriginalFineAttachedRetained (attached_support remainingRows exists_attached_recovery)
open P4BOriginalUpperFourierTailPaid (retainedRowBank)
open P4BActualSmoothHyperbolaCorrection (actualActiveUpperCap)
open P4BOuterRampRoughness (baseline)
open P4BArbitraryWidthUpperPairProfile (licence)
open P4BArbitraryWidthUpperBlockGeometry (countingScale target_le_countingScale countingScale_one_le)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (properPowerReserve)

variable {m r n q : ℕ} {e : ℚ} {a nu v etaPP betaMax extra : ℝ} {ft : ℝ → ℝ}

def retainedSum (b kappa width : ℝ) (N K p : ℕ) (t nu v beta : ℝ)
    (f : ℕ → List ℕ → Bool) : ℂ :=
  ∑ js ∈ chartBank N 2,
    retainedRowBank b kappa width N K (js.getD 0 0) (js.getD 1 0) t nu v beta f id p

private theorem cap_le (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) (hnu : 0 < nu) {N : ℕ} (hN : 2 ≤ N) :
    (actualActiveUpperCap nu v s.beta (retention m r n e q a (nu*s.beta^2)) id N : ℝ) ≤
      (N : ℝ)^(599/1000 : ℝ) := by
  let X := (N : ℝ)^(599/1000 : ℝ)
  have hX : 0 ≤ X := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfloor : actualActiveUpperCap nu v s.beta (retention m r n e q a (nu*s.beta^2))
      id N ≤ Nat.floor X := by
    apply Finset.sup_le
    intro d hd
    exact (Nat.le_floor_iff hX).mpr (attached_support s he hnu hN (Finset.mem_filter.mp hd).2).le
  exact (Nat.cast_le.mpr hfloor).trans (Nat.floor_le hX)

/-- This is an estimate of a difference of two explicitly defined
original arithmetic sums, with no admissibility or SW estimate as input. -/
theorem eventually_proper_removed (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) (hnu : 0 < nu) (hv : 0 < v) (p : ℕ) (d : ℝ) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, ∀ (b kappa width : ℝ) (hb : 0 < b) (hk : 0 < kappa)
      (hw : 0 < width) (hg : 2*width ≤ baseline b kappa - nu*v) (K : ℕ) (t : ℝ),
      let f := retention m r n e q a (nu*s.beta^2)
      ‖retainedSum b kappa width N K p t nu v s.beta f -
        remainingRows hb hnu hv hw hg N K p t s.beta f‖ ≤ d*(N : ℝ)/(Real.log (N : ℝ))^p := by
  filter_upwards [P4BOriginalAllWidthProperPowers.eventually_all_width_properPower_sum_norm
    nu v (599/1000) hnu hv (by norm_num) (by norm_num) p d hd,
    eventually_ge_atTop (2 : ℕ)] with N hbudget hN
  intro b kappa w hb hk hw hg K t
  let f := retention m r n e q a (nu*s.beta^2)
  let P (js : List ℕ) := properPowerReserve (licence hb hnu hv hw hg N) K N N t
    (attachedUpperModuli nu v s.beta f id N)
    (fun z => (attachedUpperCoefficient nu v s.beta f id N z : ℂ)) js
  have hsum : retainedSum b kappa w N K p t nu v s.beta f -
      remainingRows hb hnu hv hw hg N K p t s.beta f = ∑ js ∈ chartBank N 2, P js := by
    unfold retainedSum remainingRows
    rw [Finset.sum_sub_distrib]
    dsimp only [P]
    ring
  change ‖retainedSum b kappa w N K p t nu v s.beta f -
    remainingRows hb hnu hv hw hg N K p t s.beta f‖ ≤ _
  rw [hsum]
  exact (norm_sum_le _ _).trans (hbudget b kappa w hb hk hw hg K t s.beta f id (cap_le s he hnu hN))

/-- One fixed permissible width. The accuracy p is chosen after the
width-dependent constant. Both trim and Fourier recover the same E. -/
private theorem fixed_error (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) {b kappa w t : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hk : 0 < kappa)
    (hnu : 0 < nu) (hv : 0 < v) (hw : 0 < w) (hg : 2*w ≤ baseline b kappa-nu*v)
    (ht : 0 < t) (ht1 : t < 1) (K : ℕ) (hK : 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, ∀ᶠ N : ℕ in atTop,
      let f := retention m r n e q a (nu*s.beta^2)
      let E := Part3.primeProductSignedError 2 N N (attachedUpperModuli nu v s.beta f id N)
        (attachedUpperCoefficient nu v s.beta f id N)
        (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) w)
      ‖(E : ℂ) - remainingRows hb hnu hv hw hg N K p t s.beta f‖ ≤
        C*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨C, hC, heq⟩ := exists_attached_recovery s he hb hb1 hk hnu hv ht ht1 K hK
  let Z := C/w^24
  have hZ : 0 ≤ Z := div_nonneg hC (pow_nonneg hw.le _)
  refine ⟨Z+1, by linarith, ?_⟩
  intro p
  filter_upwards [heq p, eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)]
    with N hpay hlog hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hscale : Real.log (N : ℝ) ≤ logScale (countingScale N) := by
    have hX := target_le_countingScale N
    have hp := countingScale_one_le (show 0 < N by omega)
    have hh := Real.log_le_log hN0 (show (N : ℝ) ≤ 7*countingScale N by linarith)
    unfold logScale
    linarith
  have hpow := (pow_le_pow_left₀ (zero_le_one.trans hlog) hscale p).trans
    (pow_le_pow_right₀ (hlog.trans hscale) (show p ≤ p+3 by omega))
  have htail := div_le_div_of_nonneg_left (mul_nonneg hZ hN0.le)
    (pow_pos (zero_lt_one.trans_le hlog) p) hpow
  exact (hpay w hw hg).trans ((add_le_add_right htail _).trans_eq (by dsimp only [Z]; ring))

/-- Different actual trims (and, if desired, different legal HB orders)
can be compared unconditionally through the same physical discrepancy.
The second object is the literal Y07 sum with its original subtraction. -/
theorem retained_to_reported (s : Selection m r n e q a nu v etaPP betaMax extra ft)
    (he : 0 ≤ e) {b kappa w t u : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hk : 0 < kappa)
    (hnu : 0 < nu) (hv : 0 < v) (hw : 0 < w) (hg : 2*w ≤ baseline b kappa-nu*v)
    (ht : 0 < t) (ht1 : t < 1) (hu : 0 < u) (hu1 : u < 1)
    (K J : ℕ) (hK : 2 ≤ K) (hJ : 2 ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, ∀ᶠ N : ℕ in atTop,
      let f := retention m r n e q a (nu*s.beta^2)
      ‖retainedSum b kappa w N K p t nu v s.beta f -
        remainingRows hb hnu hv hw hg N J p u s.beta f‖ ≤ C*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨D, hD, hT⟩ := fixed_error s he hb hb1 hk hnu hv hw hg ht ht1 K hK
  obtain ⟨G, hG, hU⟩ := fixed_error s he hb hb1 hk hnu hv hw hg hu hu1 J hJ
  refine ⟨1+D+G, by linarith, ?_⟩
  intro p
  filter_upwards [eventually_proper_removed s he hnu hv p 1 zero_lt_one, hT p, hU p]
    with N hpp hfirst hsecond
  let f := retention m r n e q a (nu*s.beta^2)
  let E : ℂ := (Part3.primeProductSignedError 2 N N (attachedUpperModuli nu v s.beta f id N)
    (attachedUpperCoefficient nu v s.beta f id N)
    (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) w) : ℝ)
  let R := remainingRows hb hnu hv hw hg N K p t s.beta f
  let S := remainingRows hb hnu hv hw hg N J p u s.beta f
  let A := retainedSum b kappa w N K p t nu v s.beta f
  change ‖A-S‖ ≤ _
  have hR : ‖R-E‖ = ‖E-R‖ := norm_sub_rev _ _
  calc
    _ = ‖((A-R)+(R-E))+(E-S)‖ := by congr 1; ring
    _ ≤ (‖A-R‖+‖E-R‖)+‖E-S‖ := by
      exact (norm_add_le _ _).trans (add_le_add_right ((norm_add_le _ _).trans_eq (by rw [hR])) _)
    _ ≤ (1*(N : ℝ)/(Real.log (N : ℝ))^p + D*N/(Real.log (N : ℝ))^p) +
        G*N/(Real.log (N : ℝ))^p :=
      add_le_add (add_le_add (hpp b kappa w hb hk hw hg K t) hfirst) hsecond
    _ = _ := by ring

/-- Choose the analytic trim after the local medium parameter. The
denominator is the complete local-scale change with theta=599/1000. -/
theorem exists_manuscript_trim (localKappa : ℝ) (hlocal : 0 < localKappa) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t < localKappa/(4*(1+localKappa)) ∧
      (599/1000 : ℝ)/(1-t) < 3/5 := by
  let t := min (1/1200 : ℝ) (localKappa/(8*(1+localKappa)))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have h1 : t ≤ 1/1200 := min_le_left _ _
  have h2 : t ≤ localKappa/(8*(1+localKappa)) := min_le_right _ _
  refine ⟨t, ht, by linarith, ?_, ?_⟩
  · apply h2.trans_lt
    exact div_lt_div_of_pos_left hlocal (by positivity) (by linarith)
  · apply (div_lt_iff₀ (by linarith : 0 < 1-t)).mpr
    linarith only [h1]

end
end ImbalancedChen.P4BOriginalFineRetainedCalibration
