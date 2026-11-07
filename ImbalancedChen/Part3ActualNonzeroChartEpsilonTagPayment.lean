import ImbalancedChen.Part3ActualChartTagHeightCount
import ImbalancedChen.Part3ActualLogTagBetaRestriction
import ImbalancedChen.Part3FreeEpsilonActualCount
import ImbalancedChen.Part3ActualFixedFeatureCountGeometry
import ImbalancedChen.Part3ActualLogDyadicSchwartzSum

/-!
SOURCEONLY / UNCOMPILED standalone consumer candidate.
Proposed module: ImbalancedChen.Part3ActualNonzeroChartEpsilonTagPayment.
The five public API owner sources above are present in the project source
checkout. Their observed byte hashes and exact public contracts are recorded
in the companion V4 current-API recipe; no old Htag source hash is assumed.
Part3FreeEpsilonActualCount remains an uncompiled dependency: ROOT must first
strict-compile and qualify its original source and imports before compiling
this consumer. Source presence does not establish an importable compiled API.
No parent source, actual receipt, object or cache was modified by this draft.

The complete V3 namespace body, statements and proofs below are byte-preserved.
In particular each uniform existential constant precedes every scale and
atom parameter; kappa=0, the single five-kappa debit, original harmonic
factor and explicit physical-T0 reciprocal losses remain literal.
This is one original t/sign/fKey chart, with the original row split before
squaring. No desired energy/count/spectral estimate is a hypothesis.
Full spectral closure, hLower/hUpper, full K/C and main remain OPEN.
-/
namespace ImbalancedChen.Part3.ActualNonzeroChartEpsilonTagPaymentSourceOnly
noncomputable section
open Classical Finset CommonSmoothCutoff
open GeneralDGateNormalization GeneralDActiveOuterEnergySourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualM2FinitePoissonAdapterSourceOnly
open ActualReciprocalSquarePoissonSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly ActualFixedFeaturePacketPushforwardSourceOnly
open ActualCompletedSquarePushforwardSourceOnly ActualClosedTCountLicenseSourceOnly
open ActualRestrictedChartWeightCountSourceOnly ActualLogTagHSupportSourceOnly
open ActualChartTagHeight576SourceOnly ActualFixedFeatureCountGeometrySourceOnly
open FreeEpsilonActualCountSourceOnly ActualLogDyadicSchwartzSumSourceOnly
open _root_.P3ActualLogAdapterSourceOnly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Explicit physical loss: T^-2 and the extra T^-1/R are NOT hidden in x^eps. -/
def chartShapeFee (T R G : ℝ) : ℝ :=
  (1 + (2 / T) / R) * (((2 / T) * R) ^ 2) * G

private theorem shape_bound {T R G ell : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hG : 0 ≤ G) (hell : 0 ≤ ell) :
    (1 + (2 * ell / T) / R) * ((2 * ell / T) * R) ^ 2 * G ≤
      chartShapeFee T R G * (1 + ell) ^ 3 := by
  have hA : 0 ≤ 2 / T := by positivity
  have hAR : 0 ≤ (2 / T) / R := by positivity
  have hL : 0 ≤ 1 + ell := by linarith
  have hlin : 1 + (2 * ell / T) / R ≤
      (1 + (2 / T) / R) * (1 + ell) := by
    have heq : (2 * ell / T) / R = ((2 / T) / R) * ell := by ring
    rw [heq]
    nlinarith
  have hheight : (2 * ell / T) * R ≤ ((2 / T) * R) * (1 + ell) := by
    have hp := mul_nonneg hA hR.le
    have heq : (2 * ell / T) * R = ((2 / T) * R) * ell := by ring
    rw [heq]
    nlinarith
  have hsq : ((2 * ell / T) * R) ^ 2 ≤
      (((2 / T) * R) ^ 2) * (1 + ell) ^ 2 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (2 * ell / T) * R) hheight 2
    simpa only [mul_pow] using hp
  calc
    _ ≤ (((1 + (2 / T) / R) * (1 + ell)) *
        ((((2 / T) * R) ^ 2) * (1 + ell) ^ 2)) * G :=
      mul_le_mul_of_nonneg_right (mul_le_mul hlin hsq (sq_nonneg _) (by positivity)) hG
    _ = _ := by unfold chartShapeFee; ring

private theorem tag_height_physical {e : MediumAtom} {D : ℕ}
    (hT : 0 < physicalT0 e D) (tag : ℕ × Bool) :
    (tagFrequencyBound tag : ℝ) = 2 * lambda e D tag.1 / physicalT0 e D := by
  simp only [tagFrequencyBound, Nat.cast_mul, Nat.cast_ofNat]
  change 2 * (Hnat tag.1 : ℝ) =
    2 * (physicalT0 e D * (Hnat tag.1 : ℝ)) / physicalT0 e D
  field_simp [hT.ne']

private theorem polynomial_rpow {L p : ℝ} (hL : 0 < L) :
    L ^ p * L ^ (3 : ℕ) = L ^ (3 + p) := by
  simpa only [Nat.cast_ofNat, add_comm] using
    (Real.rpow_add_natCast hL.ne' p 3).symm

/-- Original fKey-image membership supplies the only nonempty-chart input. -/
theorem actual_fKey_mem_nonempty_chart (e : MediumAtom) (D delta g l : ℕ)
    (Z : ℝ) (negative upper : Bool) (fj : ℕ × Bool)
    (hfj : fj ∈ (upperSource (g*l) (signedResidue negative e.residue)
      (e.Q2 / ((D/delta : ℕ) : ℝ)) upper
      (e.sharedSmoothFrequencyBound Z D) (scaleF e D g)).image fKey) :
    (actualChartSource e D delta g l Z negative upper fj).Nonempty := by
  obtain ⟨s, hs, hkey⟩ := mem_image.mp hfj
  exact ⟨s, mem_filter.mpr ⟨hs, hkey⟩⟩

/-- The original actual row mass goes through the EXISTING factor-two split
BEFORE the row square/Poisson pushforward. Thus mixed lower/upper t pairs are
already paid here; they are not a new count-interface gap. This is an inequality
of positive physical row masses, never a beta-subcarrier monotonicity claim. -/
theorem actual_mode_row_mass_closed_two_chart
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (Yb Ys : ℝ)
    {D delta g l : ℕ} (hD : 0 < D) {o : OuterIndex}
    (ho : o ∈ fixedSlice e Yb Ys D delta g l) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (Bb Cc : ℝ) (Lpack : Finset Packet) :
    sixSmoothMass Bb Cc Lpack
      (finiteReciprocalRow (g*l) (signedResidue negative e.residue)
        (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
        (actualModeLambda e D delta g l m negative u k)
        (actualModeOmega e D g l Z tag m negative k)) ≤
      2 * sixSmoothMass Bb Cc Lpack
        (finiteReciprocalRow (g*l) (signedResidue negative e.residue)
          (tChart (e.Q2 / ((D/delta : ℕ) : ℝ)) false)
          (e.sharedSmoothFrequencyBound Z D)
          (actualModeLambda e D delta g l m negative u k)
          (actualModeOmega e D g l Z tag m negative k)) +
      2 * sixSmoothMass Bb Cc Lpack
        (finiteReciprocalRow (g*l) (signedResidue negative e.residue)
          (tChart (e.Q2 / ((D/delta : ℕ) : ℝ)) true)
          (e.sharedSmoothFrequencyBound Z D)
          (actualModeLambda e D delta g l m negative u k)
          (actualModeOmega e D g l Z tag m negative k)) := by
  have hq := actual_quotient_positive e Yb Ys hD ho
  exact actual_base_sixSmoothMass_closed_split e
    (zero_le_one.trans he.2.2.2.1) hq (g*l) (signedResidue negative e.residue)
    (e.sharedSmoothFrequencyBound Z D)
    (actualModeLambda e D delta g l m negative u k)
    (actualModeOmega e D g l Z tag m negative k) Bb Cc Lpack

section ActualChart
variable {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
variable (he : MediumAdmissible B sigma kappa c0 e) (hsigma : 0 ≤ sigma)
variable (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g)
variable {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
variable [NeZero (g*l)] (Z : ℝ) (negative upper : Bool) (fj : ℕ × Bool)
variable (hblock : (actualChartSource e D delta g l Z negative upper fj).Nonempty)
include he hsigma hD hg ho hblock

/-- Count loss at an arbitrary positive epsilon. The actual Hglobal energy is
unchanged on the left. The right uses the PROVED tag cap and explicit T0 fee.
The existential constant depends only on eta (the witness below is universal). -/
theorem actual_chart_energy_count_free_epsilon {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (tag : ℕ × Bool) (m : ℤ × ℤ)
      (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (nu : ℕ), 0 < nu →
      actualChartWeightedEnergy e D delta g l Z tag m negative u k upper fj nu ≤
        C * e.scale ^ eta *
          chartShapeFee (physicalT0 e D)
            (countScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper) (fScale fj.1) *
          (1 + lambda e D tag.1) ^ (3 + eta / 7) / (nu : ℝ) := by
  let p : ℝ := eta / 7
  have hp : 0 < p := by dsimp [p]; positivity
  obtain ⟨K, hK, hcost⟩ := actual_count_cost_product_free_epsilon hp
  refine ⟨576 * K * (13 : ℝ) ^ p, by positivity, ?_⟩
  intro tag m u k nu hnu
  let S : ℝ := e.Q2 / ((D/delta : ℕ) : ℝ)
  let R : ℝ := countScale S upper
  let G : ℝ := fScale fj.1
  let H : ℝ := (tagFrequencyBound tag : ℝ)
  let L : ℝ := 1 + lambda e D tag.1
  have hgeom := actual_nonempty_fBlock_count_geometry he hsigma Yb Ys hD hg ho
    upper negative (e.sharedSmoothFrequencyBound Z D) fj hblock
  have hR : 1 ≤ R := hgeom.2.1
  have hG : 1 ≤ G := hgeom.1
  have hT := hgeom.2.2.1
  have hX := (actual_admissible_geometry he hsigma).1
  have hX0 : 0 ≤ e.scale := zero_le_one.trans hX
  have hH : 1 ≤ H := by
    simpa only [H, tagFrequencyBound] using actual_tag_height_ge_one tag
  have hell : 0 ≤ lambda e D tag.1 :=
    mul_nonneg hT.le (Hreal_pos tag.1).le
  have hL : 0 < L := by dsimp [L]; linarith
  have hprod : G * H * R ≤ (13 * e.scale ^ (7 : ℕ)) * L := by
    have hsep := block_product_le_scale_times_decay hT
      (zero_le_one.trans hG) (zero_le_one.trans hR) (Hreal_pos tag.1).le
    have hsep' : G * H * R ≤
        (1 + 2 * G * R / physicalT0 e D) * L := by
      simpa only [H, L, tagFrequencyBound, Nat.cast_mul, Nat.cast_ofNat,
        lambda, Hreal, base, physicalT0] using hsep
    exact hsep'.trans (mul_le_mul_of_nonneg_right hgeom.2.2.2 hL.le)
  have hpower : (G * H * R) ^ p ≤
      (13 : ℝ) ^ p * e.scale ^ eta * L ^ p := by
    have h7p : (7 : ℝ) * p = eta := by dsimp [p]; ring
    calc
      _ ≤ ((13 * e.scale ^ (7 : ℕ)) * L) ^ p :=
        Real.rpow_le_rpow (by positivity) hprod hp.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) hL.le,
          Real.mul_rpow (by norm_num) (pow_nonneg hX0 7),
          ← Real.rpow_natCast_mul hX0 7 p]
        simp only [Nat.cast_ofNat, h7p]
  have hcount :
      (LichtmanSignedDifferenceMultiplicity.divisorMaximum R H G : ℝ) ^ 5 *
          (harmonic (Nat.floor (2 * R)) : ℝ) ≤
        K * (13 : ℝ) ^ p * e.scale ^ eta * L ^ p :=
    (hcost R H G hR hH hG).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpower hK.le)
  have hshape : (1 + H / R) * (H * R) ^ 2 * G ≤
      chartShapeFee (physicalT0 e D) R G * L ^ (3 : ℕ) := by
    have ht := tag_height_physical hT tag
    simpa only [H, ht, L] using shape_bound hT (zero_lt_one.trans_le hR)
      (zero_le_one.trans hG) hell
  have hq := actual_quotient_positive e Yb Ys hD ho
  have hactual := (actual_chart_weighted_576_tag_height he D delta g l Z tag m
    negative u k hq upper fj nu hnu).1
  have hnur : 0 ≤ (nu : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ 576 *
        ((LichtmanSignedDifferenceMultiplicity.divisorMaximum R H G : ℝ) ^ 5 *
          (harmonic (Nat.floor (2 * R)) : ℝ)) *
        ((1 + H / R) * (H * R) ^ 2 * G) / (nu : ℝ) := by
      convert hactual using 1; dsimp [R, S, H, G]; ring
    _ ≤ 576 * (K * (13 : ℝ) ^ p * e.scale ^ eta * L ^ p) *
        (chartShapeFee (physicalT0 e D) R G * L ^ (3 : ℕ)) / (nu : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnur
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hcount (by norm_num)
      · exact hshape
      · positivity
      · positivity
    _ = _ := by
      have hpow := polynomial_rpow (p := p) hL
      dsimp [R, S, G]
      rw [show 3 + eta / 7 = 3 + p by rfl]
      rw [← hpow]
      ring

/-- Full finite actual log-mode and tag payment, with the genuine nu-harmonic
outer factor retained. J and M are arbitrary finite subsets; no cardinal fee.
Only ONE 5*kappa coefficient debit appears, including kappa=0. The physical
T0^(-delta) Schwartz loss and chartShapeFee's T0^-2/T0^-3 remain explicit. -/
theorem actual_nonzero_chart_count_epsilon_tag_payment
    (hkappa : 0 ≤ kappa) (hZ : 0 < Z) {eta : ℝ} (heta : 0 < eta)
    (decay : ℝ) (hdecay : 0 < decay) (b : ℕ)
    (hb : 3 + eta / 7 + decay ≤ (b : ℝ))
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset ℕ) (M : Finset (ℤ × ℤ)) (N : ℕ) (sign : Bool),
      (∑ j ∈ J, ∑ m ∈ M, ‖coeff e D Z (j, sign) m‖ *
        ∑ nu ∈ Icc 1 N,
          actualChartWeightedEnergy e D delta g l Z (j, sign) m
            negative u k upper fj nu) ≤
      C * _root_.P3ActualJointGSourceOnly.fourierCost b * e.scale ^ (5*kappa + eta) *
        chartShapeFee (physicalT0 e D)
          (countScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper) (fScale fj.1) *
        ((physicalT0 e D) ^ (-decay) / (1 - (2 : ℝ) ^ (-decay))) *
        (harmonic N : ℝ) := by
  obtain ⟨K, hK, henergy⟩ := actual_chart_energy_count_free_epsilon
    he hsigma Yb Ys hD hg ho Z negative upper fj hblock heta
  refine ⟨16 * K, by positivity, ?_⟩
  intro J M N sign
  let R : ℝ := countScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper
  let G : ℝ := fScale fj.1
  let T : ℝ := physicalT0 e D
  let r : ℝ := 3 + eta / 7
  let A : ℝ := K * e.scale ^ eta * chartShapeFee T R G
  have hgeom := actual_nonempty_fBlock_count_geometry he hsigma Yb Ys hD hg ho
    upper negative (e.sharedSmoothFrequencyBound Z D) fj hblock
  have hT : 0 < T := hgeom.2.2.1
  have hR : 0 < R := zero_lt_one.trans_le hgeom.2.1
  have hG : 0 ≤ G := zero_le_one.trans hgeom.1
  have hX := (actual_admissible_geometry he hsigma).1
  have hXpos : 0 < e.scale := zero_lt_one.trans_le hX
  have hfee : 0 ≤ chartShapeFee T R G := by unfold chartShapeFee; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hhar : 0 ≤ (harmonic N : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic N by unfold harmonic; positivity)
  have hnu (j : ℕ) (m : ℤ × ℤ) :
      (∑ nu ∈ Icc 1 N, actualChartWeightedEnergy e D delta g l Z (j, sign) m
        negative u k upper fj nu) ≤
        A * (1 + lambda e D j) ^ r * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ nu ∈ Icc 1 N, A * (1 + lambda e D j) ^ r / (nu : ℝ) := by
        apply sum_le_sum
        intro nu hnu
        exact henergy (j, sign) m u k nu (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hnu).1)
      _ = _ := by
        simp only [div_eq_mul_inv, ← mul_sum, harmonic_eq_sum_Icc,
          Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hmode (j : ℕ) :
      (∑ m ∈ M, ‖coeff e D Z (j, sign) m‖ *
        ∑ nu ∈ Icc 1 N, actualChartWeightedEnergy e D delta g l Z (j, sign) m
          negative u k upper fj nu) ≤
        (A * (harmonic N : ℝ)) * actualWeightedBlockMass e D Z sign r j := by
    have hc := (coeff_l1_original_five he hkappa b D Z hZ (j, sign)).1
    have hm := hc.sum_le_tsum M (fun m _ => norm_nonneg _)
    have hell : 0 ≤ lambda e D j := mul_nonneg hT.le (Hreal_pos j).le
    have hL : 0 ≤ (1 + lambda e D j) ^ r := Real.rpow_nonneg (by linarith) _
    calc
      _ ≤ ∑ m ∈ M, ‖coeff e D Z (j, sign) m‖ *
          (A * (1 + lambda e D j) ^ r * (harmonic N : ℝ)) :=
        sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (hnu j m) (norm_nonneg _))
      _ = (A * (harmonic N : ℝ)) *
          ((∑ m ∈ M, ‖coeff e D Z (j, sign) m‖) * (1 + lambda e D j) ^ r) := by
        rw [← sum_mul]
        ring
      _ ≤ _ := by
        unfold actualWeightedBlockMass
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hL)
          (mul_nonneg hA hhar)
  have htags := actual_finite_weighted_block_mass_bound he hkappa hD Z hZ sign
    r decay hdecay b hb J
  have hxp : e.scale ^ eta * e.scale ^ (5*kappa) = e.scale ^ (5*kappa+eta) := by
    rw [← Real.rpow_add hXpos]
    congr 1; ring
  calc
    _ ≤ ∑ j ∈ J, (A * (harmonic N : ℝ)) * actualWeightedBlockMass e D Z sign r j :=
      sum_le_sum (fun j _ => hmode j)
    _ = (A * (harmonic N : ℝ)) * ∑ j ∈ J, actualWeightedBlockMass e D Z sign r j :=
      (mul_sum _ _ _).symm
    _ ≤ (A * (harmonic N : ℝ)) *
        ((16 * _root_.P3ActualJointGSourceOnly.fourierCost b * e.scale ^ (5*kappa)) *
          ((base e D) ^ (-decay) / (1 - (2 : ℝ) ^ (-decay)))) :=
      mul_le_mul_of_nonneg_left htags (mul_nonneg hA hhar)
    _ = _ := by
      change (A * (harmonic N : ℝ)) *
        ((16 * _root_.P3ActualJointGSourceOnly.fourierCost b * e.scale ^ (5*kappa)) *
          (T ^ (-decay) / (1 - (2 : ℝ) ^ (-decay)))) = _
      dsimp [A]
      calc
        _ = (16 * K) * _root_.P3ActualJointGSourceOnly.fourierCost b *
            (e.scale ^ eta * e.scale ^ (5*kappa)) * chartShapeFee T R G *
            (T ^ (-decay) / (1 - (2 : ℝ) ^ (-decay))) * (harmonic N : ℝ) := by ring
        _ = _ := by rw [hxp]

end ActualChart

/-- Uniform count constant: eta is fixed BEFORE all atom, scale and chart
variables. The proof uses the genuinely uniform free-epsilon count theorem.
The original local theorem and its by-proof remain unchanged above. -/
theorem actual_chart_energy_count_free_epsilon_uniform {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom)
        (_he : MediumAdmissible B sigma kappa c0 e) (_hsigma : 0 ≤ sigma)
        (Yb Ys : ℝ) (D delta g l : ℕ) (_hD : 0 < D) (_hg : 0 < g)
        (o : OuterIndex) (_ho : o ∈ fixedSlice e Yb Ys D delta g l)
        [NeZero (g*l)] (Z : ℝ) (negative upper : Bool) (fj : ℕ × Bool)
        (_hblock : (actualChartSource e D delta g l Z negative upper fj).Nonempty)
        (tag : ℕ × Bool) (m : ℤ × ℤ) (u : (ZMod (g*l))ˣ)
        (k : ZMod (g*l)) (nu : ℕ), 0 < nu →
      actualChartWeightedEnergy e D delta g l Z tag m negative u k upper fj nu ≤
        C * e.scale ^ eta *
          chartShapeFee (physicalT0 e D)
            (countScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper) (fScale fj.1) *
          (1 + lambda e D tag.1) ^ (3 + eta / 7) / (nu : ℝ) := by
  let p : ℝ := eta / 7
  have hp : 0 < p := by dsimp [p]; positivity
  obtain ⟨K, hK, hcost⟩ := actual_count_cost_product_free_epsilon hp
  refine ⟨576 * K * (13 : ℝ) ^ p, by positivity, ?_⟩
  intro B sigma kappa c0 e he hsigma Yb Ys D delta g l hD hg o ho inst Z negative upper fj hblock tag m u k nu hnu
  let S : ℝ := e.Q2 / ((D/delta : ℕ) : ℝ)
  let R : ℝ := countScale S upper
  let G : ℝ := fScale fj.1
  let H : ℝ := (tagFrequencyBound tag : ℝ)
  let L : ℝ := 1 + lambda e D tag.1
  have hgeom := actual_nonempty_fBlock_count_geometry he hsigma Yb Ys hD hg ho
    upper negative (e.sharedSmoothFrequencyBound Z D) fj hblock
  have hR : 1 ≤ R := hgeom.2.1
  have hG : 1 ≤ G := hgeom.1
  have hT := hgeom.2.2.1
  have hX := (actual_admissible_geometry he hsigma).1
  have hX0 : 0 ≤ e.scale := zero_le_one.trans hX
  have hH : 1 ≤ H := by
    simpa only [H, tagFrequencyBound] using actual_tag_height_ge_one tag
  have hell : 0 ≤ lambda e D tag.1 :=
    mul_nonneg hT.le (Hreal_pos tag.1).le
  have hL : 0 < L := by dsimp [L]; linarith
  have hprod : G * H * R ≤ (13 * e.scale ^ (7 : ℕ)) * L := by
    have hsep := block_product_le_scale_times_decay hT
      (zero_le_one.trans hG) (zero_le_one.trans hR) (Hreal_pos tag.1).le
    have hsep' : G * H * R ≤
        (1 + 2 * G * R / physicalT0 e D) * L := by
      simpa only [H, L, tagFrequencyBound, Nat.cast_mul, Nat.cast_ofNat,
        lambda, Hreal, base, physicalT0] using hsep
    exact hsep'.trans (mul_le_mul_of_nonneg_right hgeom.2.2.2 hL.le)
  have hpower : (G * H * R) ^ p ≤
      (13 : ℝ) ^ p * e.scale ^ eta * L ^ p := by
    have h7p : (7 : ℝ) * p = eta := by dsimp [p]; ring
    calc
      _ ≤ ((13 * e.scale ^ (7 : ℕ)) * L) ^ p :=
        Real.rpow_le_rpow (by positivity) hprod hp.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) hL.le,
          Real.mul_rpow (by norm_num) (pow_nonneg hX0 7),
          ← Real.rpow_natCast_mul hX0 7 p]
        simp only [Nat.cast_ofNat, h7p]
  have hcount :
      (LichtmanSignedDifferenceMultiplicity.divisorMaximum R H G : ℝ) ^ 5 *
          (harmonic (Nat.floor (2 * R)) : ℝ) ≤
        K * (13 : ℝ) ^ p * e.scale ^ eta * L ^ p :=
    (hcost R H G hR hH hG).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpower hK.le)
  have hshape : (1 + H / R) * (H * R) ^ 2 * G ≤
      chartShapeFee (physicalT0 e D) R G * L ^ (3 : ℕ) := by
    have ht := tag_height_physical hT tag
    simpa only [H, ht, L] using shape_bound hT (zero_lt_one.trans_le hR)
      (zero_le_one.trans hG) hell
  have hq := actual_quotient_positive e Yb Ys hD ho
  have hactual := (actual_chart_weighted_576_tag_height he D delta g l Z tag m
    negative u k hq upper fj nu hnu).1
  have hnur : 0 ≤ (nu : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ 576 *
        ((LichtmanSignedDifferenceMultiplicity.divisorMaximum R H G : ℝ) ^ 5 *
          (harmonic (Nat.floor (2 * R)) : ℝ)) *
        ((1 + H / R) * (H * R) ^ 2 * G) / (nu : ℝ) := by
      convert hactual using 1; dsimp [R, S, H, G]; ring
    _ ≤ 576 * (K * (13 : ℝ) ^ p * e.scale ^ eta * L ^ p) *
        (chartShapeFee (physicalT0 e D) R G * L ^ (3 : ℕ)) / (nu : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnur
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hcount (by norm_num)
      · exact hshape
      · positivity
      · positivity
    _ = _ := by
      have hpow := polynomial_rpow (p := p) hL
      dsimp [R, S, G]
      rw [show 3 + eta / 7 = 3 + p by rfl]
      rw [← hpow]
      ring

/-- Uniform full payment: C is chosen from eta alone, before every atom,
scale, geometry, positive decay and Fourier order. The exact original
harmonic, physical reciprocal powers and single five-kappa debit remain. -/
theorem actual_nonzero_chart_count_epsilon_tag_payment_uniform
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom)
        (_he : MediumAdmissible B sigma kappa c0 e) (_hsigma : 0 ≤ sigma)
        (Yb Ys : ℝ) (D delta g l : ℕ) (_hD : 0 < D) (_hg : 0 < g)
        (o : OuterIndex) (_ho : o ∈ fixedSlice e Yb Ys D delta g l)
        [NeZero (g*l)] (Z : ℝ) (negative upper : Bool) (fj : ℕ × Bool)
        (_hblock : (actualChartSource e D delta g l Z negative upper fj).Nonempty)
        (_hkappa : 0 ≤ kappa) (_hZ : 0 < Z) (decay : ℝ) (_hdecay : 0 < decay)
        (b : ℕ) (_hb : 3 + eta / 7 + decay ≤ (b : ℝ))
        (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
        (J : Finset ℕ) (M : Finset (ℤ × ℤ)) (N : ℕ) (sign : Bool),
      (∑ j ∈ J, ∑ m ∈ M, ‖coeff e D Z (j, sign) m‖ *
        ∑ nu ∈ Icc 1 N,
          actualChartWeightedEnergy e D delta g l Z (j, sign) m
            negative u k upper fj nu) ≤
      C * _root_.P3ActualJointGSourceOnly.fourierCost b * e.scale ^ (5*kappa + eta) *
        chartShapeFee (physicalT0 e D)
          (countScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper) (fScale fj.1) *
        ((physicalT0 e D) ^ (-decay) / (1 - (2 : ℝ) ^ (-decay))) *
        (harmonic N : ℝ) := by
  obtain ⟨K, hK, henergyUniform⟩ := actual_chart_energy_count_free_epsilon_uniform heta
  refine ⟨16 * K, by positivity, ?_⟩
  intro B sigma kappa c0 e he hsigma Yb Ys D delta g l hD hg o ho inst Z negative upper fj hblock hkappa hZ decay hdecay b hb u k
  have henergy := henergyUniform B sigma kappa c0 e he hsigma Yb Ys D delta g l
    hD hg o ho Z negative upper fj hblock
  intro J M N sign
  let R : ℝ := countScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper
  let G : ℝ := fScale fj.1
  let T : ℝ := physicalT0 e D
  let r : ℝ := 3 + eta / 7
  let A : ℝ := K * e.scale ^ eta * chartShapeFee T R G
  have hgeom := actual_nonempty_fBlock_count_geometry he hsigma Yb Ys hD hg ho
    upper negative (e.sharedSmoothFrequencyBound Z D) fj hblock
  have hT : 0 < T := hgeom.2.2.1
  have hR : 0 < R := zero_lt_one.trans_le hgeom.2.1
  have hG : 0 ≤ G := zero_le_one.trans hgeom.1
  have hX := (actual_admissible_geometry he hsigma).1
  have hXpos : 0 < e.scale := zero_lt_one.trans_le hX
  have hfee : 0 ≤ chartShapeFee T R G := by unfold chartShapeFee; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hhar : 0 ≤ (harmonic N : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic N by unfold harmonic; positivity)
  have hnu (j : ℕ) (m : ℤ × ℤ) :
      (∑ nu ∈ Icc 1 N, actualChartWeightedEnergy e D delta g l Z (j, sign) m
        negative u k upper fj nu) ≤
        A * (1 + lambda e D j) ^ r * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ nu ∈ Icc 1 N, A * (1 + lambda e D j) ^ r / (nu : ℝ) := by
        apply sum_le_sum
        intro nu hnu
        exact henergy (j, sign) m u k nu (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hnu).1)
      _ = _ := by
        simp only [div_eq_mul_inv, ← mul_sum, harmonic_eq_sum_Icc,
          Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hmode (j : ℕ) :
      (∑ m ∈ M, ‖coeff e D Z (j, sign) m‖ *
        ∑ nu ∈ Icc 1 N, actualChartWeightedEnergy e D delta g l Z (j, sign) m
          negative u k upper fj nu) ≤
        (A * (harmonic N : ℝ)) * actualWeightedBlockMass e D Z sign r j := by
    have hc := (coeff_l1_original_five he hkappa b D Z hZ (j, sign)).1
    have hm := hc.sum_le_tsum M (fun m _ => norm_nonneg _)
    have hell : 0 ≤ lambda e D j := mul_nonneg hT.le (Hreal_pos j).le
    have hL : 0 ≤ (1 + lambda e D j) ^ r := Real.rpow_nonneg (by linarith) _
    calc
      _ ≤ ∑ m ∈ M, ‖coeff e D Z (j, sign) m‖ *
          (A * (1 + lambda e D j) ^ r * (harmonic N : ℝ)) :=
        sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (hnu j m) (norm_nonneg _))
      _ = (A * (harmonic N : ℝ)) *
          ((∑ m ∈ M, ‖coeff e D Z (j, sign) m‖) * (1 + lambda e D j) ^ r) := by
        rw [← sum_mul]
        ring
      _ ≤ _ := by
        unfold actualWeightedBlockMass
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hL)
          (mul_nonneg hA hhar)
  have htags := actual_finite_weighted_block_mass_bound he hkappa hD Z hZ sign
    r decay hdecay b hb J
  have hxp : e.scale ^ eta * e.scale ^ (5*kappa) = e.scale ^ (5*kappa+eta) := by
    rw [← Real.rpow_add hXpos]
    congr 1; ring
  calc
    _ ≤ ∑ j ∈ J, (A * (harmonic N : ℝ)) * actualWeightedBlockMass e D Z sign r j :=
      sum_le_sum (fun j _ => hmode j)
    _ = (A * (harmonic N : ℝ)) * ∑ j ∈ J, actualWeightedBlockMass e D Z sign r j :=
      (mul_sum _ _ _).symm
    _ ≤ (A * (harmonic N : ℝ)) *
        ((16 * _root_.P3ActualJointGSourceOnly.fourierCost b * e.scale ^ (5*kappa)) *
          ((base e D) ^ (-decay) / (1 - (2 : ℝ) ^ (-decay)))) :=
      mul_le_mul_of_nonneg_left htags (mul_nonneg hA hhar)
    _ = _ := by
      change (A * (harmonic N : ℝ)) *
        ((16 * _root_.P3ActualJointGSourceOnly.fourierCost b * e.scale ^ (5*kappa)) *
          (T ^ (-decay) / (1 - (2 : ℝ) ^ (-decay)))) = _
      dsimp [A]
      calc
        _ = (16 * K) * _root_.P3ActualJointGSourceOnly.fourierCost b *
            (e.scale ^ eta * e.scale ^ (5*kappa)) * chartShapeFee T R G *
            (T ^ (-decay) / (1 - (2 : ℝ) ^ (-decay))) * (harmonic N : ℝ) := by ring
        _ = _ := by rw [hxp]

end
end ImbalancedChen.Part3.ActualNonzeroChartEpsilonTagPaymentSourceOnly
