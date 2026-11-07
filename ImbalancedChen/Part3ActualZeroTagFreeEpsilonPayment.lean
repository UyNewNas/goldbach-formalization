import ImbalancedChen.Part3ActualCompletedZeroDifferencePayment
import ImbalancedChen.Part3ActualLogTagBetaRestriction
import ImbalancedChen.Part3ActualFixedFeatureCountGeometry
import ImbalancedChen.Part3ActualModeJointBetaPositiveCount
import ImbalancedChen.Part3PolynomialResidueDivisorBound

/-!
SOURCEONLY / UNCOMPILED separate-module successor of repaired zero-tag525.
Public definitions are imported from their owners. Four zero598 helpers and
two geometry helpers are reached through exact-type owner-file public wrappers.
The original mode norms are existing public positive-count APIs. No declaration
from the unused epsilon186 namespace is needed; its direct divisor API is imported.
All original declaration headers, definitions and bounds remain unchanged.
-/
namespace ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Finset CommonSmoothCutoff
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open ActualM2FinitePoissonAdapterSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly GeneralDRootResidueCostSourceOnly
open GeneralDGateNormalization GeneralDActiveOuterEnergySourceOnly GeneralDActivePairCountSourceOnly
open ActualLogTagHSupportSourceOnly
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators

/-- Exact source identity BEFORE a norm or cardinal bound; arbitrary masks P
include y=0, signed f and nu|y. No comparison between the two caps is used. -/
theorem actual_weighted_source_global_eq_tag (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l))
    (A : ℕ) (a : ℤ) (T : Finset ℕ) (Fset : Finset ℤ) (P : Source → Prop)
    (lambda : ℕ → ℂ) (K : Output → ℂ) :
    (∑ s ∈ (carrier A a T (e.sharedSmoothFrequencyBound Z D) Fset).filter P,
      weight lambda (actualModeOmega e D g l Z tag m negative k) s * K (output s)) =
    ∑ s ∈ (carrier A a T (tagFrequencyBound tag) Fset).filter P,
      weight lambda (actualModeOmega e D g l Z tag m negative k) s * K (output s) := by
  have hfilter (U : Finset Source) :
      (∑ s ∈ U, weight lambda (actualModeOmega e D g l Z tag m negative k) s * K (output s)) =
      ∑ s ∈ U.filter (tagPairSupport e D Z tag),
        weight lambda (actualModeOmega e D g l Z tag m negative k) s * K (output s) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro s _hs
    by_cases hb : tagPairSupport e D Z tag s
    · simp only [if_pos hb]
    · rw [actual_weight_zero_outside_tag_pair e D g l Z tag m negative k lambda s hb]
      simp only [if_neg hb, zero_mul]
  calc
    _ = ∑ s ∈ ((carrier A a T (e.sharedSmoothFrequencyBound Z D) Fset).filter P).filter
        (tagPairSupport e D Z tag),
        weight lambda (actualModeOmega e D g l Z tag m negative k) s * K (output s) := hfilter _
    _ = ∑ s ∈ ((carrier A a T (tagFrequencyBound tag) Fset).filter P).filter
        (tagPairSupport e D Z tag),
        weight lambda (actualModeOmega e D g l Z tag m negative k) s * K (output s) := by
      rw [actual_tag_pair_carrier_filter_eq]
    _ = _ := (hfilter _).symm

/-- On the actual zero-difference carrier every retained nu|y mask is exact.
This does not create a nu-harmonic sum or identify y=0 with Poisson m=0. -/
theorem zeroSource_filter_dvd (U : Finset Source) (nu : ℤ) :
    (zeroSource U).filter (fun s => nu ∣ (output s).2) = zeroSource U := by
  apply filter_eq_self.mpr
  intro s hs
  rw [(mem_filter.mp hs).2]
  exact dvd_zero nu

/-- The SAME original zero piece, full completed-m kernel unchanged. -/
theorem actualZeroPiece_eq_tag (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (M N : ℝ) :
    actualZeroPiece e D delta g l Z tag m negative u k M N =
      zeroPiece (g*l) (signedResidue negative e.residue) (baseCarrier e (D/delta))
        (tagFrequencyBound tag) (actualModeLambda e D delta g l m negative u k)
        (actualModeOmega e D g l Z tag m negative k)
        M N (scaleC e D g l) (scaleF e D g) := by
  unfold actualZeroPiece
  rw [zeroPiece_eq_source, zeroPiece_eq_source]
  have h := actual_weighted_source_global_eq_tag e D g l Z tag m
    negative k (g*l) (signedResidue negative e.residue) (baseCarrier e (D/delta))
    (Icc (Int.ceil (-scaleF e D g)) (Int.floor (scaleF e D g)))
    (fun s => (output s).2 = 0) (actualModeLambda e D delta g l m negative u k)
    (completedKernel M N (scaleC e D g l) (signedResidue negative e.residue))
  refine Eq.trans ?_ (Eq.trans h ?_)
  · apply sum_congr
    · ext s
      simp only [zeroSource, mem_filter]
    · intro s hs
      rfl
  · apply sum_congr
    · ext s
      simp only [zeroSource, mem_filter]
    · intro s hs
      rfl

/-- The real nonpositive-Z boundary uses the owned empty ORIGINAL window.
The pointwise amplitude at Z=0 is not asserted to vanish. -/
theorem actualZeroPiece_eq_zero_of_nonpos
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)] {Z : ℝ} (hZ : Z ≤ 0)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (M N : ℝ) :
    actualZeroPiece e D delta g l Z tag m negative u k M N = 0 := by
  unfold actualZeroPiece
  rw [_root_.P3ActualLogAdapterSourceOnly.frequency_bound_zero_of_nonpos he D hZ,
    zeroPiece_eq_source]
  have hW : poissonNonzeroFrequencyWindow 0 = ∅ := by
    norm_num [poissonNonzeroFrequencyWindow]
  simp only [zeroSource, carrier, rawCarrier, finiteInnerCarrier, hW,
    product_empty, filter_empty, sum_empty]

def actualTagTau (e : MediumAtom) (D delta : ℕ) (tag : ℕ × Bool) : ℕ :=
  tauEnvelope (baseCarrier e (D/delta)) (poissonNonzeroFrequencyWindow (tagFrequencyBound tag))

/-- Linear Htag*Sinner count and the same 9MN positive-kernel bound.
All coefficient norms are supplied by the original gamma/log/root formulas. -/
theorem actualZeroPiece_norm_le_tag
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hdeltaD : delta ∣ D) (hg : 0 < g)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) {M N : ℝ} (hM : 0 < M) (hN : 0 < N) :
    ‖actualZeroPiece e D delta g l Z tag m negative u k M N‖ ≤
      72*M*N*(scaleF e D g)*(tagFrequencyBound tag : ℝ)*
        (e.Q2*(delta : ℝ)/(D : ℝ))*(actualTagTau e D delta tag : ℝ) := by
  have hq : 0 < D/delta := Nat.div_pos (Nat.le_of_dvd hD hdeltaD) hdelta
  have hqR : (0 : ℝ) < (D/delta : ℕ) := by exact_mod_cast hq
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hQ : 0 < e.Q2 := zero_lt_one.trans_le he.2.2.2.1
  have hS : 0 < e.Q2/((D/delta : ℕ) : ℝ) := div_pos hQ hqR
  have hTeq := baseCarrier_eq_factorCarrier_div e hQ.le hq
  have hT : ∀ t ∈ baseCarrier e (D/delta), 0 < t := by
    intro t ht
    rw [hTeq] at ht
    exact zero_factor_pos_small hS ht
  have hTc : ((baseCarrier e (D/delta)).card : ℝ) ≤
      2*(e.Q2/((D/delta : ℕ) : ℝ)) := by rw [hTeq]; exact zero_factor_card_small hS
  have hF : 0 ≤ scaleF e D g := by
    have hU := zero_lt_one.trans_le he.1
    have hQ1 := zero_lt_one.trans_le he.2.2.1
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg
    unfold scaleF
    positivity
  have hfact : ((D/delta : ℕ) : ℝ)*(delta : ℝ) = (D : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hdeltaD
  have hscale : e.Q2/((D/delta : ℕ) : ℝ) = e.Q2*(delta : ℝ)/(D : ℝ) := by
    apply (div_eq_div_iff hqR.ne' hDR.ne').mpr
    calc
      _ = e.Q2 * (((D/delta : ℕ) : ℝ)*(delta : ℝ)) := by rw [hfact]
      _ = _ := by ring
  rw [actualZeroPiece_eq_tag]
  have hp := zeroPiece_norm_le (g*l) (signedResidue negative e.residue)
    (baseCarrier e (D/delta)) (tagFrequencyBound tag)
    (actualModeLambda e D delta g l m negative u k)
    (actualModeOmega e D g l Z tag m negative k) (scaleC e D g l)
    hM hN hS.le hF hT hTc
    (fun t ht => ActualModeBetaPositiveCountSourceOnly.actualModeLambda_norm_le he D delta g l m negative u k ht)
    (fun h _ => ActualModeBetaPositiveCountSourceOnly.actualModeOmega_norm_le e D g l Z tag m negative k h)
  simpa only [hscale, actualTagTau] using hp

/-- The existing SIX pieces, with the same 1512=72*3*7 and no new
six-piece Cauchy charge. Only the exact h cap and its tau envelope change. -/
theorem actualZeroSix_norm_le_tag
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hdeltaD : delta ∣ D)
    (hg : 0 < g) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    ‖actualZeroSix e D delta g l Z tag m negative u k‖ ≤
      1512*(scaleB e delta l)*(scaleC e D g l)*(scaleF e D g)*
        (tagFrequencyBound tag : ℝ)*(e.Q2*(delta : ℝ)/(D : ℝ))*
          (actualTagTau e D delta tag : ℝ) := by
  let Bb := scaleB e delta l
  let Cc := scaleC e D g l
  let R : ℝ := (scaleF e D g)*(tagFrequencyBound tag : ℝ)*
    (e.Q2*(delta : ℝ)/(D : ℝ))*(actualTagTau e D delta tag : ℝ)
  have hU := zero_lt_one.trans_le he.1
  have hQ2 := zero_lt_one.trans_le he.2.2.2.1
  have hQ3 := zero_lt_one.trans_le he.2.2.2.2.1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hdelta
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hBb : 0 < Bb := by dsimp only [Bb, scaleB]; positivity
  have hCc : 0 < Cc := by dsimp only [Cc, scaleC]; positivity
  have hp (M N : ℝ) (hM : 0 < M) (hN : 0 < N) :
      ‖actualZeroPiece e D delta g l Z tag m negative u k M N‖ ≤ 72*M*N*R := by
    have ht := actualZeroPiece_norm_le_tag he D delta g l hD hdelta hdeltaD hg
      Z tag m negative u k hM hN
    simpa only [R, mul_assoc] using ht
  have h1 := hp Bb Cc hBb hCc
  have h2 := hp Bb (2*Cc) hBb (by positivity)
  have h3 := hp Bb (4*Cc) hBb (by positivity)
  have h4 := hp (2*Bb) Cc (by positivity) hCc
  have h5 := hp (2*Bb) (2*Cc) (by positivity) (by positivity)
  have h6 := hp (2*Bb) (4*Cc) (by positivity) (by positivity)
  have hsix := zero_norm_six_le
    (actualZeroPiece e D delta g l Z tag m negative u k Bb Cc)
    (actualZeroPiece e D delta g l Z tag m negative u k Bb (2*Cc))
    (actualZeroPiece e D delta g l Z tag m negative u k Bb (4*Cc))
    (actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) Cc)
    (actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) (2*Cc))
    (actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) (4*Cc))
  have hnorm : ‖actualZeroSix e D delta g l Z tag m negative u k‖ ≤ 1512*Bb*Cc*R := by
    change ‖actualZeroPiece e D delta g l Z tag m negative u k Bb Cc +
      actualZeroPiece e D delta g l Z tag m negative u k Bb (2*Cc) +
      actualZeroPiece e D delta g l Z tag m negative u k Bb (4*Cc) +
      actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) Cc +
      actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) (2*Cc) +
      actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) (4*Cc)‖ ≤ _
    nlinarith [h1,h2,h3,h4,h5,h6,hsix]
  simpa only [Bb, Cc, R, mul_assoc] using hnorm

/-- The SAME literal raw E324, with T0 squared once. The physical tau(D),
ordinary packet-tau, root-residue charges and the Re/2 weights stay distinct. -/
theorem actual_zero_tag_payment_rawE324
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)] (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice d.cleanedAlphaAtom Yb Ys D delta g l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    let e := d.cleanedAlphaAtom
    let Z0 := 1512*(scaleB e delta l)*(scaleC e D g l)*(scaleF e D g)*
      (tagFrequencyBound tag : ℝ)*(e.Q2*(delta : ℝ)/(D : ℝ))*(actualTagTau e D delta tag : ℝ)
    (physicalT0 e D)^2*fixedFirstEnergy e Yb Ys D delta g l*
      (actualZeroSix e D delta g l Z tag m negative u k).re ≤
      (physicalT0 e D)^2*
        (324*(D.divisors.card : ℝ)*d.U^2*d.Q3^2*d.Q2 /
          ((g : ℝ)^2*(l : ℝ)*(delta : ℝ)*(D : ℝ)^2))*Z0 := by
  dsimp only
  let e := d.cleanedAlphaAtom
  let Z0 := 1512*(scaleB e delta l)*(scaleC e D g l)*(scaleF e D g)*
    (tagFrequencyBound tag : ℝ)*(e.Q2*(delta : ℝ)/(D : ℝ))*(actualTagTau e D delta tag : ℝ)
  have hdeq : o.2.1.1.gcd D = delta := (mem_filter.mp ho).2.2.1
  have hdpos : 0 < delta := by
    rw [← hdeq, Nat.gcd_comm]
    exact Nat.gcd_pos_of_pos_left _ hD
  have hdiv : delta ∣ D := by rw [← hdeq]; exact Nat.gcd_dvd_right _ _
  have h0 : ‖actualZeroSix e D delta g l Z tag m negative u k‖ ≤ Z0 :=
    actualZeroSix_norm_le_tag (mediumAdmissible_cleanedAlphaAtom hd)
      D delta g l hD hdpos hdiv hg hl Z tag m negative u k
  have hZ0 : 0 ≤ Z0 := (norm_nonneg _).trans h0
  have hre : (actualZeroSix e D delta g l Z tag m negative u k).re ≤ Z0 :=
    (Complex.re_le_norm _).trans h0
  have hE := GeneralDPhysicalTailCountSourceOnly.actual_fixedFirstEnergy_le_324
    hd Yb Ys hD hdpos hg hl
  have hE0 : 0 ≤ fixedFirstEnergy e Yb Ys D delta g l := by
    unfold fixedFirstEnergy
    exact sum_nonneg (fun o _ => sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left hre (mul_nonneg (sq_nonneg _) hE0)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (sq_nonneg _)) hZ0)

private theorem frequency_natAbs_cap (H : ℕ) {h : ℤ}
    (hh : h ∈ poissonNonzeroFrequencyWindow H) : h.natAbs ≤ H := by
  rcases mem_union.mp hh with hh | hh
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
    simpa only [Int.natAbs_natCast] using (mem_Icc.mp hn).2
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using (mem_Icc.mp hn).2

private theorem tag_height_eq_lambda (e : MediumAtom) (D : ℕ) (tag : ℕ × Bool)
    (hT : 0 < physicalT0 e D) :
    (tagFrequencyBound tag : ℝ) =
      2 * _root_.P3ActualLogAdapterSourceOnly.lambda e D tag.1 * (1/physicalT0 e D) := by
  simp only [tagFrequencyBound, Nat.cast_mul, Nat.cast_ofNat]
  change 2*(_root_.P3ActualLogAdapterSourceOnly.Hnat tag.1 : ℝ) =
    2*(physicalT0 e D*(_root_.P3ActualLogAdapterSourceOnly.Hnat tag.1 : ℝ))*(1/physicalT0 e D)
  field_simp [hT.ne']

/-- A genuine selectable-epsilon bound on the actual zero-collision divisor
maximum. Constants precede sigma, kappa, the atom, features, Z and the tag.
No harmonic/divisibility cost from nonzero y is charged on this zero branch. -/
theorem actual_tag_tau_free_epsilon {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom),
      MediumAdmissible B sigma kappa c0 e → 0 ≤ sigma →
      ∀ (Yb Ys : ℝ) (D delta g l : ℕ), 0 < D →
        (fixedSlice e Yb Ys D delta g l).Nonempty → ∀ tag : ℕ × Bool,
      (actualTagTau e D delta tag : ℝ) ≤
        C*e.scale^eta*(1+_root_.P3ActualLogAdapterSourceOnly.lambda e D tag.1)^(eta/6) := by
  obtain ⟨K, hK, htau⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (show 0 < eta/6 by positivity)
  refine ⟨K*(4 : ℝ)^(eta/6), by positivity, ?_⟩
  intro B sigma kappa c0 e he hsigma Yb Ys D delta g l hD hfixed tag
  obtain ⟨o, ho⟩ := hfixed
  have hx := ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry he hsigma
  have hT := ActualFixedFeatureCountGeometrySourceOnly.actual_physicalT0_positive_and_inv_bound
    he hsigma hD
  have hq := ActualFixedFeatureCountGeometrySourceOnly.actual_quotient_positive e Yb Ys hD ho
  have hq1 : (1 : ℝ) ≤ (D/delta : ℕ) := by exact_mod_cast hq
  have hx0 : 0 ≤ e.scale := zero_le_one.trans hx.1
  let L := _root_.P3ActualLogAdapterSourceOnly.lambda e D tag.1
  have hL : 0 < L := by
    change 0 < physicalT0 e D * _root_.P3ActualLogAdapterSourceOnly.Hreal tag.1
    exact mul_pos hT.1 (_root_.P3ActualLogAdapterSourceOnly.Hreal_pos tag.1)
  have hH : (tagFrequencyBound tag : ℝ) ≤ 2*L*e.scale^5 := by
    rw [tag_height_eq_lambda e D tag hT.1]
    exact mul_le_mul_of_nonneg_left hT.2 (by positivity)
  let T := baseCarrier e (D/delta)
  let W := poissonNonzeroFrequencyWindow (tagFrequencyBound tag)
  have hpoint (ht : ℤ × ℕ) (hht : ht ∈ W ×ˢ T) :
      ((ht.1.natAbs*ht.2).divisors.card : ℝ) ≤
        (K*(4 : ℝ)^(eta/6))*e.scale^eta*(1+L)^(eta/6) := by
    obtain ⟨hh, htmem⟩ := mem_product.mp hht
    have hhs : ht.1 ≠ 0 := zero_frequency_nonzero (tagFrequencyBound tag) hh
    have hs := baseCarrier_window e (D/delta) htmem
    have hqt := factorCarrier_bounds he.2.2.2.1 hs
    have htpos : 0 < ht.2 := by
      by_contra hn
      have hz : ht.2 = 0 := Nat.eq_zero_of_not_pos hn
      simpa only [hz, Nat.mul_zero, lt_self_iff_false] using hqt.1
    have htx : (ht.2 : ℝ) ≤ 2*e.scale := by
      calc
        _ ≤ ((D/delta*ht.2 : ℕ) : ℝ) := by
          simpa only [Nat.cast_mul, one_mul] using
            mul_le_mul_of_nonneg_right hq1 (Nat.cast_nonneg ht.2)
        _ ≤ 2*e.Q2 := hqt.2.2
        _ ≤ _ := mul_le_mul_of_nonneg_left hx.2.2.2.1 (by norm_num)
    have hhcap : (ht.1.natAbs : ℝ) ≤ (tagFrequencyBound tag : ℝ) := by
      exact_mod_cast frequency_natAbs_cap (tagFrequencyBound tag) hh
    have hn : 0 < ht.1.natAbs*ht.2 := mul_pos (Int.natAbs_pos.mpr hhs) htpos
    have hncap : ((ht.1.natAbs*ht.2 : ℕ) : ℝ) ≤ 4*e.scale^6*(1+L) := by
      calc
        _ = (ht.1.natAbs : ℝ)*(ht.2 : ℝ) := by simp only [Nat.cast_mul]
        _ ≤ (tagFrequencyBound tag : ℝ)*(2*e.scale) :=
          mul_le_mul hhcap htx (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ ≤ (2*L*e.scale^5)*(2*e.scale) :=
          mul_le_mul_of_nonneg_right hH (by positivity)
        _ = 4*e.scale^6*L := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith : L ≤ 1+L) (by positivity)
    have hp : (e.scale^6)^(eta/6) = e.scale^eta := by
      rw [← Real.rpow_natCast_mul hx0]
      congr 1
      ring
    calc
      _ ≤ K*((ht.1.natAbs*ht.2 : ℕ) : ℝ)^(eta/6) := by
        simpa only [fouvryTau_two] using htau _ hn
      _ ≤ K*(4*e.scale^6*(1+L))^(eta/6) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hncap (by positivity)) hK.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by norm_num) (by positivity), hp]
        ring
  change (((W ×ˢ T).sup (fun ht : ℤ × ℕ => (ht.1.natAbs*ht.2).divisors.card) : ℕ) : ℝ) ≤ _
  by_cases hn : (W ×ˢ T).Nonempty
  · obtain ⟨ht, hht, heq⟩ := exists_mem_eq_sup _ hn
      (fun ht : ℤ × ℕ => (ht.1.natAbs*ht.2).divisors.card)
    rw [heq]
    exact hpoint ht hht
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [hempty, sup_empty]
    rw [Nat.bot_eq_zero, Nat.cast_zero]
    positivity

/-- The positive lambda factor prevents a low-block logarithm. This is
an exact finite dyadic bound, uniform even when T0 is very small. -/
theorem finite_tag_height_decay_sum (e : MediumAtom) (D : ℕ)
    (hT : 0 < physicalT0 e D) (negative : Bool) (J : ℕ) :
    (∑ j ∈ range J, (tagFrequencyBound (j,negative) : ℝ) /
      (1+_root_.P3ActualLogAdapterSourceOnly.lambda e D j)^2) ≤ 4/physicalT0 e D := by
  let L := fun j => _root_.P3ActualLogAdapterSourceOnly.lambda e D j
  have hL (j : ℕ) : 0 ≤ L j := by
    change 0 ≤ physicalT0 e D*_root_.P3ActualLogAdapterSourceOnly.Hreal j
    exact mul_nonneg hT.le (_root_.P3ActualLogAdapterSourceOnly.Hreal_pos j).le
  have hsucc (j : ℕ) : L (j+1) = 2*L j := by
    dsimp [L, _root_.P3ActualLogAdapterSourceOnly.lambda,
      _root_.P3ActualLogAdapterSourceOnly.Hreal, _root_.P3ActualLogAdapterSourceOnly.Hnat]
    rw [pow_succ]
    push_cast
    ring
  let q := fun j => 1/(1+L j)
  have htel (n : ℕ) : (∑ j ∈ range n, (q j-q (j+1))) = q 0-q n := by
    induction n with
    | zero => simp only [sum_empty, range_zero, sub_self]
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have hp (j : ℕ) : L j/(1+L j)^2 ≤ 2*(q j-q (j+1)) := by
    have hj0 := hL j
    have heq : 2*(1/(1+L j)-1/(1+2*L j))-L j/(1+L j)^2 =
        L j/((1+L j)^2*(1+2*L j)) := by
      field_simp [show 1+L j ≠ 0 by positivity, show 1+2*L j ≠ 0 by positivity]
      ring
    have hn : 0 ≤ L j/((1+L j)^2*(1+2*L j)) := by positivity
    change L j/(1+L j)^2 ≤ 2*(1/(1+L j)-1/(1+L (j+1)))
    rw [hsucc]
    linarith
  have hL0 := hL 0
  have hLJ := hL J
  have hq0 : q 0 ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 1+L 0)).mpr
    linarith [hL 0]
  have hqJ : 0 ≤ q J := by dsimp [q]; positivity
  calc
    _ = (2/physicalT0 e D)*(∑ j ∈ range J, L j/(1+L j)^2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _hj
      rw [tag_height_eq_lambda e D (j,negative) hT]
      dsimp only [L]
      ring
    _ ≤ (2/physicalT0 e D)*(∑ j ∈ range J, 2*(q j-q (j+1))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun j _ => hp j)) (by positivity)
    _ = (4/physicalT0 e D)*(q 0-q J) := by rw [← mul_sum, htel]; ring
    _ ≤ 4/physicalT0 e D := by
      have hc : 0 ≤ 4/physicalT0 e D := by positivity
      nlinarith

/-- The actual linear Htag*tau0 cost, after a freely chosen Schwartz
order, is uniform in all finite tag ranges and in the all-Z auxiliary cap.
This is a proved scalar supplier, not a zero-budget or spectral premise. -/
theorem actual_linear_tag_tau_free_epsilon {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom),
      MediumAdmissible B sigma kappa c0 e → 0 ≤ sigma →
      ∀ (Yb Ys : ℝ) (D delta g l : ℕ), 0 < D →
        (fixedSlice e Yb Ys D delta g l).Nonempty →
      ∀ (b J : ℕ), eta/6+2 ≤ (b : ℝ) → ∀ negative : Bool,
      (∑ j ∈ range J,
        (tagFrequencyBound (j,negative) : ℝ)*(actualTagTau e D delta (j,negative) : ℝ) /
          (1+_root_.P3ActualLogAdapterSourceOnly.lambda e D j)^b) ≤
        C*e.scale^eta/physicalT0 e D := by
  obtain ⟨K, hK, htau⟩ := actual_tag_tau_free_epsilon heta
  refine ⟨4*K, by positivity, ?_⟩
  intro B sigma kappa c0 e he hsigma Yb Ys D delta g l hD hfixed b J hb negative
  have hT := (ActualFixedFeatureCountGeometrySourceOnly.actual_physicalT0_positive_and_inv_bound
    he hsigma hD).1
  have hKscale : 0 ≤ K*e.scale^eta := mul_nonneg hK.le
    (Real.rpow_nonneg
      (zero_le_one.trans (ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry he hsigma).1) eta)
  have hpoint (j : ℕ) :
      (tagFrequencyBound (j,negative) : ℝ)*(actualTagTau e D delta (j,negative) : ℝ) /
        (1+_root_.P3ActualLogAdapterSourceOnly.lambda e D j)^b ≤
      (K*e.scale^eta)*(tagFrequencyBound (j,negative) : ℝ) /
        (1+_root_.P3ActualLogAdapterSourceOnly.lambda e D j)^2 := by
    let L := _root_.P3ActualLogAdapterSourceOnly.lambda e D j
    have hL : 0 ≤ L := by
      change 0 ≤ physicalT0 e D*_root_.P3ActualLogAdapterSourceOnly.Hreal j
      exact mul_nonneg hT.le (_root_.P3ActualLogAdapterSourceOnly.Hreal_pos j).le
    have hbase : 1 ≤ 1+L := by linarith
    have hp : (1+L)^(eta/6)*(1+L)^2 ≤ (1+L)^b := by
      calc
        _ = (1+L)^(eta/6+2) := by
          rw [Real.rpow_add (by positivity), Real.rpow_two]
        _ ≤ (1+L)^(b : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase hb
        _ = _ := Real.rpow_natCast _ _
    have ht := htau B sigma kappa c0 e he hsigma Yb Ys D delta g l hD hfixed (j,negative)
    apply (div_le_div_iff₀ (by positivity : 0 < (1+L)^b)
      (by positivity : 0 < (1+L)^2)).mpr
    calc
      _ ≤ (tagFrequencyBound (j,negative) : ℝ)*
          (K*e.scale^eta*(1+L)^(eta/6))*(1+L)^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)) (by positivity)
      _ = (K*e.scale^eta*(tagFrequencyBound (j,negative) : ℝ))*
          ((1+L)^(eta/6)*(1+L)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hKscale (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ j ∈ range J, (K*e.scale^eta)*(tagFrequencyBound (j,negative) : ℝ) /
        (1+_root_.P3ActualLogAdapterSourceOnly.lambda e D j)^2 := sum_le_sum (fun j _ => hpoint j)
    _ = (K*e.scale^eta)*(∑ j ∈ range J, (tagFrequencyBound (j,negative) : ℝ) /
        (1+_root_.P3ActualLogAdapterSourceOnly.lambda e D j)^2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _hj
      ring
    _ ≤ (K*e.scale^eta)*(4/physicalT0 e D) :=
      mul_le_mul_of_nonneg_left (finite_tag_height_decay_sum e D hT negative J) hKscale
    _ = _ := by ring

/-- Direct use of the owned actual coefficient norm. The SAME single
five-kappa family supplies the denominator order; no extra amplitude
assumption, global-Z cutoff or second Fourier charge is introduced. -/
theorem actual_coeff_tag_tau_free_epsilon {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom),
      MediumAdmissible B sigma kappa c0 e → 0 ≤ sigma → 0 ≤ kappa →
      ∀ (Yb Ys : ℝ) (D delta g l : ℕ), 0 < D →
        (fixedSlice e Yb Ys D delta g l).Nonempty →
      ∀ (Z : ℝ), 0 < Z → ∀ (b J : ℕ), eta/6+2 ≤ (b : ℝ) → ∀ negative : Bool,
      (∑ j ∈ range J,
        (∑' m : ℤ × ℤ, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z (j,negative) m‖)*
          (tagFrequencyBound (j,negative) : ℝ)*(actualTagTau e D delta (j,negative) : ℝ)) ≤
        C*_root_.P3ActualJointGSourceOnly.fourierCost b*
          e.scale^(5*kappa+eta)/physicalT0 e D := by
  obtain ⟨K, hK, hcost⟩ := actual_linear_tag_tau_free_epsilon heta
  refine ⟨16*K, by positivity, ?_⟩
  intro B sigma kappa c0 e he hsigma hkappa Yb Ys D delta g l hD hfixed Z hZ b J hb negative
  have hx := ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry he hsigma
  have hxpos : 0 < e.scale := zero_lt_one.trans_le hx.1
  let A := 16*_root_.P3ActualJointGSourceOnly.fourierCost b*e.scale^(5*kappa)
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (by norm_num) (_root_.P3ActualJointGSourceOnly.fourierCost_nonneg b))
    (Real.rpow_nonneg hxpos.le (5*kappa))
  have hpoint (j : ℕ) :
      (∑' m : ℤ × ℤ, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z (j,negative) m‖)*
          (tagFrequencyBound (j,negative) : ℝ)*(actualTagTau e D delta (j,negative) : ℝ) ≤
        A*((tagFrequencyBound (j,negative) : ℝ)*(actualTagTau e D delta (j,negative) : ℝ)/
          (1+_root_.P3ActualLogAdapterSourceOnly.lambda e D j)^b) := by
    have hc := (_root_.P3ActualLogAdapterSourceOnly.coeff_l1_original_five
      he hkappa b D Z hZ (j,negative)).2
    calc
      _ ≤ (A/(1+_root_.P3ActualLogAdapterSourceOnly.lambda e D j)^b)*
          (tagFrequencyBound (j,negative) : ℝ)*(actualTagTau e D delta (j,negative) : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑ j ∈ range J, A*((tagFrequencyBound (j,negative) : ℝ)*
        (actualTagTau e D delta (j,negative) : ℝ)/
          (1+_root_.P3ActualLogAdapterSourceOnly.lambda e D j)^b) :=
      sum_le_sum (fun j _ => hpoint j)
    _ = A*(∑ j ∈ range J, (tagFrequencyBound (j,negative) : ℝ)*
        (actualTagTau e D delta (j,negative) : ℝ)/
          (1+_root_.P3ActualLogAdapterSourceOnly.lambda e D j)^b) := (mul_sum _ _ _).symm
    _ ≤ A*(K*e.scale^eta/physicalT0 e D) :=
      mul_le_mul_of_nonneg_left
        (hcost B sigma kappa c0 e he hsigma Yb Ys D delta g l hD hfixed b J hb negative) hA
    _ = _ := by
      rw [Real.rpow_add hxpos]
      dsimp only [A]
      ring

/-- A concrete genuine sigma debit. sigma/100 is inside the original
aggregate selectable sigma/10 account; kappa=0 is explicitly permitted. -/
theorem actual_coeff_tag_tau_sigma_budget {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (e : MediumAtom),
      MediumAdmissible B sigma kappa c0 e → 0 ≤ kappa →
      ∀ (Yb Ys : ℝ) (D delta g l : ℕ), 0 < D →
        (fixedSlice e Yb Ys D delta g l).Nonempty →
      ∀ (Z : ℝ), 0 < Z → ∀ (b J : ℕ), sigma/600+2 ≤ (b : ℝ) → ∀ negative : Bool,
      (∑ j ∈ range J,
        (∑' m : ℤ × ℤ, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z (j,negative) m‖)*
          (tagFrequencyBound (j,negative) : ℝ)*(actualTagTau e D delta (j,negative) : ℝ)) ≤
        C*_root_.P3ActualJointGSourceOnly.fourierCost b*
          e.scale^(5*kappa+sigma/100)/physicalT0 e D := by
  obtain ⟨C, hC, hc⟩ := actual_coeff_tag_tau_free_epsilon (show 0 < sigma/100 by positivity)
  refine ⟨C, hC, ?_⟩
  intro B kappa c0 e he hkappa Yb Ys D delta g l hD hfixed Z hZ b J hb negative
  apply hc B sigma kappa c0 e he hsigma.le hkappa Yb Ys D delta g l hD hfixed Z hZ b J
    (by convert hb using 1; ring) negative

end
end ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly
