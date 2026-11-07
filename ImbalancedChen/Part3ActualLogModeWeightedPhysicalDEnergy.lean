import ImbalancedChen.Part3ActualModeJointBetaPositiveCount
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import ImbalancedChen.Part3ActualPositiveLatticeSmoothCover
import ImbalancedChen.Part3ActualSeparatedRowLogModeSupplier
import ImbalancedChen.Part3ActualM2FinitePoissonAdapter
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED. ONE complete minimal physical-D energy and finite
log-mode Cauchy module candidate. All imports above are genuine current files.
No proposed P4/P5 import or old large failed prefix is copied.
From frozen16add only the finite ordinary tau maximum, positive row-square
mass and literal mode-Co energy bridge are retained. Actual M1 supplies the
proved E324 and packet representation bounds; actual P1 supplies exact six
smooth masses. Frozen511 supplies the physical T0 normalization and actual
mode scalar/HasSum. The independently reviewed211 finite weighted Cauchy is
included after those local declarations, using the REAL two-log coefficient.
Original namespaces are retained for downstream thin-epsilon compatibility.
The whole module is still uncompiled; ROOT alone owns actual installation.
-/

namespace ImbalancedChen.Part3.ActualPacketBCFCardEnergySourceOnly
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Complex Finset CommonSmoothCutoff GeneralDGateNormalization
open GeneralDActivePairCountSourceOnly GeneralDActiveOuterEnergySourceOnly
open GeneralDPhysicalTailCountSourceOnly ActualFixedFeaturePacketPushforwardSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly
open scoped BigOperators

def ordinaryTau (A : ℕ) (k : Packet) : ℕ := (k.1.1 / A).divisors.card * k.1.2.divisors.card ^ 2
def ordinaryTauMax (A : ℕ) (L : Finset Packet) : ℕ := L.sup (ordinaryTau A)

/-- Explicit tau(D), before any optional subpower bound on the other factors. -/
theorem tauEnvelope_le_D_times_ordinary (A D : ℕ) (L : Finset Packet) :
    tauEnvelope A D L ≤ D.divisors.card * ordinaryTauMax A L := by
  apply Finset.sup_le
  intro k hk
  calc
    packetTau A D k = D.divisors.card * ordinaryTau A k := by
      unfold packetTau ordinaryTau
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (le_sup hk)

lemma smoothMass_nonneg (M N : ℝ) (L : Finset Packet) (J : Packet → ℂ) :
    0 ≤ smoothMass M N L J := by
  exact sum_nonneg (fun k hk => mul_nonneg
    (mul_nonneg (scaledDyadicCutoff_nonneg _ _) (scaledDyadicCutoff_nonneg _ _)) (sq_nonneg _))

lemma sixSmoothMass_nonneg (B C : ℝ) (L : Finset Packet) (J : Packet → ℂ) :
    0 ≤ sixSmoothMass B C L J := by
  unfold sixSmoothMass
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (smoothMass_nonneg _ _ _ _) (smoothMass_nonneg _ _ _ _)) (smoothMass_nonneg _ _ _ _))
    (smoothMass_nonneg _ _ _ _)) (smoothMass_nonneg _ _ _ _)) (smoothMass_nonneg _ _ _ _)

/-- One representation fee remains in the ROW square pushforward. -/
theorem actual_packet_square_mass_le_six (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (J : Packet → ℂ) :
    let B := scaleB e delta l
    let C := scaleC e D g l
    let F := scaleF e D g
    let L := packetBox B C F
    (∑ o ∈ fixedSlice e Yb Ys D delta g l, ‖J (packetKey D delta g l o)‖ ^ 2) ≤
      (tauEnvelope (g*l) D L : ℝ) * sixSmoothMass B C L J := by
  dsimp only
  have hp := actual_positive_mass_smooth_mu e hN hQ hR hS Yb Ys (delta := delta) hD hg hl J
  apply hp.trans
  calc
    _ ≤ ∑ k ∈ packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g),
        (tauEnvelope (g*l) D (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ) *
          (packetWeight (scaleB e delta l) (scaleC e D g l) k * ‖J k‖ ^ 2) := by
      apply sum_le_sum
      intro k hk
      have hmu := packetFiber_card_le_tau e hN hQ hR hS Yb Ys (delta := delta) hD hg hl k
      have hmax : packetTau (g*l) D k ≤
          tauEnvelope (g*l) D (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) := le_sup hk
      have hmuR : ((packetFiber e Yb Ys D delta g l k).card : ℝ) ≤
          (tauEnvelope (g*l) D (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ) := by
        exact_mod_cast hmu.trans hmax
      have hweight : 0 ≤
          packetWeight (scaleB e delta l) (scaleC e D g l) k * ‖J k‖ ^ 2 :=
        mul_nonneg (packetWeight_nonneg (scaleB e delta l) (scaleC e D g l) k)
          (sq_nonneg ‖J k‖)
      have ht := mul_le_mul_of_nonneg_right
        (a := packetWeight (scaleB e delta l) (scaleC e D g l) k * ‖J k‖ ^ 2) hmuR hweight
      simpa only [mul_left_comm] using ht
    _ = _ := by rw [← mul_sum, cover_mass_eq_six]

def orient (negative : Bool) (z : ℂ) : ℂ := if negative then (starRingEnd ℂ) z else z
lemma norm_orient (negative : Bool) (z : ℂ) : ‖orient negative z‖ = ‖z‖ := by
  cases negative <;> simp [orient]

def modeAlpha (e : MediumAtom) (o : OuterIndex) (k : ℤ × ℤ) : ℂ :=
  P3ActualLogAdapterSourceOnly.outerMultiplier e o.1.2.1 o.1.1 o.2.1.1
    (o.2.1.2.1 * o.2.1.2.2) k
def modeCo (e : MediumAtom) (Yb Ys : ℝ) (k : ℤ × ℤ) (negative : Bool)
    (rootSlice : Finset OuterIndex) (o : OuterIndex) : ℂ :=
  if o ∈ rootSlice then e.smallCoreSquaredOuterCoefficient Yb Ys o * orient negative (modeAlpha e o k)
  else 0
def modeFirstEnergy (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ)
    (k : ℤ × ℤ) (negative : Bool) (rootSlice : Finset OuterIndex) : ℝ :=
  ∑ o ∈ fixedSlice e Yb Ys D delta g l, ‖modeCo e Yb Ys k negative rootSlice o‖ ^ 2

lemma modeAlpha_norm_le (e : MediumAtom)
    (_hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) (D delta g l : ℕ) {o : OuterIndex}
    (ho : o ∈ fixedSlice e Yb Ys D delta g l) (k : ℤ × ℤ) : ‖modeAlpha e o k‖ ≤ 1 := by
  have hf := fixedSlice_facts e Yb Ys D delta g l ho
  have hp := P3ActualLogAdapterSourceOnly.factor_ratio hQ (mem_filter.mp hf.1).1
  have hr := P3ActualLogAdapterSourceOnly.factor_ratio hR hf.2.2.2.1
  have hrp := P3ActualLogAdapterSourceOnly.factor_ratio hR hf.2.2.2.2.1
  have hsp := P3ActualLogAdapterSourceOnly.factor_ratio hS hf.2.2.2.2.2.1
  change P3ActualLogAdapterSourceOnly.P e o.1.1 ∈ Set.Icc 1 2 at hp
  change P3ActualLogAdapterSourceOnly.Rr e o.2.1.1 ∈ Set.Icc 1 2 at hr
  have hw : P3ActualLogAdapterSourceOnly.Ww e (o.2.1.2.1 * o.2.1.2.2) ∈ Set.Icc (1 : ℝ) 4 := by
    have hwEq : P3ActualLogAdapterSourceOnly.Ww e (o.2.1.2.1 * o.2.1.2.2) =
        ((o.2.1.2.1 : ℝ) / e.Q3) * ((o.2.1.2.2 : ℝ) / e.Q2) := by
      simp only [P3ActualLogAdapterSourceOnly.Ww, Nat.cast_mul, div_mul_div_comm]
    rw [hwEq]
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      P3ActualLogAdapterSourceOnly.interval_mul hrp hsp
  have hpr := P3ActualLogAdapterSourceOnly.interval_mul hp hr
  have hout := P3ActualLogAdapterSourceOnly.interval_mul hpr hw
  have hout0 : 0 < P3ActualLogAdapterSourceOnly.P e o.1.1 *
      P3ActualLogAdapterSourceOnly.Rr e o.2.1.1 *
      P3ActualLogAdapterSourceOnly.Ww e (o.2.1.2.1 * o.2.1.2.2) := zero_lt_one.trans_le hout.1
  have hinv : (P3ActualLogAdapterSourceOnly.P e o.1.1 *
      P3ActualLogAdapterSourceOnly.Rr e o.2.1.1 *
      P3ActualLogAdapterSourceOnly.Ww e (o.2.1.2.1 * o.2.1.2.2))⁻¹ ≤ (1 : ℝ) := by
    simpa only [one_div] using (div_le_one hout0).mpr hout.1
  simpa only [modeAlpha, P3ActualLogAdapterSourceOnly.outerMultiplier, norm_mul,
    P3ActualLogAdapterSourceOnly.norm_outerPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hout0.le)] using hinv

theorem modeFirstEnergy_le_original (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) (D delta g l : ℕ) (k : ℤ × ℤ) (negative : Bool)
    (rootSlice : Finset OuterIndex) :
    modeFirstEnergy e Yb Ys D delta g l k negative rootSlice ≤
      fixedFirstEnergy e Yb Ys D delta g l := by
  unfold modeFirstEnergy fixedFirstEnergy
  apply sum_le_sum
  intro o ho
  have hn : ‖modeCo e Yb Ys k negative rootSlice o‖ ≤
      ‖e.smallCoreSquaredOuterCoefficient Yb Ys o‖ := by
    unfold modeCo
    split_ifs
    · rw [norm_mul, norm_orient]
      exact (mul_le_mul_of_nonneg_left
        (modeAlpha_norm_le e hN hQ hR hS Yb Ys D delta g l ho k) (norm_nonneg _)).trans_eq (by ring)
    · simpa only [norm_zero] using norm_nonneg (e.smallCoreSquaredOuterCoefficient Yb Ys o)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn

def rootSelector (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ)
    (u : (ZMod (g*l))ˣ) : Finset OuterIndex :=
  (fixedSlice e Yb Ys D delta g l).filter
    (fun o => ActualSeparatedRowPacketMatchSourceOnly.rootFeature D delta g l o = u)

def literalModeCo (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ)
    (k : ℤ × ℤ) (negative : Bool) (u : (ZMod (g*l))ˣ) (o : OuterIndex) : ℂ :=
  if ActualSeparatedRowPacketMatchSourceOnly.rootFeature D delta g l o = u then
    e.smallCoreSquaredOuterCoefficient Yb Ys o *
      ActualLogModePacketInstanceSourceOnly.modeAlpha e k negative o else 0

theorem modeCo_eq_literalModeCo (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ)
    (k : ℤ × ℤ) (negative : Bool) (u : (ZMod (g*l))ˣ) {o : OuterIndex}
    (ho : o ∈ fixedSlice e Yb Ys D delta g l) :
    modeCo e Yb Ys k negative (rootSelector e Yb Ys D delta g l u) o =
      literalModeCo e Yb Ys D delta g l k negative u o := by
  simp only [modeCo, rootSelector, mem_filter, ho, true_and, literalModeCo,
    modeAlpha, orient, ActualLogModePacketInstanceSourceOnly.modeAlpha,
    ActualSeparatedRowPacketMatchSourceOnly.branch]

end
end ImbalancedChen.Part3.ActualPacketBCFCardEnergySourceOnly

namespace ImbalancedChen.Part3.ActualModePhysicalDPrefactorSourceOnly
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Finset GeneralDGateNormalization
open GeneralDActivePairCountSourceOnly GeneralDActiveOuterEnergySourceOnly
open GeneralDPhysicalTailCountSourceOnly ActualFixedFeaturePacketPushforwardSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly ActualPacketBCFCardEnergySourceOnly
open ActualSeparatedRowPacketMatchSourceOnly
open scoped BigOperators

def energy324 (d : MediumAtom) (D delta g l : ℕ) : ℝ :=
  324 * (D.divisors.card : ℝ) * d.U ^ 2 * d.Q3 ^ 2 * d.Q2 /
    ((g : ℝ) ^ 2 * (l : ℝ) * (delta : ℝ) * (D : ℝ) ^ 2)

/-- This is already the SQUARED scalar prefactor, after T0 and the row's
one packet representation fee. It contains the full physical tau(D)^2. -/
def normalizedPacketEnergy324 (d : MediumAtom) (D delta g l : ℕ) : ℝ :=
  324 * (D.divisors.card : ℝ) ^ 2 * d.U ^ 2 * d.V ^ 2 /
    (d.Q1 ^ 2 * d.Q3 ^ 2 * d.Q2 ^ 3 * (g : ℝ) ^ 2 * (l : ℝ) * (delta : ℝ))

def packetPrefactor (d : MediumAtom) (D delta g l : ℕ) : ℝ :=
  18 * (D.divisors.card : ℝ) * d.U * d.V /
    (d.Q1 * d.Q3 * d.Q2 * (g : ℝ) * Real.sqrt (d.Q2 * (l : ℝ) * (delta : ℝ)))

/-- Membership supplies exactly the divisor fibre used by the old D ledger.
In particular hdelta>0 in the numerical interfaces is not a new support gate. -/
theorem actual_delta_mem_divisors (e : MediumAtom) (Yb Ys : ℝ)
    {D delta g l : ℕ} (hD : 0 < D) {o : OuterIndex}
    (ho : o ∈ fixedSlice e Yb Ys D delta g l) : delta ∈ D.divisors := by
  have hd := (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.2.2.2.2.2.1
  apply Nat.mem_divisors.mpr
  refine ⟨?_, hD.ne'⟩
  rw [← hd]
  exact Nat.gcd_dvd_right o.2.1.1 D

/-- Exact actual Co energy before any BCF/cardinality enlargement. -/
theorem literalModeCo_energy_le_original (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) (D delta g l : ℕ) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) :
    (∑ o ∈ fixedSlice e Yb Ys D delta g l,
      ‖literalModeCo e Yb Ys D delta g l m negative u o‖ ^ 2) ≤
        fixedFirstEnergy e Yb Ys D delta g l := by
  have hc := modeFirstEnergy_le_original e hN hQ hR hS Yb Ys D delta g l m negative
    (rootSelector e Yb Ys D delta g l u)
  unfold modeFirstEnergy at hc
  convert! hc using 1
  apply sum_congr rfl
  intro o ho
  rw [modeCo_eq_literalModeCo e Yb Ys D delta g l m negative u ho]

/-- E324 is a CONCLUSION about the SAME literal cleaned Co, not an energy
hypothesis on a newly named amplitude. All original feature gates survive. -/
theorem actual_literalModeCo_energy_le_324
    {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B0 sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hl : 0 < l)
    (m : ℤ × ℤ) (negative : Bool) (u : (ZMod (g*l))ˣ) :
    (∑ o ∈ fixedSlice d.cleanedAlphaAtom Yb Ys D delta g l,
      ‖literalModeCo d.cleanedAlphaAtom Yb Ys D delta g l m negative u o‖ ^ 2) ≤
        energy324 d D delta g l := by
  have he := mediumAdmissible_cleanedAlphaAtom hd
  exact (literalModeCo_energy_le_original d.cleanedAlphaAtom he.1 he.2.2.1
    he.2.2.2.2.1 he.2.2.2.1 Yb Ys D delta g l m negative u).trans
      (actual_fixedFirstEnergy_le_324 hd Yb Ys hD hdelta hg hl)

/-- The first Cauchy is on ORIGINAL outer labels. Only the POSITIVE row-square
pushforward is smoothed, so there is exactly one representation payment. -/
theorem actual_literal_packet_Cauchy_six_324
    {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B0 sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hl : 0 < l)
    (m : ℤ × ℤ) (negative : Bool) (u : (ZMod (g*l))ˣ) (J : Packet → ℂ) :
    let e := d.cleanedAlphaAtom
    let B := scaleB e delta l
    let C := scaleC e D g l
    let L := packetBox B C (scaleF e D g)
    ‖∑ o ∈ fixedSlice e Yb Ys D delta g l,
      literalModeCo e Yb Ys D delta g l m negative u o * J (packetKey D delta g l o)‖ ^ 2 ≤
      energy324 d D delta g l * (tauEnvelope (g*l) D L : ℝ) * sixSmoothMass B C L J := by
  dsimp only
  let e := d.cleanedAlphaAtom
  have he := mediumAdmissible_cleanedAlphaAtom hd
  have hc := complex_finset_cauchy_norm_sq (fixedSlice e Yb Ys D delta g l)
    (literalModeCo e Yb Ys D delta g l m negative u)
    (fun o => J (packetKey D delta g l o))
  have hm := actual_packet_square_mass_le_six e he.1 he.2.2.1 he.2.2.2.2.1 he.2.2.2.1 (delta := delta)
    Yb Ys hD hg hl J
  have hE := actual_literalModeCo_energy_le_324 hd Yb Ys hD hdelta hg hl m negative u
  dsimp only at hm
  have hE0 : 0 ≤ ∑ o ∈ fixedSlice e Yb Ys D delta g l,
      ‖literalModeCo e Yb Ys D delta g l m negative u o‖ ^ 2 :=
    sum_nonneg (fun o ho => sq_nonneg _)
  have hstep := hc.trans (mul_le_mul_of_nonneg_left hm hE0)
  have hmass : 0 ≤
      (tauEnvelope (g*l) D (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ) *
        sixSmoothMass (scaleB e delta l) (scaleC e D g l)
          (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) J :=
    mul_nonneg (Nat.cast_nonneg _) (sixSmoothMass_nonneg _ _ _ _)
  exact hstep.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hE hmass)

/-- The physical tau(D) in E324 is joined by the row's explicit tau(D).
ONE ordinary maximum remains; the second BCF label-count maximum is unused. -/
theorem actual_literal_packet_Cauchy_six_324_Dtau
    {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B0 sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hl : 0 < l)
    (m : ℤ × ℤ) (negative : Bool) (u : (ZMod (g*l))ˣ) (J : Packet → ℂ) :
    let e := d.cleanedAlphaAtom
    let B := scaleB e delta l
    let C := scaleC e D g l
    let L := packetBox B C (scaleF e D g)
    ‖∑ o ∈ fixedSlice e Yb Ys D delta g l,
      literalModeCo e Yb Ys D delta g l m negative u o * J (packetKey D delta g l o)‖ ^ 2 ≤
      (energy324 d D delta g l * (D.divisors.card : ℝ)) *
        (ordinaryTauMax (g*l) L : ℝ) * sixSmoothMass B C L J := by
  dsimp only
  let e := d.cleanedAlphaAtom
  have hc := actual_literal_packet_Cauchy_six_324 hd Yb Ys hD hdelta hg hl m negative u J
  dsimp only at hc
  have ht : (tauEnvelope (g*l) D
      (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ) ≤
      (D.divisors.card : ℝ) * (ordinaryTauMax (g*l)
        (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ) := by
    exact_mod_cast tauEnvelope_le_D_times_ordinary (g*l) D
      (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g))
  have hE0 : 0 ≤ energy324 d D delta g l := by
    unfold energy324
    have hS : 0 ≤ d.Q2 := zero_le_one.trans hd.2.2.2.1
    positivity
  have hstep := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hE0)
    (sixSmoothMass_nonneg (scaleB e delta l) (scaleC e D g l)
      (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) J)
  exact hc.trans (by simpa only [mul_assoc] using hstep)

/-- Exact cancellation AFTER the real T0 has been extracted. No raw-D tail
is reused. This equality has the N^2*M^2 and S^(-3) normalization of old(P). -/
theorem T0_sq_mul_324_Dtau (d : MediumAtom) {D delta g l : ℕ}
    (hQ : 0 < d.Q1) (hR : 0 < d.Q3) (hS : 0 < d.Q2)
    (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hl : 0 < l) :
    physicalT0 d D ^ 2 * (energy324 d D delta g l * (D.divisors.card : ℝ)) =
      normalizedPacketEnergy324 d D delta g l := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hdeR : (0 : ℝ) < delta := by exact_mod_cast hdelta
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  unfold physicalT0 energy324 normalizedPacketEnergy324
  field_simp [hQ.ne', hR.ne', hS.ne', hDR.ne', hdeR.ne', hgR.ne', hlR.ne']

/-- This includes the literal log adapter's T0 exactly ONCE. Conjugation
changes neither the common coefficient norm nor that normalization. -/
theorem actual_modeCoefficient_norm_sq (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) :
    ‖ActualLogModePacketInstanceSourceOnly.modeCoefficient e D Z tag m negative‖ ^ 2 =
      physicalT0 e D ^ 2 * ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ ^ 2 := by
  unfold ActualLogModePacketInstanceSourceOnly.modeCoefficient
  have hn (z : ℂ) : ‖branch negative z‖ = ‖z‖ := by
    cases negative <;> simp [branch]
  rw [hn, norm_mul, mul_pow]
  have hb : ‖(_root_.P3ActualLogAdapterSourceOnly.base e D : ℂ)‖ ^ 2 =
      physicalT0 e D ^ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      (show _root_.P3ActualLogAdapterSourceOnly.base e D ^ 2 = physicalT0 e D ^ 2 by rfl)
  rw [hb]

def modeScalar {g l : ℕ} (e : MediumAtom) (Yb Ys : ℝ) (D delta : ℕ)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (H : Finset ℤ) : ℂ :=
  ∑ o ∈ rootSelector e Yb Ys D delta g l u,
    e.smallCoreSquaredOuterCoefficient Yb Ys o *
      ActualLogModePacketInstanceSourceOnly.actualModeRow e D Z tag m negative k H o

theorem modeScalar_eq_zero_of_empty {g l : ℕ} (e : MediumAtom) (Yb Ys : ℝ)
    (D delta : ℕ) (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (H : Finset ℤ)
    (hempty : fixedSlice e Yb Ys D delta g l = ∅) :
    modeScalar e Yb Ys D delta Z tag m negative u k H = 0 := by
  simp only [modeScalar, rootSelector, hempty, filter_empty, sum_empty]

/-- Exact scalar coupling to the NAMED actual Fourier mode and constructed J.
There is no supplied row equality and no outer label is discarded. -/
theorem actual_modeScalar_eq_packet (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} [NeZero (g*l)]
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (H : Finset ℤ) :
    modeScalar e Yb Ys D delta Z tag m negative u k H =
      ActualLogModePacketInstanceSourceOnly.modeCoefficient e D Z tag m negative *
        ∑ o ∈ fixedSlice e Yb Ys D delta g l,
          literalModeCo e Yb Ys D delta g l m negative u o *
            packetJ e D delta g l e.residue negative u k
              (ActualLogModePacketInstanceSourceOnly.modeW e m negative)
              (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative) H
              (packetKey D delta g l o) := by
  unfold modeScalar rootSelector
  rw [sum_filter, mul_sum]
  apply sum_congr rfl
  intro o ho
  by_cases hu : rootFeature D delta g l o = u
  · rw [if_pos hu,
      ActualLogModePacketInstanceSourceOnly.actualModeRow_eq_packetJ
        e hN hQ hR hS Yb Ys hD hg hl ho, hu]
    simp only [literalModeCo, if_pos hu]
    ring
  · simp only [literalModeCo, if_neg hu, zero_mul, mul_zero]

/-- True actual Fourier-mode scalar, with its literal T0*coeff, is supplied
with precisely the old physical-D squared prefactor. J remains constructed. -/
theorem actual_modeScalar_norm_sq_le_physical_prefactor
    {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B0 sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (H : Finset ℤ) :
    let e := d.cleanedAlphaAtom
    let B := scaleB e delta l
    let C := scaleC e D g l
    let L := packetBox B C (scaleF e D g)
    let J := packetJ e D delta g l e.residue negative u k
      (ActualLogModePacketInstanceSourceOnly.modeW e m negative)
      (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative) H
    ‖modeScalar e Yb Ys D delta Z tag m negative u k H‖ ^ 2 ≤
      ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ ^ 2 *
        normalizedPacketEnergy324 d D delta g l *
        (ordinaryTauMax (g*l) L : ℝ) * sixSmoothMass B C L J := by
  dsimp only
  let e := d.cleanedAlphaAtom
  let J := packetJ e D delta g l e.residue negative u k
    (ActualLogModePacketInstanceSourceOnly.modeW e m negative)
    (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative) H
  have he := mediumAdmissible_cleanedAlphaAtom hd
  have hm := actual_modeScalar_eq_packet e he.1 he.2.2.1 he.2.2.2.2.1 he.2.2.2.1 (delta := delta)
    Yb Ys hD hg hl Z tag m negative u k H
  have hc := actual_literal_packet_Cauchy_six_324_Dtau hd Yb Ys hD hdelta hg hl m negative u J
  dsimp only at hc
  rw [hm, norm_mul, mul_pow, actual_modeCoefficient_norm_sq]
  have hmul := mul_le_mul_of_nonneg_left hc
    (sq_nonneg ‖ActualLogModePacketInstanceSourceOnly.modeCoefficient e D Z tag m negative‖)
  rw [actual_modeCoefficient_norm_sq] at hmul
  have ht := T0_sq_mul_324_Dtau d
    (zero_lt_one.trans_le hd.2.2.1) (zero_lt_one.trans_le hd.2.2.2.2.1)
    (zero_lt_one.trans_le hd.2.2.2.1) hD hdelta hg hl
  change physicalT0 e D ^ 2 * (energy324 d D delta g l * (D.divisors.card : ℝ)) =
    normalizedPacketEnergy324 d D delta g l at ht
  refine hmul.trans_eq ?_
  calc
    _ = ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ ^ 2 *
        (physicalT0 e D ^ 2 * (energy324 d D delta g l * (D.divisors.card : ℝ))) *
        (ordinaryTauMax (g*l)
          (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ) *
        sixSmoothMass (scaleB e delta l) (scaleC e D g l)
          (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) J := by ring
    _ = _ := by rw [ht]

theorem packetPrefactor_sq (d : MediumAtom) (D delta g l : ℕ) (hS : 0 ≤ d.Q2) :
    packetPrefactor d D delta g l ^ 2 = normalizedPacketEnergy324 d D delta g l := by
  have h : 0 ≤ d.Q2 * (l : ℝ) * (delta : ℝ) := by positivity
  unfold packetPrefactor normalizedPacketEnergy324
  simp only [div_pow, mul_pow, Real.sq_sqrt h]
  congr 1 <;> ring

theorem actual_packetPrefactor_nonneg
    {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B0 sigma kappa c0 d) (D delta g l : ℕ) :
    0 ≤ packetPrefactor d D delta g l := by
  have hN : 0 ≤ d.U := zero_le_one.trans hd.1
  have hM : 0 ≤ d.V := zero_le_one.trans hd.2.1
  have hQ : 0 ≤ d.Q1 := zero_le_one.trans hd.2.2.1
  have hR : 0 ≤ d.Q3 := zero_le_one.trans hd.2.2.2.2.1
  have hS : 0 ≤ d.Q2 := zero_le_one.trans hd.2.2.2.1
  unfold packetPrefactor
  positivity

/-- This is the EXACT old(P) after its sqrt(tau(D)) row fee is combined.
The M and the S^(3/2) are retained. Root enumeration is not yet charged. -/
theorem packetPrefactor_eq_oldP (d : MediumAtom) (D delta g l : ℕ) (hS : 0 < d.Q2) :
    packetPrefactor d D delta g l =
      18 * (D.divisors.card : ℝ) * d.U * d.V /
        (d.Q1 * d.Q3 * d.Q2 ^ (3/2 : ℝ) * (g : ℝ) * Real.sqrt ((l : ℝ) * (delta : ℝ))) := by
  have hsqrt : Real.sqrt (d.Q2 * (l : ℝ) * (delta : ℝ)) =
      Real.sqrt d.Q2 * Real.sqrt ((l : ℝ) * (delta : ℝ)) := by
    rw [mul_assoc, Real.sqrt_mul hS.le]
  have hpow : d.Q2 ^ (3/2 : ℝ) = d.Q2 * Real.sqrt d.Q2 := by
    rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hS,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold packetPrefactor
  rw [hsqrt, hpow]
  congr 1; ring

/-- The square root is taken ONLY of row mass and ordinaryMax. No fourth
root is applied to the energy prefactor or to the later A*phi(A) charge. -/
theorem actual_modeScalar_norm_le_physical_prefactor
    {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B0 sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (H : Finset ℤ) :
    let e := d.cleanedAlphaAtom
    let B := scaleB e delta l
    let C := scaleC e D g l
    let L := packetBox B C (scaleF e D g)
    let J := packetJ e D delta g l e.residue negative u k
      (ActualLogModePacketInstanceSourceOnly.modeW e m negative)
      (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative) H
    ‖modeScalar e Yb Ys D delta Z tag m negative u k H‖ ≤
      ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ * packetPrefactor d D delta g l *
        Real.sqrt (ordinaryTauMax (g*l) L : ℝ) * Real.sqrt (sixSmoothMass B C L J) := by
  dsimp only
  let e := d.cleanedAlphaAtom
  let B := scaleB e delta l
  let C := scaleC e D g l
  let L := packetBox B C (scaleF e D g)
  let J := packetJ e D delta g l e.residue negative u k
    (ActualLogModePacketInstanceSourceOnly.modeW e m negative)
    (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative) H
  let K := ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ *
    packetPrefactor d D delta g l * Real.sqrt (ordinaryTauMax (g*l) L : ℝ) *
      Real.sqrt (sixSmoothMass B C L J)
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
      (actual_packetPrefactor_nonneg hd D delta g l)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hKsq : K ^ 2 = ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ ^ 2 *
      normalizedPacketEnergy324 d D delta g l * (ordinaryTauMax (g*l) L : ℝ) *
        sixSmoothMass B C L J := by
    dsimp only [K]
    simp only [mul_pow, packetPrefactor_sq d D delta g l (zero_le_one.trans hd.2.2.2.1),
      Real.sq_sqrt (Nat.cast_nonneg (ordinaryTauMax (g*l) L)),
      Real.sq_sqrt (sixSmoothMass_nonneg B C L J)]
  have hc := actual_modeScalar_norm_sq_le_physical_prefactor hd Yb Ys hD hdelta hg hl
    Z tag m negative u k H
  dsimp only at hc
  apply (sq_le_sq₀ (norm_nonneg _) hK).mp
  rw [hKsq]
  exact hc

def actualBlockScalar {g l : ℕ} (e : MediumAtom) (Yb Ys : ℝ) (D delta : ℕ)
    (Z : ℝ) (tag : ℕ × Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) : ℂ :=
  ∑ o ∈ rootSelector e Yb Ys D delta g l u,
    e.smallCoreSquaredOuterCoefficient Yb Ys o *
      ActualLogModePacketInstanceSourceOnly.actualBlockRow e D Z tag k o

/-- Actual complete original block: analytic reconstruction is invoked on
each real label, followed only by a finite sum. Exact Re1/2 survives. -/
theorem actualBlockScalar_hasSum_modes
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (b : ℕ) (Z : ℝ) (hZ : 0 < Z) (tag : ℕ × Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    HasSum (fun m : ℤ × ℤ =>
      (modeScalar e Yb Ys D delta Z tag m false u k
        (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) +
      modeScalar e Yb Ys D delta Z tag m true u k
        (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag)) / 2)
      (actualBlockScalar e Yb Ys D delta Z tag u k) := by
  have hs := hasSum_sum (s := rootSelector e Yb Ys D delta g l u) (fun o ho =>
    (ActualLogModePacketInstanceSourceOnly.actualBlockRow_hasSum he he.1 he.2.2.1
      he.2.2.2.2.1 he.2.2.2.1 Yb Ys hD hg hl (mem_filter.mp ho).1 b Z hZ tag k).mul_left
      (e.smallCoreSquaredOuterCoefficient Yb Ys o))
  change HasSum (fun m : ℤ × ℤ => ∑ o ∈ rootSelector e Yb Ys D delta g l u,
    e.smallCoreSquaredOuterCoefficient Yb Ys o *
      ((ActualLogModePacketInstanceSourceOnly.actualModeRow e D Z tag m false k
        (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) o +
        ActualLogModePacketInstanceSourceOnly.actualModeRow e D Z tag m true k
          (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) o) / 2))
    (actualBlockScalar e Yb Ys D delta Z tag u k) at hs
  convert! hs using 1
  funext m
  simp only [modeScalar, ← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro o ho
  ring

theorem real_half_triangle (z w : ℂ) : ‖(z+w)/2‖ ≤ (‖z‖+‖w‖)/2 := by
  calc
    _ = ‖z+w‖ / 2 := by norm_num [norm_div]
    _ ≤ _ := div_le_div_of_nonneg_right (norm_add_le z w) (by norm_num)

end
end ImbalancedChen.Part3.ActualModePhysicalDPrefactorSourceOnly

namespace ImbalancedChen.Part3.ActualLogModeWeightedCauchySourceOnly
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Finset GeneralDGateNormalization
open GeneralDActiveOuterEnergySourceOnly ActualFixedFeaturePacketPushforwardSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualPacketBCFCardEnergySourceOnly ActualModePhysicalDPrefactorSourceOnly
open scoped BigOperators

/-- The SAME actual six-piece row mass used by511; no spectral majorant. -/
def modeMass6 (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) : ℝ :=
  sixSmoothMass (scaleB e delta l) (scaleC e D g l)
    (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g))
    (packetJ e D delta g l e.residue negative u k
      (ActualLogModePacketInstanceSourceOnly.modeW e m negative)
      (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative)
      (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag))

private theorem modeMass6_nonneg (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    0 ≤ modeMass6 e D delta g l Z tag m negative u k :=
  sixSmoothMass_nonneg _ _ _ _

/-- Exact original scalar truncation, including BOTH branches and their1/2. -/
def finiteLogScalar (e : MediumAtom) (Yb Ys : ℝ) (D delta g l : ℕ)
    (Z : ℝ) (tag : ℕ × Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
    (K : Finset (ℤ × ℤ)) : ℂ :=
  ∑ m ∈ K,
    (modeScalar e Yb Ys D delta Z tag m false u k
        (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) +
      modeScalar e Yb Ys D delta Z tag m true u k
        (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag)) / 2

/-- T0 is already in modeScalar and its physical prefactor. Weight by coeff. -/
def coefficientMass (e : MediumAtom) (D : ℕ) (Z : ℝ) (tag : ℕ × Bool)
    (K : Finset (ℤ × ℤ)) : ℝ :=
  ∑ m ∈ K, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖

def weightedModeMass6 (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
    (K : Finset (ℤ × ℤ)) : ℝ :=
  ∑ m ∈ K, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ *
    ((modeMass6 e D delta g l Z tag m false u k +
      modeMass6 e D delta g l Z tag m true u k) / 2)

private theorem norm_half_sq_le (z w : ℂ) :
    ‖(z+w)/2‖^2 ≤ (‖z‖^2+‖w‖^2)/2 := by
  have ht := real_half_triangle z w
  have hsq := mul_le_mul ht ht (norm_nonneg ((z+w)/2))
    (show (0 : ℝ) ≤ (‖z‖+‖w‖)/2 by positivity)
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

/-- Genuine cross-mode Cauchy. The ONLY energy input is511's proved actual
mode bound. The zero-coefficient case requires no division or support hyp. -/
theorem actual_finite_log_mode_Cauchy_physicalD
    {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B0 sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
    (K : Finset (ℤ × ℤ)) :
    let e := d.cleanedAlphaAtom
    ‖finiteLogScalar e Yb Ys D delta g l Z tag u k K‖^2 ≤
      normalizedPacketEnergy324 d D delta g l *
        (ordinaryTauMax (g*l)
          (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ) *
        coefficientMass e D Z tag K * weightedModeMass6 e D delta g l Z tag u k K := by
  dsimp only
  let e := d.cleanedAlphaAtom
  let O : ℝ := ordinaryTauMax (g*l)
    (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g))
  let E : ℝ := normalizedPacketEnergy324 d D delta g l * O
  let a (m : ℤ × ℤ) : ℝ := ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖
  let z (m : ℤ × ℤ) (negative : Bool) : ℂ :=
    modeScalar e Yb Ys D delta Z tag m negative u k
      (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag)
  let A (m : ℤ × ℤ) : ℝ :=
    (modeMass6 e D delta g l Z tag m false u k +
      modeMass6 e D delta g l Z tag m true u k) / 2
  let r (m : ℤ × ℤ) : ℝ := ‖(z m false + z m true)/2‖
  have hE : 0 ≤ E := by
    apply mul_nonneg
    · rw [← packetPrefactor_sq d D delta g l (zero_le_one.trans hd.2.2.2.1)]
      exact sq_nonneg _
    · exact Nat.cast_nonneg _
  have hA (m : ℤ × ℤ) : 0 ≤ A m :=
    div_nonneg (add_nonneg (modeMass6_nonneg e D delta g l Z tag m false u k)
      (modeMass6_nonneg e D delta g l Z tag m true u k)) (by norm_num)
  have hm (m : ℤ × ℤ) (negative : Bool) :
      ‖z m negative‖^2 ≤ a m^2 * normalizedPacketEnergy324 d D delta g l * O *
        modeMass6 e D delta g l Z tag m negative u k :=
    actual_modeScalar_norm_sq_le_physical_prefactor hd Yb Ys hD hdelta hg hl
      Z tag m negative u k (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag)
  have hp (m : ℤ × ℤ) : r m^2 ≤ a m * (a m * E * A m) := by
    calc
      r m^2 ≤ (‖z m false‖^2+‖z m true‖^2)/2 := norm_half_sq_le _ _
      _ ≤ (a m^2 * normalizedPacketEnergy324 d D delta g l * O *
            modeMass6 e D delta g l Z tag m false u k +
          a m^2 * normalizedPacketEnergy324 d D delta g l * O *
            modeMass6 e D delta g l Z tag m true u k)/2 :=
        div_le_div_of_nonneg_right (add_le_add (hm m false) (hm m true)) (by norm_num)
      _ = a m * (a m * E * A m) := by
        dsimp only [E, A]
        ring
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul K
    (r := r) (f := a) (g := fun m => a m * E * A m)
    (fun m _ => norm_nonneg _)
    (fun m _ => mul_nonneg (mul_nonneg (norm_nonneg _) hE) (hA m))
    (fun m _ => hp m)
  have ht : ‖finiteLogScalar e Yb Ys D delta g l Z tag u k K‖ ≤ ∑ m ∈ K, r m :=
    norm_sum_le _ _
  have hsq : ‖finiteLogScalar e Yb Ys D delta g l Z tag u k K‖^2 ≤
      (∑ m ∈ K, r m)^2 := by
    simpa only [pow_two] using mul_le_mul ht ht (norm_nonneg _)
      (sum_nonneg (fun m _ => norm_nonneg _))
  have hs : (∑ m ∈ K, a m * E * A m) = E * ∑ m ∈ K, a m * A m := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m _
    ring
  calc
    ‖finiteLogScalar e Yb Ys D delta g l Z tag u k K‖^2 ≤ (∑ m ∈ K, r m)^2 := hsq
    _ ≤ (∑ m ∈ K, a m) * ∑ m ∈ K, a m * E * A m := hcs
    _ = normalizedPacketEnergy324 d D delta g l * O *
        coefficientMass e D Z tag K * weightedModeMass6 e D delta g l Z tag u k K := by
      rw [hs]
      dsimp only [E, coefficientMass, weightedModeMass6, a, A]
      ring

/-- Exactly the actual finite signed-dyadic tag and residue carrier. -/
def actualTagResidueCarrier (e : MediumAtom) (D : ℕ) (Z : ℝ) (A : ℕ) [NeZero A] :
    Finset ((ℕ × Bool) × ZMod A) :=
  ((_root_.P3ActualLogAdapterSourceOnly.window e D Z).image
    _root_.P3ActualLogAdapterSourceOnly.dyadicKey) ×ˢ univ

/-- Sum POSITIVE block squares on the original finite tag/residue carrier.
There is no uncharged Cauchy across tags, roots or residues in this statement. -/
theorem actual_tag_residue_square_sum_le
    {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B0 sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hl : 0 < l)
    (Z : ℝ) (u : (ZMod (g*l))ˣ) (K : Finset (ℤ × ℤ)) :
    let e := d.cleanedAlphaAtom
    (∑ q ∈ actualTagResidueCarrier e D Z (g*l),
      ‖finiteLogScalar e Yb Ys D delta g l Z q.1 u q.2 K‖^2) ≤
      (normalizedPacketEnergy324 d D delta g l *
        (ordinaryTauMax (g*l)
          (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ)) *
      ∑ q ∈ actualTagResidueCarrier e D Z (g*l),
        coefficientMass e D Z q.1 K * weightedModeMass6 e D delta g l Z q.1 u q.2 K := by
  dsimp only
  calc
    _ ≤ ∑ q ∈ actualTagResidueCarrier d.cleanedAlphaAtom D Z (g*l),
        normalizedPacketEnergy324 d D delta g l *
          (ordinaryTauMax (g*l) (packetBox (scaleB d.cleanedAlphaAtom delta l)
            (scaleC d.cleanedAlphaAtom D g l) (scaleF d.cleanedAlphaAtom D g)) : ℝ) *
          coefficientMass d.cleanedAlphaAtom D Z q.1 K *
          weightedModeMass6 d.cleanedAlphaAtom D delta g l Z q.1 u q.2 K :=
      sum_le_sum (fun q _ => actual_finite_log_mode_Cauchy_physicalD hd Yb Ys
        hD hdelta hg hl Z q.1 u q.2 K)
    _ = _ := by
      conv_rhs => rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring

/-- The actual installed finite-Poisson adapter changes this SAME mass into
the real part of its complete six-piece expression; all completed m survive. -/
theorem modeMass6_eq_completed_re
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e) (D delta g l : ℕ) [NeZero (g*l)]
    (hdelta : 0 < delta) (hl : 0 < l) (Z : ℝ) (tag : ℕ × Bool)
    (m : ℤ × ℤ) (negative : Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    modeMass6 e D delta g l Z tag m negative u k =
      (ActualM2FinitePoissonAdapterSourceOnly.completedModeSix
        e D delta g l Z tag m negative u k).re :=
  congrArg Complex.re (ActualM2FinitePoissonAdapterSourceOnly.actual_mode_Mass6_eq_completed
    he D delta g l hdelta hl Z tag m negative u k)

/-- The very same log coefficient mass pays the original SINGLE5kappa fee.
The premise is kappa>=0, so kappa=0 is included. No canonical4D budget is substituted. -/
theorem finite_coefficientMass_le_single_five
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e) (hkappa : 0 ≤ kappa)
    (b D : ℕ) (Z : ℝ) (hZ : 0 < Z) (tag : ℕ × Bool) (K : Finset (ℤ × ℤ)) :
    coefficientMass e D Z tag K ≤
      16 * _root_.P3ActualJointGSourceOnly.fourierCost b * e.scale^(5*kappa) /
        (1+_root_.P3ActualLogAdapterSourceOnly.lambda e D tag.1)^b := by
  obtain ⟨hs, hb⟩ := _root_.P3ActualLogAdapterSourceOnly.coeff_l1_original_five
    he hkappa b D Z hZ tag
  have hfin : coefficientMass e D Z tag K ≤
      ∑' m : ℤ × ℤ, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ := by
    simpa only [coefficientMass] using! hs.sum_le_tsum K (fun m _ => norm_nonneg _)
  exact hfin.trans hb

end
end ImbalancedChen.Part3.ActualLogModeWeightedCauchySourceOnly

/-!
SOURCEONLY / UNCOMPILED / COMPLETE MINIMAL INHERITANCE APPEND.
Load AFTER exact proposed physical-D parent bf957b976ee5786c72250a411cdff5a27c2bf8af39b29ca6fda070e8a80b87d3.
This file is not currently a standalone actual module. No missing-parent import
is executed here. Collect this genuine extra import at the qualification head:
  import ImbalancedChen.Part3PolynomialResidueDivisorBound
Future PROPOSED parent import, only AFTER ROOT installs the real module:
  import ImbalancedChen.Part3ActualLogModeWeightedPhysicalDEnergy
That path is a proposed assembly name, not a claim of current qualification.

Only the free-positive-epsilon V2 geometry/divisor suppliers needed by e909
are inherited. The old kappa>0 reallocation and alternative64BCF/two-max
consumer are excluded. The nine-line actual_scales_nonneg body is supplied
locally from frozen16add, since the new minimal physical-D parent omits it.
All original statement types and definitions are retained. One ordinary tau
maximum is paid with selectable epsilon; physical tau(D), T0, E324, Re/2,
same log coefficients and single5*kappa remain in their previous positions.
No full weighted Mass6 or spectral estimate is assumed or concluded.
-/

namespace ImbalancedChen.Part3.ActualPacketBCFCardEnergySourceOnly
noncomputable section
open ActualPositiveLatticeSmoothCoverSourceOnly

lemma actual_scales_nonneg (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (D delta g l : ℕ) :
    0 ≤ scaleB e delta l ∧ 0 ≤ scaleC e D g l ∧ 0 ≤ scaleF e D g := by
  have hNR : 0 ≤ e.U := zero_le_one.trans hN
  have hQR : 0 ≤ e.Q1 := zero_le_one.trans hQ
  have hRR : 0 ≤ e.Q3 := zero_le_one.trans hR
  have hSR : 0 ≤ e.Q2 := zero_le_one.trans hS
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [scaleB, scaleC, scaleF] <;> positivity

end
end ImbalancedChen.Part3.ActualPacketBCFCardEnergySourceOnly

namespace ImbalancedChen.Part3.ActualOrdinaryTauBudgetSourceOnly
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Finset GeneralDGateNormalization
open GeneralDActiveOuterEnergySourceOnly GeneralDActivePairCountSourceOnly
open ActualFixedFeaturePacketPushforwardSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualPacketBCFCardEnergySourceOnly
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators

lemma scale_one_le {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  change 1 ≤ d.U * d.V
  simpa only [one_mul] using
    mul_le_mul hd.1 hd.2.1 zero_le_one (zero_le_one.trans hd.1)

/-- Only actual admissibility is used for these polynomial coordinate scales. -/
theorem admissible_geometry {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma) :
    3 ≤ d.scale ∧ d.U ≤ d.scale ∧ d.Q2 ≤ d.scale ∧ d.Q3 ≤ d.scale := by
  have hx := scale_one_le hd
  obtain ⟨hU, hV, _hQ, hS, hR, hlarge, _ha0, _ha1, _hfirst, hgeom, _⟩ := hd
  have he1 := Real.add_one_le_exp (1 : ℝ)
  have he2 := Real.add_one_le_exp (Real.exp 1)
  have hx3 : 3 ≤ d.scale := by linarith
  have hUx : d.U ≤ d.scale := by
    change d.U ≤ d.U * d.V
    exact le_mul_of_one_le_right (zero_le_one.trans hU) hV
  have hpow : d.scale ^ (1 - 8 * sigma) ≤ d.scale := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx
      (show 1 - 8 * sigma ≤ 1 by linarith)
  have hU2 : 1 ≤ d.U ^ 2 := by nlinarith
  have hR2 : 1 ≤ d.Q3 ^ 2 := by nlinarith
  have hprod : 1 ≤ d.U ^ 2 * d.Q3 ^ 2 := by
    simpa only [one_mul] using mul_le_mul hU2 hR2 zero_le_one (sq_nonneg d.U)
  have hSx : d.Q2 ≤ d.scale := by
    calc
      _ ≤ d.Q2 * (d.U ^ 2 * d.Q3 ^ 2) :=
        le_mul_of_one_le_right (zero_le_one.trans hS) hprod
      _ = d.U ^ 2 * d.Q2 * d.Q3 ^ 2 := by ring
      _ ≤ _ := hgeom.le.trans hpow
  have hU2S : 1 ≤ d.U ^ 2 * d.Q2 := by
    simpa only [one_mul] using mul_le_mul hU2 hS zero_le_one (sq_nonneg d.U)
  have hRx : d.Q3 ≤ d.scale := by
    calc
      _ ≤ d.Q3 ^ 2 := by nlinarith
      _ ≤ (d.U ^ 2 * d.Q2) * d.Q3 ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) hU2S
      _ ≤ _ := hgeom.le.trans hpow
  exact ⟨hx3, hUx, hSx, hRx⟩

/-- The small l and positive delta hypotheses come from a literal surviving label. -/
theorem actual_features_of_mem {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (_hsigma : 0 < sigma)
    (hsigmaTop : sigma ≤ 4) {D delta g l : ℕ} {o : OuterIndex}
    (ho : o ∈ fixedSlice d (d.scale ^ (sigma/4)) (d.scale ^ (sigma/4)) D delta g l) :
    0 < delta ∧ (l : ℝ) ≤ d.scale := by
  obtain ⟨hactive, _hDo, hdelta, hgc, hsup⟩ := mem_filter.mp ho
  have hsupported := (mem_filter.mp hactive).1
  have hgate := d.smallCoreSquaredSupportedOuterCarrier_gates _ _ o hsupported
  rw [hgc, hsup] at hgate
  have hY : d.scale ^ (sigma/4) ≤ d.scale := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (scale_one_le hd) (show sigma/4 ≤ 1 by linarith)
  have hf := fixedSlice_facts d _ _ D delta g l ho
  have hr := factorCarrier_bounds hd.2.2.2.2.1 hf.2.2.2.1
  have hdpos : 0 < delta := by
    rw [← hdelta]
    exact Nat.gcd_pos_of_pos_left D hr.1
  exact ⟨hdpos, hgate.2.trans hY⟩

/-- The complete six-cover box, including its larger smooth support. -/
theorem packetBox_poly_six {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B0 sigma kappa c0 d) (hsigma : 0 < sigma)
    {D delta g l : ℕ} (hD : 0 < D) (hdelta : 0 < delta) (hg : 0 < g) (hl : 0 < l)
    (hlx : (l : ℝ) ≤ d.scale) {k : Packet}
    (hk : k ∈ packetBox (scaleB d delta l) (scaleC d D g l) (scaleF d D g)) :
    (k.1.1 : ℝ) ≤ d.scale ^ 6 ∧ (k.1.2 : ℝ) ≤ d.scale ^ 6 := by
  obtain ⟨hx3, hNx, hSx, hRx⟩ := admissible_geometry hd hsigma
  have hU0 : 0 ≤ d.U := zero_le_one.trans hd.1
  have hS0 : 0 ≤ d.Q2 := zero_le_one.trans hd.2.2.2.1
  have hR0 : 0 ≤ d.Q3 := zero_le_one.trans hd.2.2.2.2.1
  have hx0 : 0 ≤ d.scale := (zero_le_one.trans (scale_one_le hd))
  have hdelta1 : (1 : ℝ) ≤ delta := by exact_mod_cast (Nat.succ_le_iff.mpr hdelta)
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Nat.succ_le_iff.mpr hg)
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (Nat.succ_le_iff.mpr hl)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (Nat.succ_le_iff.mpr hD)
  have hgl1 : (1 : ℝ) ≤ (g : ℝ) * l := by
    simpa only [one_mul] using mul_le_mul hg1 hl1 zero_le_one (Nat.cast_nonneg g)
  have hden1 : (1 : ℝ) ≤ (g : ℝ) * l * D := by
    simpa only [one_mul] using mul_le_mul hgl1 hD1 zero_le_one (by positivity)
  have hNR : d.U * d.Q3 ≤ d.scale ^ 2 := by
    simpa only [pow_two] using mul_le_mul hNx hRx
      (zero_le_one.trans hd.2.2.2.2.1) hx0
  have hbnum : (l : ℝ) * d.U * d.Q3 ≤ d.scale ^ 3 := by
    calc
      _ = (l : ℝ) * (d.U * d.Q3) := by ring
      _ ≤ d.scale * d.scale ^ 2 := mul_le_mul hlx hNR
        (by positivity) hx0
      _ = _ := by ring
  have hcnum : d.U * d.Q3 * d.Q2 ≤ d.scale ^ 3 := by
    calc
      _ ≤ d.scale ^ 2 * d.scale := mul_le_mul hNR hSx
        (zero_le_one.trans hd.2.2.2.1) (sq_nonneg _)
      _ = _ := by ring
  have hB : scaleB d delta l ≤ d.scale ^ 3 :=
    (div_le_self (by positivity) hdelta1).trans hbnum
  have hC : scaleC d D g l ≤ d.scale ^ 3 :=
    (div_le_self (by positivity) hden1).trans hcnum
  have hxCube : (10 : ℝ) ≤ d.scale ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hx3 3
    norm_num at h
    linarith
  have hwide5 : 5 * scaleB d delta l ≤ d.scale ^ 6 := by
    calc
      _ ≤ 5 * d.scale ^ 3 := mul_le_mul_of_nonneg_left hB (by norm_num)
      _ ≤ d.scale ^ 3 * d.scale ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith : (5 : ℝ) ≤ d.scale ^ 3) (by positivity)
      _ = _ := by ring
  have hwide10 : 10 * scaleC d D g l ≤ d.scale ^ 6 := by
    calc
      _ ≤ 10 * d.scale ^ 3 := mul_le_mul_of_nonneg_left hC (by norm_num)
      _ ≤ d.scale ^ 3 * d.scale ^ 3 := mul_le_mul_of_nonneg_right hxCube (by positivity)
      _ = _ := by ring
  obtain ⟨hraw, _⟩ := mem_filter.mp hk
  obtain ⟨hbc, _⟩ := mem_product.mp hraw
  obtain ⟨hb, hc⟩ := mem_product.mp hbc
  obtain ⟨hBn, hCn, _hFn⟩ := actual_scales_nonneg d hd.1 hd.2.2.1
    hd.2.2.2.2.1 hd.2.2.2.1 D delta g l
  constructor
  · exact ((show (k.1.1 : ℝ) ≤ Nat.floor (5 * scaleB d delta l) by
      exact_mod_cast (mem_Ioc.mp hb).2).trans
        (Nat.floor_le (by positivity))).trans hwide5
  · exact ((show (k.1.2 : ℝ) ≤ Nat.floor (10 * scaleC d D g l) by
      exact_mod_cast (mem_Ioc.mp hc).2).trans
        (Nat.floor_le (by positivity))).trans hwide10

/-- Divisor cost of a finite maximum. No positive lower bound on a quotient
or on the finite carrier is assumed; tau(0)=0 is treated explicitly. -/
theorem finite_ordinaryTauMax_sq_le {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ A : ℕ, 1 ≤ A →
      ∀ L : Finset Packet,
        (∀ k ∈ L, (k.1.1 : ℝ) ≤ x ^ 6 ∧ (k.1.2 : ℝ) ≤ x ^ 6) →
        (ordinaryTauMax A L : ℝ) ^ 2 ≤ C * x ^ (36 * eps) := by
  obtain ⟨K, hK, hTau⟩ :=
    PolynomialResidueDivisorBound.fouvryTau_le_const_rpow (k := 2) (by norm_num) heps
  refine ⟨K ^ 6, by positivity, fun x hx A _hA L hpoly => ?_⟩
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  let M : ℝ := K * x ^ (6 * eps)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ht (n : ℕ) (hn : (n : ℝ) ≤ x ^ 6) : (n.divisors.card : ℝ) ≤ M := by
    by_cases hn0 : n = 0
    · subst n
      simpa only [Nat.divisors_zero, card_empty, Nat.cast_zero] using hM
    · have htau : (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ eps := by
        simpa only [fouvryTau_two] using hTau n (Nat.pos_of_ne_zero hn0)
      calc
        _ ≤ K * (n : ℝ) ^ eps := htau
        _ ≤ K * (x ^ 6) ^ eps := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg n) hn heps.le) hK.le
        _ = M := by
          dsimp only [M]
          congr 1
          simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hx0 6 eps).symm
  have hpoint (k : Packet) (hk : k ∈ L) : (ordinaryTau A k : ℝ) ≤ M ^ 3 := by
    have hdiv : ((k.1.1 / A : ℕ) : ℝ) ≤ x ^ 6 :=
      (show ((k.1.1 / A : ℕ) : ℝ) ≤ k.1.1 by
        exact_mod_cast Nat.div_le_self k.1.1 A).trans (hpoly k hk).1
    have hq := ht (k.1.1 / A) hdiv
    have hc := ht k.1.2 (hpoly k hk).2
    have hc2 : (k.1.2.divisors.card : ℝ) ^ 2 ≤ M ^ 2 :=
      (sq_le_sq₀ (Nat.cast_nonneg _) hM).mpr hc
    calc
      _ = ((k.1.1 / A).divisors.card : ℝ) * (k.1.2.divisors.card : ℝ) ^ 2 := by
        simp only [ordinaryTau, Nat.cast_mul, Nat.cast_pow]
      _ ≤ M * M ^ 2 := mul_le_mul hq hc2 (sq_nonneg _) hM
      _ = M ^ 3 := by ring
  have hmaxNat : ordinaryTauMax A L ≤ Nat.floor (M ^ 3) := by
    apply Finset.sup_le
    intro k hk
    exact Nat.le_floor (hpoint k hk)
  have hmax : (ordinaryTauMax A L : ℝ) ≤ M ^ 3 :=
    (show (ordinaryTauMax A L : ℝ) ≤ Nat.floor (M ^ 3) by
      exact_mod_cast hmaxNat).trans (Nat.floor_le (by positivity))
  have hpow : (x ^ (6 * eps)) ^ 6 = x ^ (36 * eps) := by
    calc
      _ = x ^ ((6 * eps) * (6 : ℝ)) := (Real.rpow_mul_natCast hx0 (6 * eps) 6).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ (M ^ 3) ^ 2 := (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr hmax
    _ = K ^ 6 * (x ^ (6 * eps)) ^ 6 := by dsimp [M]; ring
    _ = _ := by rw [hpow]

end
end ImbalancedChen.Part3.ActualOrdinaryTauBudgetSourceOnly

namespace ImbalancedChen.Part3.ActualPhysicalDSelectableDivisorSourceOnly
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Finset GeneralDGateNormalization
open GeneralDActivePairCountSourceOnly GeneralDActiveOuterEnergySourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly ActualPacketBCFCardEnergySourceOnly
open ActualModePhysicalDPrefactorSourceOnly ActualSeparatedRowPacketMatchSourceOnly
open ActualOrdinaryTauBudgetSourceOnly
open scoped BigOperators

/-- The new divisor loss occupies HALF of an EXISTING aggregate reserve.
The other half remains for the finite aggregate of old selectable costs.
In applications choose eps<=sigma/10 BEFORE the atom and before kappa. -/
theorem two_epsilon_halves_fit_existing_reserve {x eps sigma : ℝ}
    (hx : 1 ≤ x) (heps : 0 < eps) (hbudget : eps ≤ sigma/10) :
    0 < eps/2 ∧ x ^ (eps/2) * x ^ (eps/2) ≤ x ^ (sigma/10) := by
  refine ⟨by positivity, ?_⟩
  rw [← Real.rpow_add (zero_lt_one.trans_le hx)]
  apply Real.rpow_le_rpow_of_exponent_le hx
  linarith

theorem sqrt_nat_le_one_add_sq (n : ℕ) : Real.sqrt (n : ℝ) ≤ 1 + (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, Real.sqrt_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    norm_num
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hm := mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hn1)
      nlinarith
    exact ((Real.sqrt_le_self_iff).mpr (Or.inr hn1)).trans (by linarith)

/-- Uniform constant precedes every atom, physical feature and kappa.
The polynomial box is DERIVED from actual admissibility and nonempty support. -/
theorem actual_ordinaryTauMax_sqrt_selectable {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom},
      MediumAdmissible B0 sigma kappa c0 d → 0 < sigma → sigma ≤ 4 →
      ∀ {D delta g l : ℕ}, 0 < D → 0 < g → 0 < l →
      (fixedSlice d (d.scale ^ (sigma/4)) (d.scale ^ (sigma/4)) D delta g l).Nonempty →
      Real.sqrt (ordinaryTauMax (g*l)
        (packetBox (scaleB d delta l) (scaleC d D g l) (scaleF d D g)) : ℝ) ≤
        C * d.scale ^ eps := by
  obtain ⟨K, hK, hall⟩ := finite_ordinaryTauMax_sq_le
    (show (0 : ℝ) < eps/36 by positivity)
  refine ⟨1+K, by linarith, fun {B0 sigma kappa c0 d} hd hsigma hsigmaTop
    {D delta g l} hD hg hl hactive => ?_⟩
  obtain ⟨o, ho⟩ := hactive
  obtain ⟨hdelta, hlx⟩ := actual_features_of_mem hd hsigma hsigmaTop ho
  have hA : 1 ≤ g*l := Nat.succ_le_iff.mpr (Nat.mul_pos hg hl)
  have hmax := hall d.scale (scale_one_le hd) (g*l) hA _
    (fun p hp => packetBox_poly_six hd hsigma hD hdelta hg hl hlx hp)
  rw [show (36 : ℝ) * (eps/36) = eps by ring] at hmax
  have hx : 1 ≤ d.scale ^ eps := Real.one_le_rpow (scale_one_le hd) heps.le
  calc
    _ ≤ 1 + (ordinaryTauMax (g*l)
        (packetBox (scaleB d delta l) (scaleC d D g l) (scaleF d D g)) : ℝ) ^ 2 :=
      sqrt_nat_le_one_add_sq _
    _ ≤ 1 + K * d.scale ^ eps := add_le_add_right hmax 1
    _ ≤ _ := by nlinarith

/-- Actual raw mode supplier in the EXACT old physical-D normalization.
The ordinary divisor fee is paid from an existing freely selectable epsilon;
the physical tau(D) and the single Fourier 5*kappa remain in their own slots. -/
theorem actual_modeScalar_oldP_selectable {eps : ℝ} (heps : 0 < eps) :
    ∃ Ceps : ℝ, 0 < Ceps ∧ ∀ {B0 : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom},
      MediumAdmissible B0 sigma kappa c0 d → 0 < sigma → sigma ≤ 4 →
      ∀ {D delta g l : ℕ} [NeZero (g*l)], 0 < D → 0 < delta → 0 < g → 0 < l →
      ∀ (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
        (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (H : Finset ℤ),
      let e := d.cleanedAlphaAtom
      let Y := e.scale ^ (sigma/4)
      let B := scaleB e delta l
      let C := scaleC e D g l
      let L := packetBox B C (scaleF e D g)
      let J := packetJ e D delta g l e.residue negative u k
        (ActualLogModePacketInstanceSourceOnly.modeW e m negative)
        (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative) H
      ‖modeScalar e Y Y D delta Z tag m negative u k H‖ ≤
        Ceps * d.scale ^ eps * ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ *
          packetPrefactor d D delta g l * Real.sqrt (sixSmoothMass B C L J) := by
  obtain ⟨Ceps, hCeps, hmax⟩ := actual_ordinaryTauMax_sqrt_selectable heps
  refine ⟨Ceps, hCeps, fun {B0 sigma kappa c0 d} hd hsigma hsigmaTop
    {D delta g l} _ hD hdelta hg hl Z tag m negative u k H => ?_⟩
  dsimp only
  let e := d.cleanedAlphaAtom
  let Y := e.scale ^ (sigma/4)
  let B := scaleB e delta l
  let C := scaleC e D g l
  let L := packetBox B C (scaleF e D g)
  let J := packetJ e D delta g l e.residue negative u k
    (ActualLogModePacketInstanceSourceOnly.modeW e m negative)
    (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative) H
  have he := mediumAdmissible_cleanedAlphaAtom hd
  by_cases hactive : (fixedSlice e Y Y D delta g l).Nonempty
  · have ht := hmax he hsigma hsigmaTop hD hg hl hactive
    change Real.sqrt (ordinaryTauMax (g*l) L : ℝ) ≤ Ceps * d.scale ^ eps at ht
    have hc := actual_modeScalar_norm_le_physical_prefactor hd Y Y hD hdelta hg hl
      Z tag m negative u k H
    dsimp only at hc
    have hpre : 0 ≤ ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ *
        packetPrefactor d D delta g l :=
      mul_nonneg (norm_nonneg _) (actual_packetPrefactor_nonneg hd D delta g l)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hpre)
      (Real.sqrt_nonneg (sixSmoothMass B C L J))
    exact hc.trans (by convert! hh using 1; ring)
  · have hempty := not_nonempty_iff_eq_empty.mp hactive
    rw [modeScalar_eq_zero_of_empty e Y Y D delta Z tag m negative u k H hempty, norm_zero]
    have hP := actual_packetPrefactor_nonneg hd D delta g l
    have hx : 0 ≤ d.scale ^ eps := Real.rpow_nonneg (zero_le_one.trans (scale_one_le hd)) eps
    positivity

end
end ImbalancedChen.Part3.ActualPhysicalDSelectableDivisorSourceOnly
