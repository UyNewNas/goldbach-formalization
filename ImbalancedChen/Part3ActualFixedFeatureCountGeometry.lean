import ImbalancedChen.Part3ActualCompletedSquarePushforward
import ImbalancedChen.Part3ActualM2FinitePoissonAdapter
import ImbalancedChen.Part3ActualClosedTCountLicense

/-!
SOURCEONLY / UNCOMPILED. Both direct imports are existing actual sources.
This supplies ONLY the actual fixed-feature geometry in line23/24 of
a4e065ce. In that CP, G is the positive dyadic f scale and R is the
t-count chart scale; neither is the root modulus A=g*l.
The definitions below are the literal Nat.log / Nat.ceil formulas of
the pending closed-T/fKey count license, with unambiguous names.
No parameter is replaced by a power of x in its definition.
sigma>=0 suffices; kappa is arbitrary, including zero. No sigma upper
bound, residue-size exponent, global-Z cap or spectral premise is used.
Actual signed f, both unit gates and the exact baseCarrier are retained
in the main theorem's source membership. Gamma/log weights are untouched.
-/

namespace ImbalancedChen.Part3.ActualFixedFeatureCountGeometrySourceOnly
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Finset
open GeneralDGateNormalization GeneralDActivePairCountSourceOnly
open GeneralDActiveOuterEnergySourceOnly ActualFixedFeaturePacketPushforwardSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualCompletedSquarePushforwardSourceOnly ActualM2FinitePoissonAdapterSourceOnly

/-- Exactly countScale of the pending two-chart license, after reducing ceilIndex. -/
def tCountScale (S : ℝ) (upper : Bool) : ℝ :=
  ((if upper then 2 * Nat.ceil S else Nat.ceil S : ℕ) : ℝ)

/-- Exactly fScale (fKey s).1 of the pending signed-f license. -/
def sourceFScale (s : Source) : ℝ := ((2 : ℕ) ^ Nat.log 2 s.1.natAbs : ℕ)

private theorem admissible_geometry {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (hsigma : 0 ≤ sigma) :
    1 ≤ e.scale ∧ e.U ≤ e.scale ∧ e.Q1 ≤ e.scale ∧
      e.Q2 ≤ e.scale ∧ e.Q3 ≤ e.scale := by
  obtain ⟨hU, hV, _hQ, hS, hR, _, _, _, hfirst, hgeom, _⟩ := he
  have hU0 : 0 ≤ e.U := zero_le_one.trans hU
  have hS0 : 0 ≤ e.Q2 := zero_le_one.trans hS
  have hx : 1 ≤ e.scale := by
    change 1 ≤ e.U * e.V
    simpa only [one_mul] using mul_le_mul hU hV zero_le_one hU0
  have hUx : e.U ≤ e.scale := le_mul_of_one_le_right hU0 hV
  have hsmall : e.scale ^ (-sigma) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hx (show -sigma ≤ 0 by linarith)
  have hQx : e.Q1 ≤ e.scale := by
    calc
      _ ≤ e.U * e.scale ^ (-sigma) := hfirst.le
      _ ≤ e.U * 1 := mul_le_mul_of_nonneg_left hsmall hU0
      _ = e.U := mul_one _
      _ ≤ _ := hUx
  have hpow : e.scale ^ (1 - 8 * sigma) ≤ e.scale := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx
      (show 1 - 8 * sigma ≤ 1 by linarith)
  have hU2 : 1 ≤ e.U ^ 2 := one_le_pow₀ hU
  have hR2 : 1 ≤ e.Q3 ^ 2 := one_le_pow₀ hR
  have hprod : 1 ≤ e.U ^ 2 * e.Q3 ^ 2 := by
    simpa only [one_mul] using mul_le_mul hU2 hR2 zero_le_one (sq_nonneg e.U)
  have hSx : e.Q2 ≤ e.scale := by
    calc
      _ ≤ e.Q2 * (e.U ^ 2 * e.Q3 ^ 2) := le_mul_of_one_le_right hS0 hprod
      _ = e.U ^ 2 * e.Q2 * e.Q3 ^ 2 := by ring
      _ ≤ _ := hgeom.le.trans hpow
  have hU2S : 1 ≤ e.U ^ 2 * e.Q2 := by
    simpa only [one_mul] using mul_le_mul hU2 hS zero_le_one (sq_nonneg e.U)
  have hRx : e.Q3 ≤ e.scale := by
    calc
      _ ≤ e.Q3 ^ 2 := by nlinarith
      _ ≤ (e.U ^ 2 * e.Q2) * e.Q3 ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hU2S
      _ ≤ _ := hgeom.le.trans hpow
  exact ⟨hx, hUx, hQx, hSx, hRx⟩

private theorem physicalT0_positive_and_inv_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (hsigma : 0 ≤ sigma)
    {D : ℕ} (hD : 0 < D) :
    0 < physicalT0 e D ∧ 1 / physicalT0 e D ≤ e.scale ^ 5 := by
  have hx := admissible_geometry he hsigma
  have hM : 1 ≤ e.V := he.2.1
  have hQ : 1 ≤ e.Q1 := he.2.2.1
  have hS : 1 ≤ e.Q2 := he.2.2.2.1
  have hR : 1 ≤ e.Q3 := he.2.2.2.2.1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hM0 : 0 < e.V := zero_lt_one.trans_le hM
  have hQ0 : 0 < e.Q1 := zero_lt_one.trans_le hQ
  have hS0 : 0 < e.Q2 := zero_lt_one.trans_le hS
  have hR0 : 0 < e.Q3 := zero_lt_one.trans_le hR
  have hden : 0 < e.V * (D : ℝ) := mul_pos hM0 hDR
  have hden1 : 1 ≤ e.V * (D : ℝ) := by
    simpa only [one_mul] using mul_le_mul hM hD1 zero_le_one hM0.le
  have hnum0 : 0 ≤ e.Q1 * e.Q3 ^ 2 * e.Q2 ^ 2 := by positivity
  have hR2x : e.Q3 ^ 2 ≤ e.scale ^ 2 :=
    pow_le_pow_left₀ hR0.le hx.2.2.2.2 2
  have hS2x : e.Q2 ^ 2 ≤ e.scale ^ 2 :=
    pow_le_pow_left₀ hS0.le hx.2.2.2.1 2
  have hnum : e.Q1 * e.Q3 ^ 2 * e.Q2 ^ 2 ≤ e.scale ^ 5 := by
    calc
      _ ≤ e.scale * e.scale ^ 2 * e.scale ^ 2 :=
        mul_le_mul (mul_le_mul hx.2.2.1 hR2x (sq_nonneg _) (zero_le_one.trans hx.1))
          hS2x (sq_nonneg _)
            (mul_nonneg (zero_le_one.trans hx.1) (sq_nonneg e.scale))
      _ = _ := by ring
  have hinv : 1 / physicalT0 e D =
      (e.Q1 * e.Q3 ^ 2 * e.Q2 ^ 2) / (e.V * (D : ℝ)) := by
    simp only [physicalT0, one_div_div]
  refine ⟨by dsimp [physicalT0]; positivity, ?_⟩
  rw [hinv]
  calc
    _ ≤ e.Q1 * e.Q3 ^ 2 * e.Q2 ^ 2 := by
      apply (div_le_iff₀ hden).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hden1 hnum0
    _ ≤ _ := hnum

/-- The actual gcd feature licenses the literal quotient D/delta. -/
theorem actual_quotient_positive (e : MediumAtom) (Yb Ys : ℝ)
    {D delta g l : ℕ} (hD : 0 < D) {o : OuterIndex}
    (ho : o ∈ fixedSlice e Yb Ys D delta g l) : 0 < D / delta := by
  have hd : o.2.1.1.gcd D = delta := (mem_filter.mp ho).2.2.1
  have hdelta : 0 < delta := by
    rw [← hd, Nat.gcd_comm]
    exact Nat.gcd_pos_of_pos_left _ hD
  have hdvd : delta ∣ D := by rw [← hd]; exact Nat.gcd_dvd_right _ _
  exact Nat.div_pos (Nat.le_of_dvd hD hdvd) hdelta

private theorem source_f_data {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ}
    {F : ℝ} {s : Source}
    (hs : s ∈ carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))) :
    s.1 ≠ 0 ∧ (s.1.natAbs : ℝ) ≤ F := by
  obtain ⟨hr, hgate⟩ := mem_filter.mp hs
  have hf := (mem_product.mp hr).1
  have hlo : -F ≤ (s.1 : ℝ) := (Int.le_ceil (-F)).trans
    (by exact_mod_cast (mem_Icc.mp hf).1)
  have hhi : (s.1 : ℝ) ≤ F :=
    (show (s.1 : ℝ) ≤ ((Int.floor F : ℤ) : ℝ) by
      exact_mod_cast (mem_Icc.mp hf).2).trans (Int.floor_le F)
  exact ⟨hgate.1, by rw [natAbs_cast_real]; exact abs_le.mpr ⟨hlo, hhi⟩⟩

private theorem countScale_bounds {S : ℝ} (hS : (1 : ℝ) / 2 ≤ S) (upper : Bool) :
    1 ≤ tCountScale S upper ∧ tCountScale S upper ≤ 6 * S := by
  have hS0 : 0 ≤ S := by linarith
  have hSc : S ≤ (Nat.ceil S : ℝ) := Nat.le_ceil S
  have hn : 0 < Nat.ceil S := by
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero] at hSc
    linarith
  have hn1 : (1 : ℝ) ≤ (Nat.ceil S : ℝ) := by exact_mod_cast hn
  have hnupper : (Nat.ceil S : ℝ) < S + 1 := Nat.ceil_lt_add_one hS0
  cases upper with
  | false => change 1 ≤ (Nat.ceil S : ℝ) ∧ (Nat.ceil S : ℝ) ≤ 6*S; constructor <;> linarith
  | true =>
      change 1 ≤ ((2*Nat.ceil S : ℕ) : ℝ) ∧ ((2*Nat.ceil S : ℕ) : ℝ) ≤ 6*S
      push_cast
      constructor <;> linarith

/-- The exact natural block height is always in the count theorem's H>=1 domain. -/
theorem actual_tag_height_ge_one (tag : ℕ × Bool) :
    (1 : ℝ) ≤ (2 * _root_.P3ActualLogAdapterSourceOnly.Hnat tag.1 : ℕ) := by
  have hp : 0 < (2 : ℕ) ^ tag.1 := Nat.pow_pos (by norm_num)
  have hnat : 1 ≤ 2 * _root_.P3ActualLogAdapterSourceOnly.Hnat tag.1 := by
    dsimp [_root_.P3ActualLogAdapterSourceOnly.Hnat]
    omega
  exact_mod_cast hnat

/-- A true signed-f boundary: all source predicates, weights and output/nu
filters may still be retained. In particular no nonzero beta survives F<1. -/
theorem beta_zero_of_upper_f_lt_one (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    {F : ℝ} (hF : F < 1) (P : Source → Prop)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (zy : Output) :
    beta ((carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))).filter P)
      lambda omega zy = 0 := by
  have hempty : carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨hf, hb⟩ := source_f_data hs
    have hone : (1 : ℝ) ≤ s.1.natAbs := by
      exact_mod_cast (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hf))
    linarith
  simp only [hempty, filter_empty, beta, fiber, sum_empty]

/-- Actual fixed-feature geometry, with the original baseCarrier, signed
residue and both fixedUnit gates in hs. No upper bound on kappa is used.
The two returned lower bounds license the actual count theorem's G,R>=1.
Taking a witness of a nonempty fBlock and its owned full-carrier inclusion
instantiates this theorem; no row-descent or count-bound hypothesis is needed. -/
theorem actual_source_count_geometry
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (hsigma : 0 ≤ sigma)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    (upper negative : Bool) (H : ℕ) {s : Source}
    (hs : s ∈ carrier (g*l) (signedResidue negative e.residue)
      (baseCarrier e (D/delta)) H
      (Icc (Int.ceil (-scaleF e D g)) (Int.floor (scaleF e D g)))) :
    1 ≤ sourceFScale s ∧
      1 ≤ tCountScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper ∧
      0 < physicalT0 e D ∧
      1 + 2 * sourceFScale s *
        tCountScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper / physicalT0 e D ≤
          13 * e.scale ^ 7 := by
  have hx := admissible_geometry he hsigma
  have hx0 : 0 ≤ e.scale := zero_le_one.trans hx.1
  have hU : 1 ≤ e.U := he.1
  have hQ : 1 ≤ e.Q1 := he.2.2.1
  have hS : 1 ≤ e.Q2 := he.2.2.2.1
  have hS0 : 0 < e.Q2 := zero_lt_one.trans_le hS
  have hq := actual_quotient_positive e Yb Ys hD ho
  have hqR : (0 : ℝ) < (D/delta : ℕ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (D/delta : ℕ) := by exact_mod_cast hq
  let S := e.Q2 / ((D/delta : ℕ) : ℝ)
  have hSinner : 0 < S := div_pos hS0 hqR
  have hSinnerx : S ≤ e.scale := by
    calc
      _ ≤ e.Q2 := by
        apply (div_le_iff₀ hqR).mpr
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 hS0.le
      _ ≤ _ := hx.2.2.2.1
  obtain ⟨hraw, _⟩ := mem_filter.mp hs
  have ht : s.2.1.1 ∈ baseCarrier e (D/delta) :=
    (mem_product.mp (mem_product.mp (mem_product.mp hraw).2).1).1
  rw [baseCarrier_eq_factorCarrier_div e hS0.le hq] at ht
  have htS : s.2.1.1 ∈ factorCarrier S := ht
  obtain ⟨htlo, hthi⟩ := mem_Icc.mp htS
  have htloR : S ≤ (s.2.1.1 : ℝ) := (Nat.le_ceil S).trans (by exact_mod_cast htlo)
  have htpos : 0 < s.2.1.1 := by exact_mod_cast (hSinner.trans_le htloR)
  have ht1 : (1 : ℝ) ≤ s.2.1.1 := by exact_mod_cast htpos
  have htupper : (s.2.1.1 : ℝ) ≤ 2*S :=
    (show (s.2.1.1 : ℝ) ≤ (Nat.floor (2*S) : ℝ) by
      exact_mod_cast hthi).trans (Nat.floor_le (by positivity))
  have hhalf : (1 : ℝ)/2 ≤ S := by linarith
  have hRc := countScale_bounds hhalf upper
  have hRx : tCountScale S upper ≤ 6*e.scale :=
    hRc.2.trans (mul_le_mul_of_nonneg_left hSinnerx (by norm_num))
  obtain ⟨hf, hfF⟩ := source_f_data hs
  have hfn : s.1.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hf
  have hGabs : sourceFScale s ≤ (s.1.natAbs : ℝ) := by
    dsimp [sourceFScale]
    exact_mod_cast Nat.pow_log_le_self 2 hfn
  have hG1 : 1 ≤ sourceFScale s := by
    dsimp [sourceFScale]
    exact_mod_cast (one_le_pow₀ (show (1 : ℕ) ≤ 2 by norm_num) :
      1 ≤ (2 : ℕ) ^ Nat.log 2 s.1.natAbs)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hQ0 : 0 < e.Q1 := zero_lt_one.trans_le hQ
  have hden : 0 < (g : ℝ)*e.Q1*D := by positivity
  have hden1 : 1 ≤ (g : ℝ)*e.Q1*D := by
    have hfirst : 1 ≤ (g : ℝ)*e.Q1 := by
      simpa only [one_mul] using mul_le_mul hg1 hQ zero_le_one hgR.le
    simpa only [one_mul] using mul_le_mul hfirst hD1 zero_le_one (by positivity)
  have hFx : scaleF e D g ≤ e.scale := by
    calc
      _ ≤ e.U := by
        apply (div_le_iff₀ hden).mpr
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hden1
          (zero_le_one.trans hU)
      _ ≤ _ := hx.2.1
  have hGx : sourceFScale s ≤ e.scale := hGabs.trans (hfF.trans hFx)
  have hT := physicalT0_positive_and_inv_bound he hsigma hD
  have hGR : sourceFScale s * tCountScale S upper ≤ e.scale * (6*e.scale) :=
    mul_le_mul hGx hRx (zero_le_one.trans hRc.1) hx0
  have h2GR : 2*sourceFScale s*tCountScale S upper ≤ 12*e.scale^2 := by
    nlinarith [hGR]
  have hmain : 2*sourceFScale s*tCountScale S upper / physicalT0 e D ≤
      12*e.scale^7 := by
    calc
      _ = (2*sourceFScale s*tCountScale S upper) * (1/physicalT0 e D) := by ring
      _ ≤ (12*e.scale^2) * e.scale^5 :=
        mul_le_mul h2GR hT.2 (div_nonneg zero_le_one hT.1.le)
          (mul_nonneg (by norm_num) (sq_nonneg e.scale))
      _ = _ := by ring
  have hx7 : 1 ≤ e.scale^7 := one_le_pow₀ hx.1
  refine ⟨hG1, hRc.1, hT.1, ?_⟩
  change 1 + 2*sourceFScale s*tCountScale S upper / physicalT0 e D ≤ _
  linarith

/-- Public same-proof API for consumers in a separate module. -/
theorem actual_admissible_geometry {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (hsigma : 0 ≤ sigma) :
    1 ≤ e.scale ∧ e.U ≤ e.scale ∧ e.Q1 ≤ e.scale ∧
      e.Q2 ≤ e.scale ∧ e.Q3 ≤ e.scale :=
  admissible_geometry he hsigma

/-- Public same-proof API for the actual positive T0 and reciprocal bound. -/
theorem actual_physicalT0_positive_and_inv_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (hsigma : 0 ≤ sigma)
    {D : ℕ} (hD : 0 < D) :
    0 < physicalT0 e D ∧ 1 / physicalT0 e D ≤ e.scale ^ 5 :=
  physicalT0_positive_and_inv_bound he hsigma hD

end
end ImbalancedChen.Part3.ActualFixedFeatureCountGeometrySourceOnly
/-
HEADER-FREE SOURCEONLY APPEND; not a standalone importable module.
Required source order is recorded in the companion CP/manifest.
1. Existing actual M1/P1/M2/adapter/P3 sources.
2. Exact closed-T count license b9705fa4 (PROPOSED_NOT_YET_ACTUAL).
3. The sibling actual-fixed-feature-count-geometry candidate.
This body uses the real fBlock and countScale, without redefining either.
It closes the fBlock nonempty -> 13*x^7 application, keeping both signs,
the true upper-f cutoff and both h/t/source unit restrictions unchanged.
-/
namespace ImbalancedChen.Part3.ActualClosedTCountLicenseSourceOnly
noncomputable section
open Classical Finset
open GeneralDGateNormalization GeneralDActiveOuterEnergySourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualCompletedSquarePushforwardSourceOnly ActualM2FinitePoissonAdapterSourceOnly
open ActualFixedFeatureCountGeometrySourceOnly

theorem actual_nonempty_fBlock_count_geometry
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (hsigma : 0 ≤ sigma)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    (upper negative : Bool) (H : ℕ) (j : ℕ × Bool)
    (hblock : (fBlock (g*l) (signedResidue negative e.residue)
      (e.Q2 / ((D/delta : ℕ) : ℝ)) upper H (scaleF e D g) j).Nonempty) :
    1 ≤ fScale j.1 ∧
      1 ≤ countScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper ∧
      0 < physicalT0 e D ∧
      1 + 2 * fScale j.1 *
        countScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper / physicalT0 e D ≤
          13 * e.scale ^ 7 := by
  obtain ⟨s, hs⟩ := hblock
  have hfull := fBlock_subset_fullSource (g*l) (signedResidue negative e.residue)
    (e.Q2 / ((D/delta : ℕ) : ℝ)) upper H (scaleF e D g) j hs
  have hc := (mem_filter.mp hfull).1
  have hq := actual_quotient_positive e Yb Ys hD ho
  have hS0 : 0 ≤ e.Q2 := zero_le_one.trans he.2.2.2.1
  have hbase : s ∈ carrier (g*l) (signedResidue negative e.residue)
      (baseCarrier e (D/delta)) H
      (Icc (Int.ceil (-scaleF e D g)) (Int.floor (scaleF e D g))) := by
    rw [baseCarrier_eq_factorCarrier_div e hS0 hq]
    exact hc
  have hgeom := actual_source_count_geometry he hsigma Yb Ys hD hg ho
    upper negative H hbase
  have hlog : Nat.log 2 s.1.natAbs = j.1 :=
    congrArg Prod.fst (mem_filter.mp hs).2
  have hfscale : sourceFScale s = fScale j.1 := by
    dsimp [sourceFScale, fScale]
    rw [hlog]
  have htcount : tCountScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper =
      countScale (e.Q2 / ((D/delta : ℕ) : ℝ)) upper := by
    cases upper <;> rfl
  simpa only [hfscale, htcount] using hgeom

end
end ImbalancedChen.Part3.ActualClosedTCountLicenseSourceOnly
