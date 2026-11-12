import ImbalancedChen.P4AOriginalFiniteFallbackCount
import ImbalancedChen.P4AFallbackCanonicalBanks
import ImbalancedChen.P4BSmoothOuterRampRoughness
import ImbalancedChen.P4BIntegerShiftOuterCarrier

/-! Exact positive outer count for the finite fallback policy, the enlarged
fifth bank and the whole ordered third. The full labelled product stays
in the integer-shift identity even when it is at least the target. -/
namespace ImbalancedChen.P4BOriginalFiniteSmoothCount
noncomputable section
open scoped Classical BigOperators
open Part3 (labelledPrimeTuples primeProductSignedError)
open P4B (smoothPhysicalPairOuterRamp)
open P4BLabelledOuterPushforward (productCarrier productWeight)
open P4BOuterRampRoughness (baseline)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFull87CompiledCounting (moduli compiled_modulus_dvd)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalNewFifthUnion (data)

abbrev Q (omega : ℝ) (N : ℕ) := moduli N ((N : ℝ)^omega)

abbrev coefficient (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N : ℕ) (L : ℝ) :=
  P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N
    (alignedWidth (jointIndex (bank m) (data e q a).m) k) L

abbrev weight (b kappa s : ℝ) (N : ℕ) :=
  smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) s

def mass (b kappa s : ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ labelledPrimeTuples 2 N, weight b kappa s N t

theorem mass_nonneg (b kappa s : ℝ) (N : ℕ) : 0 ≤ mass b kappa s N :=
  Finset.sum_nonneg (fun t _ => (P4B.smoothPhysicalPairOuterRamp_bounds b N _ s t).1)

/-- A nonzero product fibre has two actual prime factors above the
strict sieve cutoff. Every displayed modulus of the rectangle divides
that sieve product, including moduli at which its coefficient vanishes. -/
theorem coprime_on_outer {b kappa s omega : ℝ} {N x d : ℕ}
    (hb : 0<b) (hN : 2≤N) (hs : 0<s)
    (hgap : 2*s≤baseline b kappa-19/96) (homega : omega≤19/96)
    (hx : productWeight N (weight b kappa s N) x≠0) (hd : d∈Q omega N) :
    Nat.Coprime x d := by
  have hbase : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hwz : (N:ℝ)^omega≤cutoff N :=
    Real.rpow_le_rpow_of_exponent_le hbase homega
  apply (P4BOuterRampRoughness.coprime_sieveProduct_ceil_of_prime_divisor_rough
    N x (cutoff N) ?_).of_dvd_right (compiled_modulus_dvd N _ hwz hd)
  intro ell hell hdiv
  exact P4BSmoothOuterRampRoughness.smooth_physical_ramp_productWeight_nonzero_prime_divisor_rough
    hb hN hs hgap hx hell hdiv

theorem outer_correction_eq_zero {b kappa s omega : ℝ} {N : ℕ}
    (hb : 0<b) (hN : 2≤N) (hs : 0<s)
    (hgap : 2*s≤baseline b kappa-19/96) (homega : omega≤19/96)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ) (L : ℝ) :
    let X := productCarrier N
    let W := productWeight N (weight b kappa s N)
    let rho := coefficient m r n e q a omega k N L
    (∑ d ∈ Q omega N,rho d*((finiteCoprimeMass X W d-finiteSourceMass X W)/
      (Nat.totient d:ℝ)))=0 := by
  dsimp only
  apply P4BOuterCoprimeElimination.signed_coprime_sum_eq_zero_of_active_weight_support
  intro d hd _ x _ hx
  exact coprime_on_outer hb hN hs hgap homega hx hd

/-- The original smooth rank-two PP expression is the only signed
discrepancy on the right. This finite inequality requires no density,
smooth PP, boundary-mass or historical attachment equality premise. -/
theorem realB_le_smooth_signed {b kappa s : ℝ} {N : ℕ}
    (hb : 0<b) (hb1 : b<1) (hN : 2≤N) (hs : 0<s)
    (hgap : 2*s≤baseline b kappa-19/96)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ)
    (nu beta : ℝ) (hnu : 0<nu) (hbpos : 0<beta) (hbmax : beta≤1)
    (hw : nu*beta^2≤19/96) :
    let omega := nu*beta^2
    let rho := coefficient m r n e q a omega k N ((N:ℝ)^(nu*beta))
    (RealB b N:ℝ)≤mass b kappa s N*physicalDensitySum (Q omega N) rho+
      primeProductSignedError 2 N N (Q omega N) rho (weight b kappa s N)+
      (Nat.ceil (cutoff N):ℝ)+(manuscriptHalfProductCutoff kappa N+1) := by
  let omega := nu*beta^2
  let L := (N:ℝ)^(nu*beta)
  let T := manuscriptHalfProductCutoff kappa N
  let V := weight b kappa s N
  let rho := coefficient m r n e q a omega k N L
  have hbase : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hT : 0<T := mul_pos (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans hbase) _)
  have hwL : (N:ℝ)^omega≤L := by
    apply Real.rpow_le_rpow_of_exponent_le hbase.le
    apply mul_le_mul_of_nonneg_left _ hnu.le
    simpa only [sq,one_mul] using mul_le_mul_of_nonneg_right hbmax hbpos.le
  have hL : 1<L := Real.one_lt_rpow hbase (mul_pos hnu hbpos)
  have hwz : (N:ℝ)^omega≤cutoff N :=
    Real.rpow_le_rpow_of_exponent_le hbase.le hw
  have hz : cutoff N≤(N:ℝ) := by
    simpa only [cutoff,Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase.le (show (19/96:ℝ)≤1 by norm_num)
  obtain ⟨hsource,houter⟩ :=
    P4BLabelledOuterPushforward.actual_outer_pushforward_majorant b N T V
      (fun t _ => (P4B.smoothPhysicalPairOuterRamp_bounds b N T s t).1)
      (fun _ ht => P4B.actual_W_le_smoothPhysicalPairOuterRamp hbase hT hs ht)
  have hh := P4B.RealB_cast_le_same_rho_integer_outer_main_add_errors N (Nat.ceil (cutoff N))
    (productCarrier N) (Q omega N) (productWeight N V) rho hb1 hT.le hsource houter
    (P4AOriginalFiniteFallbackCount.upper_majorant (bank m) r n e q a omega N _ L
      hL hwL hwz hz)
  have hzero := outer_correction_eq_zero hb hN hs hgap hw m r n e q a k L
  dsimp only at hzero
  rw [hzero,add_zero,P4BLabelledOuterPushforward.signed_productWeight_eq_primeProductSignedError,
    P4BLabelledOuterPushforward.finiteSourceMass_eq_labelled] at hh
  exact hh

end
end ImbalancedChen.P4BOriginalFiniteSmoothCount
