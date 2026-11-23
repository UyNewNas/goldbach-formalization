import ImbalancedChen.Part5OriginalH430MemberAttachedPrimeCarrier
import ImbalancedChen.P4BOriginalAllWidthProperPowers

/-! Reuse the existing arbitrary-retention proper-power and Fourier estimates
on the actual H430 residual coefficient. Keep the two integer chart slots,
the global additive numerator N and the original half-product weight. -/
namespace ImbalancedChen.Part5OriginalH430RetainedAnalyticReserves
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430RootSourceDictionary Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430OwnedRootCounts Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SameQHistoryCells
open Part5OriginalH430RetainedRejectedPayment (retainedEdge)
open Part5OriginalH430AttachedUpperMember (coefficientAt)
open Part5OriginalH430MemberAttachedPrimeCarrier (memberModuli memberRetention retained_residual_binding)
open P4BOuterRampRoughness (baseline)
open P4BArbitraryWidthUpperPairProfile (licence)
open P4BActualSmoothHyperbolaCorrection (actualActiveUpperCap actual_active_modulus_mem_Icc)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (properPowerReserve)
open P5Z.ProperPowerPhysicalPolynomialPayment (physicalRho)
open P4BOriginalAllWidthProperPowers (eventually_all_width_properPower_sum_norm)
open P4BOriginalUpperFourierTailPaid (retainedUpperAtlas exists_eventual_original_upper_fourier_tail_paid)
open P4BArbitraryWidthUpperBlockGeometry (countingScale)
open P5Z.CompleteProductTailDivisorBudgets (logScale)

private theorem a_pos : 0<a := by norm_num [a]

/-- The two-integer-chart proper-power correction now takes the actual
H430 signed residual function, on its actual displayed finite moduli.
The threshold is uniform even in the marked root and its retention. -/
theorem eventually_retained_properPowers (nu : ℝ) (hnu : 0<nu) (l : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠ N : ℕ in atTop, ∀ {n m p cap : ℕ} {k : Root} {t : ℝ} {key : RootKey n m} {o : Occurrence N},
    111≤n → 0≤t → t≤1/12 → p∈rootFibre N n m k t key → o∈rootHistory N n k t p →
    rootSource k (physicalPrime N p)=.enhanced → o.path.all retainedEdge=true →
    ∀ (b kappa w : ℝ) (hb : 0<b), 0<kappa → ∀ (hw : 0<w) (hg : 2*w≤baseline b kappa-nu*(a/nu))
    (K : ℕ) (trim beta : ℝ), nu*beta^2≤a → nu*beta≤1/1000 →
    let Q := cellQ N n key.1
    (∑ js ∈ chartBank N 2, ‖properPowerReserve (licence hb hnu (div_pos a_pos hnu) hw hg N) K N N trim
      (memberModuli cap Q (nu*beta^2) o) (fun d=>(coefficientAt cap Q (nu*beta^2) (nu*beta) o d:ℂ)) js‖) ≤
      eps*(N:ℝ)/(Real.log (N:ℝ))^l := by
  filter_upwards [eventually_all_width_properPower_sum_norm nu (a/nu) (599/1000) hnu (div_pos a_pos hnu)
    (by norm_num) (by norm_num) l eps heps,eventually_ge_atTop (2:ℕ)] with N H hN
  intro n m p cap k t key o hn ht ht' hp ho hen hret b kappa w hb hk hw hg K trim beta hu he
  have eqs := retained_residual_binding (cap:=cap) hN hn ht ht' hp ho hen hret hnu hu he
  dsimp only
  rw [eqs.1,eqs.2.1]
  exact H b kappa w hb hk hw hg K trim beta _ _ eqs.2.2

/-- The already paid arbitrary-width Fourier tail accepts the same
residual function and the very same retention on its retained atlas.
The threshold precedes the independent choices of Member, width, cap,
truncation and integer accuracy, including all admissible beta values. -/
theorem exists_retained_fourier_tail : ∃ C : ℝ, 0≤C ∧ ∀ b kappa nu : ℝ,
    ∀ (hb : 0<b), b≤1 → 0<kappa → ∀ (hnu : 0<nu), ∀ᶠ N : ℕ in atTop,
    ∀ {n m p cap : ℕ} {k : Root} {t : ℝ} {key : RootKey n m} {o : Occurrence N},
    111≤n → 0≤t → t≤1/12 → p∈rootFibre N n m k t key → o∈rootHistory N n k t p →
    rootSource k (physicalPrime N p)=.enhanced → o.path.all retainedEdge=true →
    ∀ (w : ℝ) (hw : 0<w) (hg : 2*w≤baseline b kappa-nu*(a/nu)) (K l : ℕ) (trim beta : ℝ),
    nu*beta^2≤a → nu*beta≤1/1000 →
    let Q := cellQ N n key.1
    ‖(Part3.primeProductSignedError 2 N N (memberModuli cap Q (nu*beta^2) o)
      (coefficientAt cap Q (nu*beta^2) (nu*beta) o)
      (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) w):ℂ) -
      retainedUpperAtlas hb hnu (div_pos a_pos hnu) hw hg N K trim beta (memberRetention Q o) (fun _=>cap) l‖ ≤
      (C/w^24)*(N:ℝ)/logScale (countingScale N)^(l+3) := by
  obtain ⟨C,hC,H⟩ := exists_eventual_original_upper_fourier_tail_paid (599/1000:ℝ) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro b kappa nu hb hb' hk hnu
  filter_upwards [H b kappa nu (a/nu) hb hb' hk hnu (div_pos a_pos hnu),eventually_ge_atTop (2:ℕ)] with N h hN
  intro n m p cap k t key o hn ht ht' hp ho hen hret w hw hg K l trim beta hu he
  have eqs := retained_residual_binding (cap:=cap) hN hn ht ht' hp ho hen hret hnu hu he
  let f := memberRetention (cellQ N n key.1) o
  let D := ⌊(N:ℝ)^(599/1000:ℝ)⌋₊
  have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hpow := Real.one_le_rpow hNr (show (0:ℝ)≤599/1000 by norm_num)
  have hD : 1≤D := (Nat.le_floor_iff (zero_le_one.trans hpow)).mpr (by simpa using hpow)
  dsimp only
  rw [eqs.1,eqs.2.1]
  apply h w hw hg K D l trim beta f _ hD (Nat.floor_le (zero_le_one.trans hpow))
  intro q hq ha
  exact (Nat.le_floor_iff (zero_le_one.trans hpow)).mpr
    ((Nat.cast_le.mpr (Finset.mem_Icc.mp (actual_active_modulus_mem_Icc nu (a/nu) beta f (fun _=>cap) N q hq ha)).2).trans eqs.2.2)

end
end ImbalancedChen.Part5OriginalH430RetainedAnalyticReserves
