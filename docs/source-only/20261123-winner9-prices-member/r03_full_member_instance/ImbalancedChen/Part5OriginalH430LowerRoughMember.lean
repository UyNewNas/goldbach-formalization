import ImbalancedChen.Part5OriginalH430PresievedBoxCatalog
import ImbalancedChen.ActualLowerSmallRoughAttachment

/-! The even-retained ordinary lower rough term attaches the opposite
beta signs. At its physical comparison s>=2 the first-prime square and
the genuine native lower admissibility follow internally. -/
namespace ImbalancedChen.Part5OriginalH430LowerRoughMember
noncomputable section
open scoped Classical BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5Z.OriginalOrdinaryBetaRegroup
open P5Z.OriginalOrdinaryCommonBetaModel (roughProduct_eq_universe_prod)
open Part5OriginalH430PhysicalRoots Part5OriginalH430RootSourceDictionary
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SameQHistoryCells Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback (memberCutoff)
open Part5OriginalH430EnhancedPhysicalGrid Part5OriginalH430EmittedWordBox Part5OriginalH430EnhancedMemberFactors
open Part5OriginalH430HistoryQuotientCounts (history_integer_roughness)

def retainEven (R : ℝ) (w : List ℕ) := decide (ordinaryRosserPrefixAdmissible true R w)

/-- The actual rough carrier gives the true lower signed native term.
It suffices that all carrier primes lie strictly below the full level.
The presieve boundary can coincide with the physical cutoff. -/
theorem lower_rough_native {N cap d : ℕ} {u Z R : ℝ} (hR : 1<R) (hZ : Z≤R) (hu : u≤Z)
    (hd : d∈fixedEvenRoughSupport (retainEven R) N cap u Z) :
    actualSmallRosserMinus N cap Z R d≠0 := by
  let ps := roughPrimeUniverse N cap u Z
  change d∈firstExitRetainedModuli (ordinaryParityRosserPolicy true R) ps at hd
  have hs := roughPrimeUniverse_pairwise_gt N cap u Z
  have hp : ∀ p∈ps,p.Prime := fun _ h=>mem_roughPrimeUniverse_prime h
  rw [ordinaryParityRosserRetainedModuli_eq true R hR ps hs hp
    (fun _ _ h => (mem_roughPrimeUniverse_upper h).trans_le hZ)] at hd
  have ha := (mem_ordinaryRosserRetainedModuli_iff true R hR ps hs hp d).mp hd
  have hsupp : d∈roughSupport N cap u Z := by
    change d∈(roughProduct N cap u Z).divisors
    rw [roughProduct_eq_universe_prod]
    exact ha.1
  have hone : 1∈actualSmallRosserSupport N cap u :=
    Nat.mem_divisors.mpr ⟨one_dvd _,actualSmallPrimeProduct_ne_zero N cap u⟩
  have htotal : d∈actualSmallRosserSupport N cap Z := by
    rw [nativeSupport_eq_products N cap hu]
    exact Finset.mem_image.mpr ⟨(1,d),Finset.mem_product.mpr ⟨hone,hsupp⟩,one_mul _⟩
  change lowerWeight (actualSmallPrimeProduct N cap Z) R d≠0
  rw [lowerWeight_apply,if_pos ⟨htotal,ha.2.1,ha.2.2⟩]
  exact pow_ne_zero _ (by norm_num)

def coefficientAt {N : ℕ} (cap : ℕ) (Q rho ell : ℝ) (o : Occurrence N) :=
  let B := parentProduct o.current.old
  actualLowerSmallRoughRho (retainEven (Q/(B:ℝ))) (N*B) cap ((N:ℝ)^rho) (memberCutoff Q o) ((N:ℝ)^ell)

/-- Exact nonzero signed lower attachment at an original Member, with
the lower native d and both true square lists. An adopted nonzero
rough coefficient can be positive or negative; the required beta
weight is recovered from precisely that coefficient's sign. -/
theorem lower_attached_native_word {N n m p cap h : ℕ} {k : Root} {t rho ell : ℝ}
    {c : RootKey n m} {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (hen : rootSource k (physicalPrime N p)=.enhanced)
    (hs : 2≤o.current.node.physical.argument) (hr : rho≤frozenLeafCutoffFloor)
    (hactive : coefficientAt cap (cellQ N n c.1) rho ell o h≠0) :
    let Q := cellQ N n c.1
    let B := parentProduct o.current.old
    let R := Q/(B:ℝ)
    let Z := memberCutoff Q o
    let u := (N:ℝ)^rho
    let M := (N:ℝ)^ell
    let F := fixedEvenRoughCoefficient (retainEven R) (N*B) cap u Z
    ∃ e d : ℕ, h=e*d ∧ (e:ℝ)<M ∧ SmallPrimeSupportedAt u e ∧ RoughPrimeSupportedAt u d ∧
      coefficientAt cap Q rho ell o h =
        signAttachedCoefficient (F d) (actualSmallRosserPlus (N*B) cap u M e) (actualSmallRosserMinus (N*B) cap u M e) ∧
      nativeCoefficient false N cap B Q o.current.node.physical.argument d≠0 ∧
      actualDwellSupport Q (completeWord o d) ∧ actualDwellSupport (Q/(p:ℝ)) (completeWord o d).tail ∧
      (completeWord o d).prod=B*d ∧ (∀ q∈completeWord o d,q.Prime) ∧ (completeWord o d).head?=some p := by
  dsimp only
  let Q := cellQ N n c.1
  let B := parentProduct o.current.old
  let R := Q/(B:ℝ)
  let u := (N:ℝ)^rho
  let Z := memberCutoff Q o
  let M := (N:ℝ)^ell
  obtain ⟨e,he,d,hd,hprod,heM,_⟩ := actualLowerSmallRoughRho_ne_zero_factors
    (retainEven R) (N*B) cap u Z M hactive
  have hb := (Finset.mem_filter.mp hp).1
  have H := rootHistory_support (by omega : 1<N) ht hu (precision_error hn) (original_band_prime hb)
    (original_band_geometry hN hb) ho
  have hQ := (original_fibre_geometry hN ht hu (precision_error hn) hp).1
  have hR : 1<R := by
    rw [show R=cellQ N n c.1/(B:ℝ) from rfl,hQ]
    exact (parentWindow_logs H.1).2.1
  have huZ : u≤Z := by
    change (N:ℝ)^rho ≤ memberCutoff (cellQ N n c.1) o
    rw [hQ]
    exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega)) hr).trans
      (history_integer_roughness hN ht hu (precision_error hn) hb ho).2.1
  have hZR : Z≤R := by
    change R^(1/o.current.node.physical.argument)≤R
    exact (Real.rpow_le_rpow_of_exponent_le hR.le ((div_le_one (by linarith only [hs])).mpr
      (by linarith only [hs]))).trans_eq (Real.rpow_one R)
  have hnative := lower_rough_native hR hZR huZ hd
  have hword := native_word_support hN hn ht hu hp ho hen false (fun _=>hs) hnative
  refine ⟨e,d,hprod,heM,actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ he,
    fixedEvenRoughSupport_roughPrimeSupportedAt _ _ _ _ _ hd,?_,hnative,hword⟩
  rw [hprod]
  exact smallRoughRho_mul
    (fun _ h=>actualSmallRosserSupport_smallPrimeSupportedAt (N*B) cap u h)
    (fun _ h=>fixedEvenRoughSupport_roughPrimeSupportedAt (retainEven R) (N*B) cap u Z h)
    (fixedEvenRoughCoefficient (retainEven R) (N*B) cap u Z)
    (actualSmallRosserPlus (N*B) cap u M) (actualSmallRosserMinus (N*B) cap u M) he hd

end
end ImbalancedChen.Part5OriginalH430LowerRoughMember
