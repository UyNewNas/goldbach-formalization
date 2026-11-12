import ImbalancedChen.P4BOriginalHighRankMediumScale
import ImbalancedChen.P4AOriginalFiniteFallbackAllHighAtoms

/-! The canonical representative of an active high-rank modulus has at least
three rough primes.  For a high first rough prime, the native three endpoint
groups meet the four numerical medium inequalities on the selected HB cell. -/
namespace ImbalancedChen.P4BOriginalHighRankMediumHeads
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.ActualHBMediumBranchPartition (firstMedium)
open P4BUpperPairOrderedRowGeometry (integerProfile)
open P4BOriginalHighRankMotherScale (completeScale)
open P4BOriginalHighRankMediumScale (eventually_live_medium)
open P4BOuterRampRoughness (baseline)
open P4BOriginalAllRankClassicalRange (wholeHigh)
open P4BOriginalFiniteSmoothCount (coefficient)
open P4BOriginalRankTwoChartPayment (tau)
open P4AOriginalFiniteFallbackCommonGroups (gap groupsAt)
open P4AOriginalFiniteFallbackPhysicalSelected (word pick witnesses)
open P4AOriginalFiniteFallbackSelectedMask (front)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87RawChronology (cutoff)
open P4AHeldTaggedCompilerSupport (J0)
open P4AUpperTaggedParityCompiler (rawSupport primeWordLabel)
open P4AFiniteFallbackLowRankRho (retain)

theorem active_word (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (ell : ℝ)
    {v : ℕ} (hv : v∈wholeHigh m r n e q a omega k N ell)
    (hc : coefficient m r n e q a omega k N ((N:ℝ)^ell) v≠0) :
    let f := retain m r n e q a omega N
    let W := (N:ℝ)^omega
    let T := tau m e q a k
    ∃ h d : ℕ,h∈actualSmallRosserSupport N N W ∧
      d∈P4AUpperTaggedParityCompiler.universe N N W (cutoff N) ∧ h*d=v ∧ (h:ℝ)<(N:ℝ)^ell ∧
      P4AUpperTaggedParityCompiler.coefficient f (fun _ => []) N N W (cutoff N) T d≠0 ∧
      let u := pick f N N W (cutoff N) T (primeWordLabel N T d)
      u∈rawSupport f N N W (cutoff N) ∧ word N T u=word N T d ∧
      ∃ p : Fin 3→ℕ,∃ tail : List ℕ,u.primeFactorsList.reverse=front p tail := by
  let f := retain m r n e q a omega N
  let W := (N:ℝ)^omega
  let T := tau m e q a k
  obtain ⟨hvQ,hnl⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨⟨h,d⟩,hm,hprod⟩ := Finset.mem_image.mp hvQ
  obtain ⟨hh,hd⟩ := Finset.mem_product.mp hm
  let c := P4AUpperTaggedParityCompiler.coefficient f (fun _ => []) N N W (cutoff N) T
  have H := P4AUpperTaggedBetaAttachment.rho_at_product f (fun _ => []) N N W (cutoff N) T ((N:ℝ)^ell) hh hd
  have hact : c d*(if 0≤c d then actualSmallRosserPlus N N W ((N:ℝ)^ell) h
      else actualSmallRosserMinus N N W ((N:ℝ)^ell) h)≠0 := by
    rw [←H,hprod]; exact hc
  obtain ⟨hcoef,hbeta⟩ := mul_ne_zero_iff.mp hact
  have hsmall : (h:ℝ)<(N:ℝ)^ell := by
    split_ifs at hbeta
    · exact (actualSmallRosserPlus_active hbeta).2.1
    · exact (actualSmallRosserMinus_active hbeta).2.1
  have hlen : 3≤d.primeFactorsList.length := by
    by_contra! bad
    exact hnl (P4AFiniteFallbackLowRankRho.mem_activeLow_of_decomposition m r n e q a omega N T ell
      hc hh hd hprod (by omega))
  obtain ⟨w,hw,_,_,hJ⟩ := P4AUpperTaggedParityCompiler.active_has_raw_witness f (fun _ => []) N N W
    (cutoff N) T hcoef
  let V := witnesses f N N W (cutoff N) T (primeWordLabel N T d)
  have hne : V.Nonempty := ⟨w,Finset.mem_filter.mpr ⟨hw,hJ⟩⟩
  let u := pick f N N W (cutoff N) T (primeWordLabel N T d)
  have hu : u∈V := by change (if h : V.Nonempty then V.min' h else 1)∈V; rw [dif_pos hne]; exact V.min'_mem hne
  obtain ⟨hu0,hmatch⟩ := Finset.mem_filter.mp hu
  have hword : word N T u=word N T d := by
    simpa only [word,P4AOriginalFiniteFallbackNaturalEndpoints.tag,primeWordLabel,
      P2LowerFiniteCellRounding.label,List.map_map,Function.comp_def] using congrArg (List.map Int.toNat) hmatch
  have hr : 3≤u.primeFactorsList.reverse.length := by
    have heq := congrArg List.length hword
    simp only [word,List.length_map,List.length_reverse] at heq
    simpa only [List.length_reverse] using heq.symm ▸ hlen
  refine ⟨h,d,hh,hd,hprod,hsmall,hcoef,hu0,hword,?_⟩
  generalize hL : u.primeFactorsList.reverse=xs at hr ⊢
  cases xs with
  | nil => simp at hr
  | cons x xs =>
    cases xs with
    | nil => simp at hr
    | cons y xs =>
      cases xs with
      | nil => simp at hr
      | cons z tail => exact ⟨![x,y,z],tail,rfl⟩

private theorem groups_nonneg (m N : ℕ) (D : P5OriginalCommonRefinedConstructor.OriginalData)
    (omega T x U eta : ℝ) (p : Fin 3→ℕ) (J : List ℕ) :
    let abc := groupsAt m N D omega T x U eta p J
    0≤abc.1 ∧ 0≤abc.2.1 := by
  unfold groupsAt
  split <;> simp only [P4AOriginalFiniteFallbackPhysicalSelected.upperGroups,
    P4BUpperSelectedBoxCapacity.endpoints,P4BUpperSelectedBoxCapacity.endpoint_eq_cast] <;>
    exact ⟨Nat.cast_nonneg _,Nat.cast_nonneg _⟩

/-- All four inequalities on the original complete x and actual target N.
The selector and raw representative are those of the physical rectangle.
The remaining low-head and spectral analytic estimates are separate. -/
theorem eventually_high_heads (K : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa) (hkz : kappa≤zeta/10000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (u v cj ck : ℕ) (bs : Fin (u+v)→Block) (y : Fin (u+v)→ℕ) (i : Fin (u+v)),
      y∈rectangle bs → integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0 →
      firstMedium (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck])
        (List.ofFn bs)=some i.val →
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      0≤e → 0<omega → 0≤ell → 2*ell≤zeta/16 → zeta≤gap m (data e q a) →
      tau m e q a k*((J0 omega:ℝ)+1)≤zeta →
      ∀ j∈wholeHigh m r n e q a omega k N ell,
        coefficient m r n e q a omega k N ((N:ℝ)^ell) j≠0 →
      let f := retain m r n e q a omega N
      let W := (N:ℝ)^omega
      let T := tau m e q a k
      let x := completeScale bs y i
      let U := (lower (bs i):ℝ)
      ∃ h d : ℕ,h*d=j ∧ h∈actualSmallRosserSupport N N W ∧
        d∈P4AUpperTaggedParityCompiler.universe N N W (cutoff N) ∧
        let w := pick f N N W (cutoff N) T (primeWordLabel N T d)
        ∃ p : Fin 3→ℕ,∃ tail : List ℕ,w.primeFactorsList.reverse=front p tail ∧
        (VariableEnvelope.mu<actualPrimeTupleLog N p 0 →
          let abc := groupsAt m N (data e q a) omega T x U zeta p (word N T d)
          let Q3 := abc.2.2*x^(2*ell)
          (h:ℝ)≤x^(2*ell) ∧ abc.1<U*x^(-zeta/100) ∧ U^2*abc.2.1*Q3^2<x^(1-8*(zeta/100)) ∧
          (N:ℝ)^(7/32:ℝ)*U*abc.1*abc.2.1^5*Q3^2<x^(2-15*(zeta/100)) ∧
          U^(23/16:ℝ)*abc.1*abc.2.1^(73/16:ℝ)*Q3^(39/16:ℝ)<x^(2-15*(zeta/100))) := by
  have hkz' : kappa≤zeta := by linarith
  filter_upwards [eventually_live_medium K hz hz1 hk hkz' ht ht1,eventually_ge_atTop (2:ℕ)] with N H hN
  intro b kap s hb hp hs hg u v cj ck bs y i hy hw hsel m r n e q a omega k ell he ho hel hsmall hgap hbud
    j hj hc
  let x := completeScale bs y i
  let U := (lower (bs i):ℝ)
  let T := tau m e q a k
  obtain ⟨hx,hlo,hhi,hU,hU',_,_⟩ := H hb hp hs hg u v cj ck bs y i hy hw hsel
  obtain ⟨h,d,hh,hd,hprod,hL,hcoef,hwraw,hword,p,tail,hfront⟩ :=
    active_word m r n e q a omega k N ell hj hc
  refine ⟨h,d,hprod,hh,hd,p,tail,hfront,?_⟩
  intro hhead
  have htau : 0<T := div_pos (logPrimeMeshStep_pos (by norm_num) _) (by positivity)
  have hhig : (N:ℝ)≤x^(1+zeta) := hhi.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  have Hnum := P4AOriginalFiniteFallbackCommonGroups.high m n N N _ d h (width r) omega _ T ell (data e q a)
    (width_pos r) (by change 0≤e; exact he) (by omega) ho htau hz hgap hbud hwraw hword hL hel hsmall
    p tail hfront hhead hx hkz' hlo hhig hU hU'
  obtain ⟨hbeta,h1,h2,h3,h4⟩ := Hnum
  refine ⟨hbeta,h1,h2,?_,h4⟩
  let abc := groupsAt m N (data e q a) omega T x U zeta p (word N T d)
  let Q3 := abc.2.2*x^(2*ell)
  have hh' : (N:ℝ)^(7/32:ℝ)≤x^(7*(1+3*kappa)/32) := by
    calc
      _≤(x^(1+kappa))^(7/32:ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg N) hhi (by norm_num)
      _=x^((1+kappa)*(7/32:ℝ)) := (Real.rpow_mul (zero_lt_one.trans hx).le _ _).symm
      _≤_ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  obtain ⟨hQ1,hQ2⟩ := groups_nonneg m N (data e q a) omega T x U zeta p (word N T d)
  have h0 : 0≤U := Nat.cast_nonneg _
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh' h0) hQ1) (pow_nonneg hQ2 5)) (sq_nonneg Q3)) h3

end
end ImbalancedChen.P4BOriginalHighRankMediumHeads
