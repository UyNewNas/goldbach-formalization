import ImbalancedChen.Part5OriginalH430PresievedBoxCatalog
import ImbalancedChen.P5OriginalH430AttachedMediumRanges

/-! The physically attached sign-dependent upper coefficient for each
enhanced U3/U4 Member. Attach its beta integer to group three in the
preassigned whole rough box, retaining the original coefficient value,
the original residual Q/B, and all four strict medium size conditions. -/
namespace ImbalancedChen.Part5OriginalH430AttachedUpperMember
noncomputable section
open scoped Classical BigOperators
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5Z.OriginalOrdinaryCommonBetaModel
open P5Z.OriginalOrdinaryResidualArithmeticFactor (roughWeight)
open Part5OriginalH430PhysicalRoots Part5OriginalH430RootSourceDictionary
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SameQHistoryCells Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback (memberCutoff)
open Part5OriginalH430EnhancedPhysicalGrid Part5OriginalH430EmittedWordBox
open Part5OriginalH430RootTentScreen Part5OriginalH430EnhancedMemberFactors Part5OriginalH430PresievedBoxCatalog
open P5OriginalH430AttachedMediumRanges

def coefficientAt {N : ℕ} (cap : ℕ) (Q rho ell : ℝ) (o : Occurrence N) :=
  let B := parentProduct o.current.old
  presievedCoefficient (N*B) cap ((N:ℝ)^rho) (memberCutoff Q o) (Q/(B:ℝ)) ((N:ℝ)^ell)

/-- No factor, nonzero native rough divisor, predetermined rank,
box, small-factor support, or medium size premise is supplied by the
caller. The same beta-cutoff level bounds group three across the box. -/
theorem upper_member_medium {N n m p cap h : ℕ} {k : Root} {t rho ell : ℝ}
    {key : RootKey n m} {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t key) (ho : o∈rootHistory N n k t p)
    (hen : rootSource k (physicalPrime N p)=.enhanced)
    (hkeep : ¬collar n (collarIndex n) (physicalPrime N p)) (hr : 0<rho) (hr' : rho≤frozenLeafCutoffFloor)
    (hell : 0≤ell) (hactive : coefficientAt cap (cellQ N n key.1) rho ell o h≠0) :
    let Q := cellQ N n key.1
    let B := parentProduct o.current.old
    let M := (N:ℝ)^ell
    let eta := radius (collarIndex n)
    let J := meshAt n rho
    ∃ (e d r : ℕ) (v : Fin (r+1)→ℕ) (j : Fin (r+1)→Fin (J+1)),
      h=e*d ∧ (e:ℝ)<M ∧ d∈roughUpper cap o Q rho ∧
      coefficientAt cap Q rho ell o h = roughWeight (N*B) cap ((N:ℝ)^rho) (memberCutoff Q o) (Q/(B:ℝ)) d *
        commonSmallWeight (N*B) cap ((N:ℝ)^rho) (memberCutoff Q o) (Q/(B:ℝ)) M d e ∧
      List.ofFn v=completeWord o d ∧ actualPrimeTupleLog N v∈logPrimeMeshCell 0 1 J j ∧
      ∀ x q alpha z A : ℝ, 1<x → x^q=(N:ℝ) → 1≤q → q≤1+eta/4 → q≤alpha → alpha≤1+eta/2 →
      0<z → z≤eta/8 → ell≤z/16 → 1≤A → A≤x^(1/3-z/2) →
      let w := fun i => (N:ℝ)^logPrimeMeshHi 0 1 J j i
      let out := groups w ((N:ℝ)^(o.current.node.physical.total+eta)) A
      let Q1 := (out.1.map w).prod
      let Q2 := (out.2.1.map w).prod
      let Q3 := M*(out.2.2.map w).prod
      let U := A*x^z
      let sigma := z/2000
      (out.1.map v).prod*(out.2.1.map v).prod*(e*(out.2.2.map v).prod)=B*h ∧
      ((out.1.map v).prod:ℝ)≤Q1 ∧ ((out.2.1.map v).prod:ℝ)≤Q2 ∧ ((e*(out.2.2.map v).prod:ℕ):ℝ)≤Q3 ∧
      Q1<U*x^(-sigma) ∧ U^2*Q2*Q3^2<x^(1-8*sigma) ∧
      (N:ℝ)^(7/32:ℝ)*U*Q1*Q2^5*Q3^2<x^(2-15*sigma) ∧
      U^(1+7/16:ℝ)*Q1*Q2^(5-7/16:ℝ)*Q3^(2+7/16:ℝ)<x^(2-15*sigma) := by
  dsimp only
  let Q := cellQ N n key.1
  let B := parentProduct o.current.old
  let M := (N:ℝ)^ell
  let R := Q/(B:ℝ)
  let Z := memberCutoff Q o
  let J := meshAt n rho
  obtain ⟨e,he,d,hd,hprod,heM,_⟩ := actualSmallRoughRho_ne_zero_factors
    (ordinaryRetainOdd R) (N*B) cap ((N:ℝ)^rho) Z M hactive
  have hR : 1<R := by
    have hb := (Finset.mem_filter.mp hp).1
    have H := rootHistory_support (by omega : 1<N) ht hu (precision_error hn) (original_band_prime hb)
      (original_band_geometry hN hb) ho
    rw [show R=cellQ N n key.1/(B:ℝ) from rfl,(original_fibre_geometry hN ht hu (precision_error hn) hp).1]
    exact (parentWindow_logs H.1).2.1
  let tail := letters o.path ++ d.primeFactorsList.reverse
  let v : Fin (tail.length+1)→ℕ := Fin.cons p tail.get
  have hw : List.ofFn v=completeWord o d := by
    rw [List.ofFn_succ,completeWord,occurrence_old ho,List.cons_append]
    simpa only [v,Fin.cons_zero,Fin.cons_succ,List.ofFn_get]
  obtain ⟨j,hj,H⟩ := presieved_upper_groups hN hn ht hu hp ho hen hkeep hr hr' hd v hw
  refine ⟨e,d,tail.length,v,j,hprod,heM,hd,?_,hw,hj,?_⟩
  · rw [hprod]
    exact presieved_coefficient_value hR he hd
  · intro x q alpha z A hx hscale hq hq' halpha halpha' hz hz' hell' hA hA'
    dsimp only
    let w := fun i => (N:ℝ)^logPrimeMeshHi 0 1 J j i
    let D := (N:ℝ)^(o.current.node.physical.total+radius (collarIndex n))
    let out := groups w D A
    have hh := H x q alpha z A hx hscale hq hq' halpha halpha' hz hz' hA hA'
    obtain ⟨heq,ha,h2,h3,h4⟩ := hh
    have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hM : 0<M := Real.rpow_pos_of_pos hNpos _
    have hwpos (i) : 0<w i := Real.rpow_pos_of_pos hNpos _
    have hgpos (s : List (Fin (tail.length+1))) : 0<(s.map w).prod :=
      List.prod_pos (fun a ha => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha; exact hwpos i)
    have hedge : radius (collarIndex n)≤1/100 := min_le_left _ _
    have hq2 : q≤2 := by linarith only [hq',hedge]
    have hsize : M≤x^(z/8) := by
      change (N:ℝ)^ell≤x^(z/8)
      rw [←hscale,←Real.rpow_mul (zero_lt_one.trans hx).le]
      exact Real.rpow_le_rpow_of_exponent_le hx.le (by nlinarith only [mul_le_mul_of_nonneg_right hq2 hell,hell'])
    have mono := attached_medium_ranges hx hz halpha (zero_lt_one.trans_le hA) (hgpos out.1)
      (hgpos out.2.1) (hgpos out.2.2) hM hsize ha h2 h3 h4
    have hvpos (i : Fin (tail.length+1)) : 0<v i := by
      have hpr := (native_word_support hN hn ht hu hp ho hen true (by simp)
        (rough_rank hN hn ht hu hp ho hen hr hr' hd).1).2.2.2.1
      exact (hpr _ (by rw [←hw]; exact List.mem_ofFn.mpr ⟨i,rfl⟩)).pos
    have hcoord (i) : (v i:ℝ)≤w i := by
      rw [←actualPrimeTupleLog_rpow (by omega : 1<N) v hvpos i]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
        (mem_logPrimeMeshCell.mp hj i).2.le
    have endpts := (same_groups_all_tuples w D A v hcoord).2
    refine ⟨?_,endpts.1,endpts.2.1,?_,mono.1,mono.2.1,?_,mono.2.2.2⟩
    · change (out.1.map v).prod*(out.2.1.map v).prod*(e*(out.2.2.map v).prod)=B*h
      rw [hprod,show (out.1.map v).prod*(out.2.1.map v).prod*(e*(out.2.2.map v).prod)=
        e*((out.1.map v).prod*(out.2.1.map v).prod*(out.2.2.map v).prod) by ring,heq]
      ring
    · rw [Nat.cast_mul]
      exact mul_le_mul heM.le endpts.2.2 (Nat.cast_nonneg _) hM.le
    · simpa only [hscale] using mono.2.2.1

end
end ImbalancedChen.Part5OriginalH430AttachedUpperMember
