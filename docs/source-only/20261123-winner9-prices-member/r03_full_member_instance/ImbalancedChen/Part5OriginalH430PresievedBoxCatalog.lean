import ImbalancedChen.Part5OriginalH430EnhancedMemberFactors
import ImbalancedChen.P5OriginalPresievedActiveDeltaFactors

/-! Preassigned finite boxes for the actual upper rough projection at
every enhanced Member's physical argument. The common rank and mesh are
chosen from retained positive floors before the arithmetic target. -/
namespace ImbalancedChen.Part5OriginalH430PresievedBoxCatalog
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open P2EnhancedLowerPhysicalNode P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RootSourceDictionary
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SameQHistoryCells Part5OriginalH430OwnedRootCounts
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430EnhancedPhysicalGrid
open Part5OriginalH430HistoryQuotientCounts (history_integer_roughness)
open Part5OriginalH430RootTentScreen Part5OriginalH430EnhancedMemberFactors
open P5Z.OriginalOrdinaryCommonBetaModel (ordinaryRetainOdd)
open P5Z.OriginalPresievedActiveDeltaFactors (ordinary_rough_supported_native_active)
open Part5OriginalH430OriginalReceiptMemberPullback (memberCutoff)

def roughUpper {N : ℕ} (cap : ℕ) (o : Occurrence N) (Q rho : ℝ) :=
  let B := parentProduct o.current.old
  fixedRoughSupport (ordinaryRetainOdd (Q/(B:ℝ))) (N*B) cap ((N:ℝ)^rho) (memberCutoff Q o)

/-- The genuine upper rough support itself supplies nonzero native
weight, the residual prime floor and the uniform rank of the entire
original old-plus-residual word. This includes d=1. -/
theorem rough_rank {N n m p cap d : ℕ} {k : Root} {t rho : ℝ} {c : RootKey n m}
    {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (hen : rootSource k (physicalPrime N p)=.enhanced)
    (hr : 0<rho) (hr' : rho≤frozenLeafCutoffFloor) (hd : d∈roughUpper cap o (cellQ N n c.1) rho) :
    let s := o.current.node.physical.argument
    let B := parentProduct o.current.old
    let Q := cellQ N n c.1
    nativeCoefficient true N cap B Q s d≠0 ∧
      (completeWord o d).length ≤ actualRoughVectorRankBound rho ∧
      (∀ q∈completeWord o d,(N:ℝ)^rho ≤ (q:ℝ)) ∧ ((completeWord o d).prod:ℝ)<N := by
  dsimp only
  let Q := cellQ N n c.1
  let B := parentProduct o.current.old
  let s := o.current.node.physical.argument
  let lam := rootLevel N n k t p
  let W := completeWord o d
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hb := (Finset.mem_filter.mp hp).1
  have hg := original_band_geometry hN hb
  have hi := rootHistory_support (by omega : 1<N) ht hu (precision_error hn) (original_band_prime hb) hg ho
  have hQ := (original_fibre_geometry hN ht hu (precision_error hn) hp).1
  have hyp := history_integer_roughness hN ht hu (precision_error hn) hb ho
  have hR : 1<Q/(B:ℝ) := by rw [show Q=rootQ N n k t p from hQ]; exact (parentWindow_logs hi.1).2.1
  have hsmall := Real.rpow_le_rpow_of_exponent_le hNr.le hr'
  have hz : (N:ℝ)^rho ≤ memberCutoff Q o := by
    rw [show Q=rootQ N n k t p from hQ]
    exact hsmall.trans hyp.2.1
  have hd' : d∈fixedRoughSupport (ordinaryRetainOdd (Q/(B:ℝ))) (N*B) cap ((N:ℝ)^rho) (memberCutoff Q o) := hd
  have hnative : nativeCoefficient true N cap B Q s d≠0 := ordinary_rough_supported_native_active hR hz hd'
  have hcomplete := native_word_support hN hn ht hu hp ho hen true (by simp) hnative
  have hprime := hcomplete.2.2.2.1
  have hpos (u) (h : u∈W) := (hprime u h).pos
  have hf : ∀ u∈W,(N:ℝ)^rho≤(u:ℝ) := by
    intro u hu'
    rcases List.mem_append.mp hu' with h | h
    · have hpd : u∣B := List.dvd_prod h
      have hp' := hprime u (List.mem_append_left _ h)
      exact hsmall.trans (hyp.2.2.1 _ ((Nat.mem_primeFactors_of_ne_zero hi.1.2.1.ne').mpr ⟨hp',hpd⟩))
    · exact (fixedRoughSupport_roughPrimeSupportedAt _ _ _ _ _ hd').2 _
        (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr (List.mem_reverse.mp h))
  have hne : W≠[] := by intro h; have hh:=hcomplete.2.2.2.2; rw [show completeWord o d=[] from h] at hh; cases hh
  have hcap : lam≤153/256 := by
    have H := (frozenLevel_bounds (root_total_bounds ht hu hg) n).1
    have hh := (enhanced_root_total (tau:=t) hen).le.trans (VariableEnvelope.v_le_cap _)
    exact H.trans hh
  have hsupp : actualDwellSupport ((N:ℝ)^lam) W := hQ ▸ hcomplete.1
  have hprod := actualDwellSupport_prod_le W hne hpos hsupp
  refine ⟨hnative,actualRoughPrimeVector_length_le hNr hr (by linarith only [hcap]) W hne hpos hf hsupp,hf,?_⟩
  exact hprod.trans_lt (by simpa only [Real.rpow_one] using
    Real.rpow_lt_rpow_of_exponent_lt hNr (show lam<1 by linarith only [hcap]))

def meshAt (n : ℕ) (rho : ℝ) :=
  ⌈(((actualRoughVectorRankBound rho:ℕ):ℝ)+2)/radius (collarIndex n)⌉₊

private theorem mesh_width (n : ℕ) (rho : ℝ) {s : ℕ} (hs : s≤actualRoughVectorRankBound rho) :
    ((s:ℝ)+2)*logPrimeMeshStep 0 1 (meshAt n rho)≤radius (collarIndex n) := by
  have he := radius_pos (collarIndex n)
  have h := (div_le_iff₀ he).mp
    (Nat.le_ceil ((((actualRoughVectorRankBound rho:ℕ):ℝ)+2)/radius (collarIndex n)))
  have hs' : (s:ℝ)≤actualRoughVectorRankBound rho := by exact_mod_cast hs
  have hM : 0<((meshAt n rho:ℕ):ℝ)+1 := by positivity
  rw [logPrimeMeshStep,sub_zero,←mul_div_assoc,mul_one]
  apply (div_le_iff₀ hM).mpr
  change ((actualRoughVectorRankBound rho:ℝ)+2)≤(meshAt n rho:ℝ)*radius (collarIndex n) at h
  nlinarith only [h,he,hs']

/-- The original finite half-open alphabet supplies an actual box at
the common mesh, its endpoint interval and the full-rank width budget.
Its selected first slot and all original occurrences are retained. -/
theorem actual_rough_box {N n m p cap d r : ℕ} {k : Root} {t rho : ℝ} {c : RootKey n m}
    {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (hen : rootSource k (physicalPrime N p)=.enhanced)
    (hr : 0<rho) (hr' : rho≤frozenLeafCutoffFloor) (hd : d∈roughUpper cap o (cellQ N n c.1) rho)
    (v : Fin (r+1)→ℕ) (hv : List.ofFn v=completeWord o d) :
    let J := meshAt n rho
    let Q := cellQ N n c.1
    let B := parentProduct o.current.old
    nativeCoefficient true N cap B Q o.current.node.physical.argument d≠0 ∧
    ∃ j : Fin (r+1)→Fin (J+1), actualPrimeTupleLog N v∈logPrimeMeshCell 0 1 J j ∧
      (((r+1:ℕ):ℝ)+2)*logPrimeMeshStep 0 1 J≤radius (collarIndex n) ∧
      ∀ i, actualPrimeTupleLog N v i ≤ logPrimeMeshHi 0 1 J j i ∧
        logPrimeMeshHi 0 1 J j i ≤ actualPrimeTupleLog N v i + logPrimeMeshStep 0 1 J := by
  dsimp only
  let J := meshAt n rho
  have H := rough_rank hN hn ht hu hp ho hen hr hr' hd
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hW := native_word_support hN hn ht hu hp ho hen true (by simp) H.1
  have hm (i : Fin (r+1)) : v i∈completeWord o d := by rw [←hv]; exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hpos (i) := (hW.2.2.2.1 _ (hm i)).pos
  have hl : r+1≤actualRoughVectorRankBound rho := by
    simpa only [←hv,List.length_ofFn] using H.2.1
  have hlog : actualPrimeTupleLog N v∈logPrimeBox (fun _=>0) (fun _=>1) := by
    apply mem_logPrimeBox.mpr
    intro i
    have hden : 0<(completeWord o d).prod := by
      apply List.prod_pos
      exact fun p hm => (hW.2.2.2.1 p hm).pos
    have hprod : (v i:ℝ)≤(completeWord o d).prod :=
      Nat.cast_le.mpr (Nat.le_of_dvd hden (List.dvd_prod (hm i)))
    have pow := actualPrimeTupleLog_rpow (by omega : 1<N) v hpos i
    constructor
    · apply (Real.strictMono_rpow_of_base_gt_one hNr).le_iff_le.mp
      rw [pow,Real.rpow_zero]
      exact_mod_cast hpos i
    · apply (Real.strictMono_rpow_of_base_gt_one hNr).lt_iff_lt.mp
      rw [pow,Real.rpow_one]
      exact hprod.trans_lt H.2.2.2
  obtain ⟨j,hj⟩ := exists_logPrimeMeshCell 0 1 J hlog
  refine ⟨H.1,j,hj,mesh_width n rho hl,fun i=>?_⟩
  have hh := mem_logPrimeMeshCell.mp hj i
  exact ⟨hh.2.le,by rw [logPrimeMeshHi_eq_lo_add_step]; exact add_le_add_right hh.1 _⟩

/-- One actual preassigned-mesh cell of the retained upper coefficient
supplies the three complete endpoints for ALL medium lengths and local
scales. None of its rank, width, residual activity or endpoint factors
is an additional license premise. -/
theorem presieved_upper_groups {N n m p cap d r : ℕ} {k : Root} {t rho : ℝ} {c : RootKey n m}
    {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (hen : rootSource k (physicalPrime N p)=.enhanced)
    (hkeep : ¬collar n (collarIndex n) (physicalPrime N p)) (hr : 0<rho) (hr' : rho≤frozenLeafCutoffFloor)
    (hd : d∈roughUpper cap o (cellQ N n c.1) rho) (v : Fin (r+1)→ℕ) (hv : List.ofFn v=completeWord o d) :
    let J := meshAt n rho
    let eta := radius (collarIndex n)
    ∃ j : Fin (r+1)→Fin (J+1), actualPrimeTupleLog N v∈logPrimeMeshCell 0 1 J j ∧
      ∀ x q alpha z A : ℝ, 1<x → x^q=(N:ℝ) → 1≤q → q≤1+eta/4 → q≤alpha → alpha≤1+eta/2 →
      0<z → z≤eta/8 → 1≤A → A≤x^(1/3-z/2) →
      let w := fun i => (N:ℝ)^logPrimeMeshHi 0 1 J j i
      let D := (N:ℝ)^(o.current.node.physical.total+eta)
      let out := groups w D A
      let a1 := (out.1.map w).prod
      let b := (out.2.1.map w).prod
      let c3 := (out.2.2.map w).prod
      (out.1.map v).prod*(out.2.1.map v).prod*(out.2.2.map v).prod=parentProduct o.current.old*d ∧
      a1≤A ∧ A^2*b*c3^2≤x^(1-3*z) ∧ x^(7*alpha/32)*A*a1*b^5*c3^2≤x^(2-4*z) ∧
      (A*c3/b)^(7/16:ℝ)*A*a1*b^5*c3^2≤x^(2-39*z/8) := by
  dsimp only
  obtain ⟨hactive,j,hj,hwidth,hends⟩ := actual_rough_box hN hn ht hu hp ho hen hr hr' hd v hv
  refine ⟨j,hj,fun x q alpha z A hx hscale hq hq' ha ha' hz hz' hA hA'=>?_⟩
  exact actual_native_whole_box hN hn ht hu hp ho hen hkeep true (by simp) hactive v hv _
    (logPrimeMeshStep_pos (by norm_num : (0:ℝ)<1) _).le hwidth (fun i=>(hends i).1) (fun i=>(hends i).2)
    hx hscale hq hq' ha ha' hz hz' hA hA'

end
end ImbalancedChen.Part5OriginalH430PresievedBoxCatalog
