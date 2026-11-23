import ImbalancedChen.Part5OriginalH430HBMediumRectangles
import ImbalancedChen.P5ActualHBChartEventualClosure
import ImbalancedChen.Part5OriginalH430AllMarkedPrimitive

/-! Select the actual first medium block of a live bounded-rank HB
chart. Its own lower endpoint and the owner of the complementary product
are the two physical lengths at the same marked Member. -/
namespace ImbalancedChen.Part5OriginalH430SelectedHBMedium
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430RootSourceDictionary Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430SameQHistoryCells Part5OriginalH430OwnedRootCounts Part5OriginalH430EmittedWordBox
open Part5OriginalH430RootTentScreen Part5OriginalH430EnhancedMemberFactors Part5OriginalH430PresievedBoxCatalog
open Part5OriginalH430AttachedUpperMember (coefficientAt)
open Part5OriginalH430AllMarkedPrimitive (active_group_factors)
open Part5OriginalH430CompleteMediumMember (betaCap mediumReceipt upper_member_all_complete_scales)
open Part5OriginalH430OriginalReceiptMemberPullback (memberCutoff)
open P5Z.OriginalOrdinaryResidualArithmeticFactor (roughWeight)
open P5Z.OriginalOrdinaryCommonBetaModel (commonSmallWeight)
open P5Z.HBRightClosedDyadicRoles (Block Owns owner owner_owns)
open P5Z.OriginalHBCompleteProductScale (OriginalGroupTuple joined joined_prod joined_pos completeInteger
  localScale actual_occurrence_complete_window exists_actual_HB_residue_threshold)
open P5Z.ActualHBDyadicOccurrenceFamily (assignedWeight)
open P5Z.ActualRoughHeathBrownWords (roles)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds assigned_nonzero_owns)
open P5Z.ActualHBMediumBranchPartition (Medium originalLower originalUpper firstMedium firstMedium_some)
open P5Z.ActualMultiGroupHBChartScale (Group chartN chartX scaleConstant scaleConstant_pos
  blocks whole_geometry original_product_geometry owns_split)
open P5Z.SmoothChartPhysicalHBBranch (original_to_local_medium)
open P5Z.ActualHBChartEventualClosure (fixed_reserves)
open P5Z.ActualLabelledPrimeSmoothCharts (chartTerm trimmedWeight)

private theorem productGroups (gs : List Group) : (((gs.map (·.n)).prod:ℕ):ℝ)=chartN gs := by
  induction gs with
  | nil => simp [chartN]
  | cons g gs ih => simp only [List.map_cons,List.prod_cons,Nat.cast_mul,chartN,ih]

/-- Every occurrence retains its own ordered tuple in the finite signed
HB row, including repeated group data in different positions. -/
def liveRow (g : Group) (r : OriginalGroupTuple) : Prop :=
  r.integer=g.n ∧ r.row=g.j ∧ assignedWeight g.z g.y (roles g.j) g.bs r.factors≠0

private theorem aligned_rows {gs : List Group} {rows : List OriginalGroupTuple}
    (hs : List.Forall₂ liveRow gs rows) :
    List.Forall₂ Owns (blocks gs) (joined rows) ∧ (completeInteger rows:ℝ)=chartN gs := by
  induction hs with
  | nil => exact ⟨List.Forall₂.nil,by norm_num [completeInteger,chartN]⟩
  | @cons g row gs rows hg _ ih =>
    obtain ⟨howns,hprod⟩ := ih
    refine ⟨List.rel_append (assigned_nonzero_owns (roles g.j) g.bs row.factors hg.2.2) howns,?_⟩
    change ((row.integer*completeInteger rows:ℕ):ℝ)=(g.n:ℝ)*chartN gs
    rw [Nat.cast_mul,hg.1,hprod]

/-- Convert the actual first-medium decision at X into the two physical
block lengths at x. The absolute support of W is fixed on the original
complete word. Its live chart supplies the lower trim for that same word.
The input lists the individual nonzero ordered summands of its actual
HB rows. The block lengths and capacity are derived for each such list. -/
theorem selected_medium_block (K : ℕ) (C z kap k0 : ℝ) (hC : 0<C) (hz : 0<z)
    (hz' : z≤1/100) (hk : 0<kap) (hk0 : k0<kap/(4*(1+kap))) :
    ∀ᶠ N : ℕ in atTop, ∀ (gs : List Group) (rows : List OriginalGroupTuple) (chi : ℝ→ℝ) (W : List ℕ→ℂ) (js : List ℕ),
    List.Forall₂ liveRow gs rows → gs.length≤K → (∀ ns, W ns≠0 → (ns.prod:ℝ)≤C*N) →
    chartTerm chi (fun u=>Real.smoothTransition (u-1)) W (N:ℝ) k0 js (gs.map (·.n))≠0 →
    ∀ (left right : List Block) (b : Block), blocks gs=left++b::right →
    firstMedium (originalLower (chartX gs) z) (originalUpper (chartX gs) z) (blocks gs)=some left.length →
    ∃ (pl : List ℕ) (p : ℕ) (pr : List ℕ), joined rows=pl++p::pr ∧ List.Forall₂ Owns left pl ∧ Owns b p ∧
      List.Forall₂ Owns right pr ∧ Owns (owner (pl++pr).prod) (pl++pr).prod ∧
      let U : ℝ := lower b
      let V : ℝ := lower (owner (pl++pr).prod)
      let x := U*V
      let A := U/x^z
      1<x ∧ C⁻¹*x≤(N:ℝ) ∧ (N:ℝ)≤x^(1+kap) ∧
      1≤A ∧ A≤x^(1/3-z/2) ∧ A*x^z=U ∧ x/(A*x^z)=V := by
  have hk1 : 0<1+kap := by linarith
  have ht : 0<1-k0 := by
    have hh := (lt_div_iff₀ (show 0<4*(1+kap) by positivity)).mp hk0
    by_contra! h'
    have hmul := mul_le_mul_of_nonneg_right (by linarith only [h'] : (1:ℝ)≤k0)
      (show 0≤4*(1+kap) by positivity)
    nlinarith only [hh,hmul,hk]
  obtain ⟨L,hL,Hres⟩ := fixed_reserves (K+1) hz (show 18*z<(1:ℝ) by linarith only [hz'])
  obtain ⟨N0,hN0,Hx⟩ := exists_actual_HB_residue_threshold hC hk hk0
  have hgrow : ∀ᶠ N : ℕ in atTop, L*(2:ℝ)^K≤(N:ℝ)^(1-k0) :=
    ((tendsto_rpow_atTop ht).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop N0,hgrow] with N hN hlarge
  intro gs rows chi W js hrows hrank hW hlive left right b hsplit hfirst
  let ns := gs.map (·.n)
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hT := Real.rpow_pos_of_pos hNpos (1-k0)
  have hweight : W ns≠0 := by
    intro he
    apply hlive
    simp only [chartTerm,trimmedWeight,show W (gs.map (·.n))=0 from he,mul_zero]
  have htrim : (N:ℝ)^(1-k0)≤chartN gs := by
    by_contra! hsmall
    have H0 : Real.smoothTransition ((ns.prod:ℝ)/(N:ℝ)^(1-k0)-1)=0 :=
      Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ((div_le_one hT).mpr
        ((productGroups gs).le.trans hsmall.le)))
    apply hlive
    simp only [chartTerm,trimmedWeight,show Real.smoothTransition
      (((gs.map (·.n)).prod:ℝ)/(N:ℝ)^(1-k0)-1)=0 from H0,Complex.ofReal_zero,zero_mul,mul_zero]
  have hup : chartN gs≤C*N := (productGroups gs).symm.le.trans (hW ns hweight)
  obtain ⟨howns,hprod⟩ := aligned_rows hrows
  rw [hsplit] at howns
  obtain ⟨pl,p,pr,hint,hleft,hbp,hright⟩ := owns_split left right b (joined rows) howns
  have hp : p∈joined rows := by rw [hint]; simp
  have hcompPos : 0<(pl++pr).prod := by
    apply List.prod_pos
    intro u hu
    apply joined_pos rows u
    rw [hint]
    rcases List.mem_append.mp hu with hu | hu
    · exact List.mem_append_left _ hu
    · exact List.mem_append_right _ (List.mem_cons_of_mem p hu)
  have hcomp := owner_owns hcompPos
  have hdiv : completeInteger rows/p=(pl++pr).prod := by
    have hh : completeInteger rows=p*(pl++pr).prod := by
      rw [←joined_prod,hint]
      simp only [List.prod_append,List.prod_cons]
      ring
    rw [hh,Nat.mul_div_cancel_left _ ((lower_pos b).trans_le (owns_bounds hbp).1)]
  have hc : Owns (owner (pl++pr).prod) (completeInteger rows/p) := by
    rw [hdiv]
    exact hcomp
  have hw := actual_occurrence_complete_window rows hp hbp hc
  let U : ℝ := lower b
  let V : ℝ := lower (owner (pl++pr).prod)
  let x := U*V
  have hx : 0<x := mul_pos (zero_lt_one.trans_le hw.1) (zero_lt_one.trans_le hw.2.1)
  have hxN : x≤chartN gs := hw.2.2.1.trans hprod.le
  have hNx : chartN gs≤4*x := hprod.symm.le.trans hw.2.2.2
  have hX := (whole_geometry gs).1
  have htwo : (2:ℝ)^gs.length≤(2:ℝ)^K := pow_le_pow_right₀ (by norm_num) hrank
  have hNX : chartN gs≤(2:ℝ)^K*chartX gs :=
    (original_product_geometry gs).2.1.trans (mul_le_mul_of_nonneg_right htwo hX.le)
  have hXN : chartX gs≤(2:ℝ)^K*chartN gs :=
    (original_product_geometry gs).2.2.trans (mul_le_mul_of_nonneg_right htwo (original_product_geometry gs).1.le)
  have hfour : 4*(2:ℝ)^K≤scaleConstant (K+1) := calc
    4*(2:ℝ)^K ≤ 4*(128:ℝ)^K := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num) K) (by norm_num)
    _ ≤ scaleConstant (K+1) := by
      unfold scaleConstant
      rw [pow_succ]
      nlinarith only [show 0≤(128:ℝ)^K by positivity]
  have htS : (2:ℝ)^K≤scaleConstant (K+1) := by
    nlinarith only [hfour,show 0≤(2:ℝ)^K by positivity]
  have hxXK : x≤scaleConstant (K+1)*chartX gs :=
    (hxN.trans hNX).trans (mul_le_mul_of_nonneg_right htS hX.le)
  have hXxK : chartX gs≤scaleConstant (K+1)*x := calc
    chartX gs ≤ (2:ℝ)^K*(4*x) := hXN.trans (mul_le_mul_of_nonneg_left hNx (by positivity))
    _ = (4*(2:ℝ)^K)*x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfour hx.le
  have hXlarge : L≤chartX gs := le_of_mul_le_mul_right (a:=(2:ℝ)^K) (calc
    L*(2:ℝ)^K ≤ (2:ℝ)^K*chartX gs := hlarge.trans (htrim.trans hNX)
    _ = chartX gs*(2:ℝ)^K := mul_comm _ _) (by positivity)
  obtain ⟨hXL,hxl,_,_,_,hloRes,hhiRes,_,_⟩ := Hres (chartX gs) x hXlarge hXxK
  obtain ⟨hx1,hresLo,hresHi⟩ := Hx N hN rows p b (owner (pl++pr).prod) hp hbp hc
    (htrim.trans hprod.symm.le) (hprod.le.trans hup)
  obtain ⟨hi,hm,_⟩ := firstMedium_some hfirst
  have hbM : Medium (originalLower (chartX gs) z) (originalUpper (chartX gs) z) b := by
    have hl : (blocks gs)[left.length]?=some b := by
      rw [hsplit,List.getElem?_append_right (le_refl _),Nat.sub_self]
      rfl
    have heq : (blocks gs)[left.length]'hi=b :=
      Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hl)
    simpa only [heq] using hm
  have bounds := original_to_local_medium hx1.le hXL.le (scaleConstant_pos (K+1)).le hz.le hxXK hXxK hloRes hhiRes hbM
  have hxz := Real.rpow_pos_of_pos hx _
  have hU : 0<U := by exact_mod_cast lower_pos b
  have hA1 : 1≤U/x^z := (one_le_div hxz).mpr
    ((Real.rpow_le_rpow_of_exponent_le hx1.le (show z≤2*z by linarith)).trans bounds.1)
  have hA2 : U/x^z≤x^(1/3-z/2) := (div_le_iff₀ hxz).mpr (by
    rw [←Real.rpow_add hx]; convert bounds.2 using 1 <;> congr 1 <;> ring)
  have heA := div_mul_cancel₀ U hxz.ne'
  refine ⟨pl,p,pr,hint,hleft,hbp,hright,hcomp,hx1,hresLo,hresHi,hA1,hA2,heA,?_⟩
  change x/(U/x^z*x^z)=V
  rw [heA]
  exact (div_eq_iff hU.ne').mpr (mul_comm _ _)

/-- One genuine upper coefficient, ordered marked word and endpoint cell
work for each concrete nonzero ordered HB tuple and first medium
selection in the admitted live charts. The
capacity here is determined by the selected block, and its other length
is exactly the lower endpoint of the owner of all complementary factors. -/
theorem selected_HB_member (n : ℕ) (hn : 111≤n) (K : ℕ) (C z : ℝ)
    (hC : 0<C) (hz : 0<z) (he : z≤radius (collarIndex n)/8)
    (nu : ℝ) (hnu : 0<nu) (beta : ℝ) (hb : 0<beta) (hb' : beta≤betaCap nu z)
    (kap k0 : ℝ) (hk : 0<kap) (hk' : kap≤(z/2000)/200) (hk0 : k0<kap/(4*(1+kap))) :
    ∀ᶠ N : ℕ in atTop, ∀ {m p cap h : ℕ} {k : Root} {t : ℝ} {key : RootKey n m} {o : Occurrence N},
    0≤t → t≤1/12 → p∈rootFibre N n m k t key → o∈rootHistory N n k t p →
    rootSource k (physicalPrime N p)=.enhanced → ¬collar n (collarIndex n) (physicalPrime N p) →
    coefficientAt cap (cellQ N n key.1) (nu*beta^2) (nu*beta) o h≠0 →
    let Q := cellQ N n key.1
    let B := parentProduct o.current.old
    let M := (N:ℝ)^(nu*beta)
    let J := meshAt n (nu*beta^2)
    ∃ (e d r : ℕ) (v : Fin (r+1)→ℕ) (j : Fin (r+1)→Fin (J+1)),
    h=e*d ∧ (e:ℝ)<M ∧ d∈roughUpper cap o Q (nu*beta^2) ∧
    coefficientAt cap Q (nu*beta^2) (nu*beta) o h=roughWeight (N*B) cap ((N:ℝ)^(nu*beta^2))
      (memberCutoff Q o) (Q/(B:ℝ)) d*commonSmallWeight (N*B) cap ((N:ℝ)^(nu*beta^2))
        (memberCutoff Q o) (Q/(B:ℝ)) M d e ∧
    List.ofFn v=completeWord o d ∧ actualPrimeTupleLog N v∈logPrimeMeshCell 0 1 J j ∧
    ∀ (gs : List Group) (rows : List OriginalGroupTuple) (chi : ℝ→ℝ) (W : List ℕ→ℂ) (js : List ℕ),
    List.Forall₂ liveRow gs rows → gs.length≤K → (∀ ns, W ns≠0 → (ns.prod:ℝ)≤C*N) →
    chartTerm chi (fun u=>Real.smoothTransition (u-1)) W (N:ℝ) k0 js (gs.map (·.n))≠0 →
    ∀ (left right : List Block) (b : Block), blocks gs=left++b::right →
    firstMedium (originalLower (chartX gs) z) (originalUpper (chartX gs) z) (blocks gs)=some left.length →
    ∃ (pl : List ℕ) (s : ℕ) (pr : List ℕ), joined rows=pl++s::pr ∧ List.Forall₂ Owns left pl ∧ Owns b s ∧
      List.Forall₂ Owns right pr ∧ Owns (owner (pl++pr).prod) (pl++pr).prod ∧
      let U : ℝ := lower b
      let V : ℝ := lower (owner (pl++pr).prod)
      let x := U*V
      let A := U/x^z
      1≤A ∧ A≤x^(1/3-z/2) ∧ A*x^z=U ∧ x/(A*x^z)=V ∧
      let w := fun i=>(N:ℝ)^logPrimeMeshHi 0 1 J j i
      let D := (N:ℝ)^(o.current.node.physical.total+radius (collarIndex n))
      let out := groups w D A
      mediumReceipt N B h e v w D M x z A ∧
        (out.1.map v).prod.Coprime N ∧ (out.2.1.map v).prod.Coprime N ∧ (e*(out.2.2.map v).prod).Coprime N := by
  have hzsmall : z≤1/100 := by
    have hcap : radius (collarIndex n)≤1/100 := min_le_left _ _
    linarith only [he,hcap]
  filter_upwards [upper_member_all_complete_scales n hn C⁻¹ z (inv_pos.mpr hC)
    hz he nu hnu beta hb hb',selected_medium_block K C z kap k0 hC hz hzsmall hk hk0,
    eventually_ge_atTop (2:ℕ)] with N HM HS hN
  intro m p cap h k t key o ht hu hp ho hsrc hkeep ha
  dsimp only
  obtain ⟨e,d,r,v,j,hed,heM,hrough,hcoef,hword,hcell,Hm⟩ := HM ht hu hp ho hsrc hkeep ha
  have hprimitive := (active_group_factors hN hn ht hu hp ho true cap (nu*beta^2) (nu*beta) ha).2.2
  refine ⟨e,d,r,v,j,hed,heM,hrough,hcoef,hword,hcell,?_⟩
  intro gs rows chi W js hrows hK hW hlive left right b hsplit hfirst
  obtain ⟨pl,s,pr,hints,hleft,hb,hright,hc,hx,hlo,hhi,hA,hA',hU,hV⟩ :=
    HS gs rows chi W js hrows hK hW hlive left right b hsplit hfirst
  have H := Hm kap _ _ hk.le hk' (zero_lt_one.trans hx) hlo hhi hA hA'
  exact ⟨pl,s,pr,hints,hleft,hb,hright,hc,hA,hA',hU,hV,H,hprimitive _ _ _ H.2.2.2.2.2.2.1⟩

end
end ImbalancedChen.Part5OriginalH430SelectedHBMedium
