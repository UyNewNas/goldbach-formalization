import ImbalancedChen.Part5OriginalH430CompleteMediumMember
import ImbalancedChen.P5OriginalHBCompleteProductScale
import ImbalancedChen.P5ActualLabelledPrimeSmoothCharts

/-! Apply the H430 Member's same signed coefficient and endpoint cell to
actual Heath--Brown dyadic rectangles on the complete global target. -/
namespace ImbalancedChen.Part5OriginalH430HBMediumRectangles
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430RootSourceDictionary
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430SameQHistoryCells Part5OriginalH430OwnedRootCounts Part5OriginalH430EmittedWordBox
open Part5OriginalH430RootTentScreen Part5OriginalH430EnhancedMemberFactors Part5OriginalH430PresievedBoxCatalog
open Part5OriginalH430AttachedUpperMember (coefficientAt)
open Part5OriginalH430CompleteMediumMember (betaCap mediumReceipt upper_member_all_complete_scales)
open Part5OriginalH430OriginalReceiptMemberPullback (memberCutoff)
open P5Z.OriginalOrdinaryResidualArithmeticFactor (roughWeight)
open P5Z.OriginalOrdinaryCommonBetaModel (commonSmallWeight)
open P5Z.OriginalHBCompleteProductScale (OriginalGroupTuple joined completeInteger localScale exists_actual_HB_residue_threshold)
open P5Z.HBRightClosedDyadicRoles (Block Owns)
open P5Z.ActualLabelledPrimeSmoothCharts (chartTerm trimmedWeight)

/-- The manuscript's actual cutoff eta(s)=smoothTransition(s-1) in the
existing labelled chart forces its complete integer above the lower trim.
There is no separate lower-support hypothesis on the rectangle. -/
theorem active_chart_complete_integer {N : ℕ} (hN : 0<N) (k0 : ℝ) (gs : List OriginalGroupTuple)
    (chi : ℝ→ℝ) (W : List ℕ→ℂ) (js : List ℕ)
    (ha : chartTerm chi (fun u=>Real.smoothTransition (u-1)) W (N:ℝ) k0 js (gs.map (·.integer))≠0) :
    (N:ℝ)^(1-k0)<(completeInteger gs:ℝ) := by
  by_contra! hh
  have hcut := (div_le_one (Real.rpow_pos_of_pos (by exact_mod_cast hN : (0:ℝ)<N) (1-k0))).mpr hh
  have hzero : Real.smoothTransition ((completeInteger gs:ℝ)/(N:ℝ)^(1-k0)-1)=0 :=
    Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hcut)
  apply ha
  simp only [chartTerm,trimmedWeight,←completeInteger,hzero,Complex.ofReal_zero,zero_mul,mul_zero]

/-- Same original root, actual coefficient, labelled word and all
marked factors on every live HB rectangle. Its chosen integer, its
complement and the two original Owns certificates supply x. The upper
window is the original complete-integer support of the geometric weight. -/
theorem actual_member_HB_rectangles (n : ℕ) (hn : 111≤n) (C z : ℝ) (hC : 0<C) (hz : 0<z)
    (he : z≤radius (collarIndex n)/8) (nu : ℝ) (hnu : 0<nu) (beta : ℝ) (hb : 0<beta) (hb' : beta≤betaCap nu z)
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
    ∀ (gs : List OriginalGroupTuple) (s : ℕ) (b c : Block) (chi : ℝ→ℝ) (W : List ℕ→ℂ) (js : List ℕ),
    s∈joined gs → Owns b s → Owns c (completeInteger gs/s) →
    chartTerm chi (fun u=>Real.smoothTransition (u-1)) W (N:ℝ) k0 js (gs.map (·.integer))≠0 →
    (completeInteger gs:ℝ)≤C*N →
    ∀ A : ℝ, 1≤A → A≤(localScale b c)^(1/3-z/2) →
    mediumReceipt N B h e v (fun i=>(N:ℝ)^logPrimeMeshHi 0 1 J j i)
      ((N:ℝ)^(o.current.node.physical.total+radius (collarIndex n))) M (localScale b c) z A := by
  obtain ⟨N0,hN0,Hs⟩ := exists_actual_HB_residue_threshold hC hk hk0
  filter_upwards [upper_member_all_complete_scales n hn C⁻¹ z (inv_pos.mpr hC) hz he nu hnu beta hb hb',
    eventually_ge_atTop N0] with N H hN
  intro m p cap h k t key o ht hu hp ho hsrc hkeep ha
  dsimp only
  obtain ⟨e,d,r,v,j,hed,heM,hrough,hcoef,hword,hcell,Hm⟩ := H ht hu hp ho hsrc hkeep ha
  refine ⟨e,d,r,v,j,hed,heM,hrough,hcoef,hword,hcell,?_⟩
  intro gs s b c chi W js hs hb hc hlive hsup A hA hA'
  have htrim := active_chart_complete_integer (by omega : 0<N) k0 gs chi W js hlive
  obtain ⟨hx,hlo,hhi⟩ := Hs N hN gs s b c hs hb hc htrim.le hsup
  exact Hm kap (localScale b c) A hk.le hk' (zero_lt_one.trans hx) hlo hhi hA hA'

end
end ImbalancedChen.Part5OriginalH430HBMediumRectangles
