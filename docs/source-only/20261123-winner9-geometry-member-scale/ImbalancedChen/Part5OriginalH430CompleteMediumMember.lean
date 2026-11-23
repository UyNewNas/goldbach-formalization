import ImbalancedChen.Part5OriginalH430AttachedUpperMember
import ImbalancedChen.P5OriginalH430ResidueWindow

/-! The original enhanced Member at every complete local scale of the
moving-residue proposition. A single upper endpoint vector and one
chronological marked integer word work simultaneously in every such
rectangle, on either side of the global target. -/
namespace ImbalancedChen.Part5OriginalH430CompleteMediumMember
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P5Z.OriginalOrdinaryCommonBetaModel (commonSmallWeight)
open P5Z.OriginalOrdinaryResidualArithmeticFactor (roughWeight)
open Part5OriginalH430PhysicalRoots Part5OriginalH430RootSourceDictionary
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SameQHistoryCells Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback (memberCutoff)
open Part5OriginalH430EnhancedPhysicalGrid Part5OriginalH430EmittedWordBox
open Part5OriginalH430RootTentScreen Part5OriginalH430EnhancedMemberFactors Part5OriginalH430PresievedBoxCatalog
open Part5OriginalH430AttachedUpperMember (coefficientAt upper_member_medium)
open P5OriginalH430ResidueWindow (eventually_residue_window)
open P5OriginalH430CompleteScale (full_trim_medium_ranges)

/-- A local positive upper limit for the one common beta after this
positive support floor and zeta are fixed. -/
def betaCap (nu z : ℝ) := min 1 (min (frozenLeafCutoffFloor/nu) ((z/16)/nu))

theorem betaCap_pos {nu z : ℝ} (hnu : 0<nu) (hz : 0<z) : 0<betaCap nu z :=
  lt_min zero_lt_one (lt_min (div_pos frozenLeafCutoffFloor_pos hnu) (div_pos (by positivity) hnu))

/-- The genuine group factorization, lengths and all four moving-residue
conditions evaluated at the actual chart x, the actual global N, and its
specified medium capacity A. -/
def mediumReceipt {r : ℕ} (N B h e : ℕ) (v : Fin (r+1)→ℕ) (w : Fin (r+1)→ℝ) (D M x z A : ℝ) : Prop :=
  let out := groups w D A
  let Q1 := (out.1.map w).prod
  let Q2 := (out.2.1.map w).prod
  let Q3 := M*(out.2.2.map w).prod
  let U := A*x^z
  let sigma := z/2000
  x^(Real.logb x (N:ℝ))=(N:ℝ) ∧ 1≤U ∧ 1≤x/U ∧ 1≤Q1 ∧ 1≤Q2 ∧ 1≤Q3 ∧
    (out.1.map v).prod*(out.2.1.map v).prod*(e*(out.2.2.map v).prod)=B*h ∧
    ((out.1.map v).prod:ℝ)≤Q1 ∧ ((out.2.1.map v).prod:ℝ)≤Q2 ∧ ((e*(out.2.2.map v).prod:ℕ):ℝ)≤Q3 ∧
    Q1<U*x^(-sigma) ∧ U^2*Q2*Q3^2<x^(1-8*sigma) ∧
    (N:ℝ)^(7/32:ℝ)*U*Q1*Q2^5*Q3^2<x^(2-15*sigma) ∧
    U^(1+7/16:ℝ)*Q1*Q2^(5-7/16:ℝ)*Q3^(2+7/16:ℝ)<x^(2-15*sigma)

/-- Fix the policy precision, zeta, and one common positive beta. The
same modulus factors, true signed coefficient value, half-open cell and
endpoint vector work on the entire original residue window. The common
threshold precedes both roots, the whole marked history and every x,A.
Zero-length residual words are included. -/
theorem upper_member_all_complete_scales (n : ℕ) (hn : 111≤n) (c0 z : ℝ) (hc0 : 0<c0)
    (hz : 0<z) (hzeta : z≤radius (collarIndex n)/8) (nu : ℝ) (hnu : 0<nu) (beta : ℝ)
    (hb : 0<beta) (hbeta : beta≤betaCap nu z) :
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
    ∀ kap x A : ℝ, 0≤kap → kap≤(z/2000)/200 → 0<x → c0*x≤(N:ℝ) → (N:ℝ)≤x^(1+kap) →
    1≤A → A≤x^(1/3-z/2) → mediumReceipt N B h e v (fun i=>(N:ℝ)^logPrimeMeshHi 0 1 J j i)
      ((N:ℝ)^(o.current.node.physical.total+radius (collarIndex n))) M x z A := by
  let eta := radius (collarIndex n)
  let rho := nu*beta^2
  let ell := nu*beta
  have heta : eta≤1/100 := min_le_left _ _
  have hzsmall : z≤1/100 := by dsimp only [eta] at heta; linarith only [hzeta,heta]
  have hb1 := hbeta.trans (min_le_left _ _)
  have hb2 := hbeta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb3 := hbeta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr : 0<rho := mul_pos hnu (sq_pos_of_pos hb)
  have hrf : rho≤frozenLeafCutoffFloor := calc
    nu*beta^2 ≤ nu*beta := mul_le_mul_of_nonneg_left (by nlinarith only [mul_nonneg hb.le (sub_nonneg.mpr hb1)]) hnu.le
    _ ≤ frozenLeafCutoffFloor := by simpa only [mul_comm] using (le_div_iff₀ hnu).mp hb2
  have hell : 0<ell := mul_pos hnu hb
  have hell' : ell≤z/16 := by simpa only [ell,mul_comm] using (le_div_iff₀ hnu).mp hb3
  filter_upwards [eventually_residue_window hc0 hz hzsmall,eventually_ge_atTop (2:ℕ)] with N hs hN
  intro m p cap h k t key o ht hu hp ho hen hkeep hact
  dsimp only
  let Q := cellQ N n key.1
  let B := parentProduct o.current.old
  let M := (N:ℝ)^ell
  let J := meshAt n rho
  let D := (N:ℝ)^(o.current.node.physical.total+eta)
  obtain ⟨e,d,r,v,_,hprod,heM,hd,hcoef,hword,_,_⟩ :=
    upper_member_medium hN hn ht hu hp ho hen hkeep hr hrf hell.le hact
  obtain ⟨j,hj,H⟩ := presieved_upper_groups hN hn ht hu hp ho hen hkeep hr hrf hd v hword
  refine ⟨e,d,r,v,j,hprod,heM,hd,hcoef,hword,hj,?_⟩
  intro kap x A hk hk' hx0 hcN hNx hA hA'
  have hksmall : kap≤1/100 := by linarith only [hk',hzsmall]
  let y := min x (N:ℝ)
  let q := Real.logb y (N:ℝ)
  obtain ⟨hx,hxq,hy,hyx,hyq,hqlo,hqhi,hcap⟩ := hs kap x hk hksmall hx0 hcN hNx
  change q≤1+kap at hqhi
  change y^q=(N:ℝ) at hyq
  have hq1 : q≤1+eta/4 := by linarith only [hqhi,hk',hzeta,hz]
  have hq2 : q≤1+eta/2 := by linarith only [hq1,radius_pos (collarIndex n)]
  have haux := H y q q (7*z/8) A hy hyq hqlo hq1 le_rfl hq2 (by positivity)
    (by linarith only [hzeta,hz]) hA (hA'.trans hcap)
  obtain ⟨hraw,hgroup,H2,H3,H4⟩ := haux
  let w := fun i=> (N:ℝ)^logPrimeMeshHi 0 1 J j i
  let out := groups w D A
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hactual : y^(7*q/32)=(N:ℝ)^(7/32:ℝ) := by
    rw [←hyq,←Real.rpow_mul (zero_lt_one.trans hy).le]
    congr 1 <;> ring
  have H3' : (N:ℝ)^(7/32:ℝ)*A*(out.1.map w).prod*(out.2.1.map w).prod^5*(out.2.2.map w).prod^2≤
      y^(2-4*(7*z/8)) := by rwa [←hactual]
  have hM : 0<M := Real.rpow_pos_of_pos hNp _
  have hMx : M≤x^(z/8) := calc
    (N:ℝ)^ell ≤ (x^(1+kap))^ell := Real.rpow_le_rpow hNp.le hNx hell.le
    _ = x^((1+kap)*ell) := (Real.rpow_mul hx0.le _ _).symm
    _ ≤ x^(z/8) := Real.rpow_le_rpow_of_exponent_le hx.le (by
      nlinarith only [mul_le_mul_of_nonneg_right (show 1+kap≤2 by linarith only [hksmall]) hell.le,hell'])
  have hvpos (i : Fin (r+1)) : 0<v i := by
    have hpr := (native_word_support hN hn ht hu hp ho hen true (by simp)
      (rough_rank hN hn ht hu hp ho hen hr hrf hd).1).2.2.2.1
    exact (hpr _ (by rw [←hword]; exact List.mem_ofFn.mpr ⟨i,rfl⟩)).pos
  have hcoord (i : Fin (r+1)) : (v i:ℝ)≤w i := by
    rw [←actualPrimeTupleLog_rpow (by omega : 1<N) v hvpos i]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (mem_logPrimeMeshCell.mp hj i).2.le
  have hw (L : List (Fin (r+1))) : 1≤(L.map w).prod := by
    induction L with
    | nil => simp
    | cons i L ih =>
      have hw1 := (show (1:ℝ)≤v i by exact_mod_cast (show 1≤v i from hvpos i)).trans (hcoord i)
      simpa only [List.map_cons,List.prod_cons,one_mul] using
        mul_le_mul hw1 ih zero_le_one (zero_le_one.trans hw1)
  have hmono := full_trim_medium_ranges hx (zero_lt_one.trans hy) hyx hNp hz hzsmall (zero_lt_one.trans_le hA)
    (zero_lt_one.trans_le (hw out.1)) (zero_lt_one.trans_le (hw out.2.1)) (zero_lt_one.trans_le (hw out.2.2))
    hM hMx hgroup H2 H3' H4
  have hend := (same_groups_all_tuples w D A v hcoord).2
  have hU : 1≤A*x^z := by
    simpa only [one_mul] using mul_le_mul hA (Real.one_le_rpow hx.le hz.le) zero_le_one (zero_le_one.trans hA)
  have hUx : A*x^z≤x := calc
    _ ≤ x^(1/3-z/2)*x^z := mul_le_mul_of_nonneg_right hA' (Real.rpow_nonneg hx0.le _)
    _ = x^(1/3-z/2+z) := (Real.rpow_add hx0 _ _).symm
    _ ≤ x^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [hzsmall])
    _ = x := Real.rpow_one _
  have hm1 : 1≤M := Real.one_le_rpow hN1 hell.le
  have h3one : 1≤M*(out.2.2.map w).prod := by
    simpa only [one_mul] using mul_le_mul hm1 (hw out.2.2) zero_le_one (zero_le_one.trans hm1)
  refine ⟨hxq,hU,(one_le_div (zero_lt_one.trans_le hU)).mpr hUx,hw _,hw _,h3one,?_,hend.1,hend.2.1,?_,hmono⟩
  · change (out.1.map v).prod*(out.2.1.map v).prod*(e*(out.2.2.map v).prod)=B*h
    rw [hprod,show (out.1.map v).prod*(out.2.1.map v).prod*(e*(out.2.2.map v).prod)=
      e*((out.1.map v).prod*(out.2.1.map v).prod*(out.2.2.map v).prod) by ring,hraw]
    ring
  · rw [Nat.cast_mul]
    exact mul_le_mul heM.le hend.2.2 (Nat.cast_nonneg _) hM.le

end
end ImbalancedChen.Part5OriginalH430CompleteMediumMember
