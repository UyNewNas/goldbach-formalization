import ImbalancedChen.Part5OriginalH430RootTentScreen
import ImbalancedChen.Part5OriginalH430AllRootRejectedWindows
import ImbalancedChen.P5OriginalH430SingletonCoverRescale
import ImbalancedChen.P2OriginalSelectedIntegerPrefixSquares
import ImbalancedChen.P2EnhancedNativeLowerAtomSupport
import ImbalancedChen.P5ZU1011OriginalFifteenJointSelectedSupport
import ImbalancedChen.ActualFrozenSelectedPairSlots

/-! Actual enhanced U3/U4 occurrences use the selected first prime at
every depth. Following the Y08/Y11 root-collar removal, the same complete
level supports a boxwise upper-endpoint allocation for both capacity
cases and either nonzero native Rosser sign. -/
namespace ImbalancedChen.Part5OriginalH430EnhancedMemberFactors
noncomputable section
open scoped Classical BigOperators Topology
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalSelectedIntegerPrefixSquares (squareGates_to_integer integerSquareGates_at)
open P5Z.U1011OriginalFifteenJointSelectedSupport (actual_plus_residual_well append_square_support)
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember Part5OriginalH430RequestedAdmission
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SameQHistoryCells Part5OriginalH430OwnedRootCounts
open Part5OriginalH430EnhancedPhysicalGrid Part5OriginalH430RootSourceDictionary
open Part5OriginalH430EmittedWordBox Part5OriginalH430RootTentScreen
open P5OriginalH430SingletonCoverRescale
open Part5OriginalH430SquareStripPrimeMass (width)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables.OriginalU34 (tailCutoff)

private theorem total_eq {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    (ho : o∈rootHistory N n k t p) :
    o.current.node.physical.total = (frozenRoot n k t (physicalPrime N p)).physical.total := by
  rw [(history_facts ho).2.2,replay_total]
  rfl

/-- Before the local rescaling the middle line has uniform positive
slack on the entire enhanced root band, including the change of tent slope. -/
theorem redundant_line_slack {k : Root} {x : ℝ} (hb : x∈rootBand k) (he : rootSource k x=.enhanced) :
    71/28672 ≤ 2-(39/16)*VariableEnvelope.v x-(17/8)*x := by
  have hx := enhanced_root_coordinate he hb
  have hcap := VariableEnvelope.v_le_cap x
  dsimp [VariableEnvelope.cap] at hcap
  dsimp [tailCutoff] at hx
  linarith

/-- Actual root code, actual selected prime, and actual descendant total
supply all three admissibility lines. The previous scalar theorem's
four geometric hypotheses are derived here on the paid complement. -/
theorem actual_chart_interval {N n m p : ℕ} {k : Root} {t : ℝ} {c : RootKey n m}
    {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (hen : rootSource k (physicalPrime N p)=.enhanced)
    (hkeep : ¬collar n (collarIndex n) (physicalPrime N p))
    {q y alpha z : ℝ} (hq : 1≤q) (hq' : q≤1+radius (collarIndex n)/4)
    (hres : q≤alpha) (hres' : alpha≤1+radius (collarIndex n)/2)
    (hy : physicalPrime N p≤y) (hy' : y≤physicalPrime N p+radius (collarIndex n))
    (hz : 0<z) (hz' : z≤radius (collarIndex n)/8) :
    let lam := o.current.node.physical.total
    let theta := q*(lam+radius (collarIndex n))+2*z
    codeLevel n c.1 = lam ∧ (N:ℝ)^lam = cellQ N n c.1 ∧
    1/2 < lam ∧ lam+radius (collarIndex n)<VariableEnvelope.v (physicalPrime N p) ∧
    1/2 < theta ∧ theta < 153/256 ∧ 2*theta-1 < q*y ∧ q*y < actualSelectedSubproductUpper alpha theta := by
  dsimp only
  let x := physicalPrime N p
  let lam := o.current.node.physical.total
  let eta := radius (collarIndex n)
  have hband := (Finset.mem_filter.mp hp).1
  have hb := original_band_geometry hN hband
  have hpp := original_band_prime hband
  have heq := total_eq ho
  have hQ := (original_fibre_geometry hN ht hu (precision_error hn) hp).1
  have hcode : codeLevel n c.1 = lam :=
    (Real.strictMono_rpow_of_base_gt_one (by exact_mod_cast (show 1<N by omega) : (1:ℝ)<N)).injective
      (hQ.trans (rootHistory_sameQ ho).symm)
  have hlevel : lam = frozenLevel n (VariableEnvelope.v x) := by
    rw [show lam = (frozenRoot n k t x).physical.total from heq]
    change frozenLevel n (sourceRoot k t x).physical.total = _
    rw [enhanced_root_total (tau:=t) hen]
  have hnu := root_total_bounds ht hu hb
  rw [enhanced_root_total (tau:=t) hen] at hnu
  have hxb := rootBand_subset k hb
  have hlow : 1/2 < lam := by
    rw [hlevel]
    exact (by norm_num : (1/2:ℝ)<57/112).trans_le
      (Part5OriginalH430AllRootRejectedWindows.enhanced_level_floor hn ht hu hb hen)
  have hl : lam ≤ VariableEnvelope.v x := hlevel.le.trans (frozenLevel_bounds hnu n).1
  have hd : ¬ |VariableEnvelope.v x-codeLevel n c.1| ≤ width (collarIndex n) :=
    fun h => hkeep ⟨c.1,h⟩
  rw [hcode,abs_of_nonneg (sub_nonneg.mpr hl)] at hd
  have he := radius_pos (collarIndex n)
  have h4 : 4*eta ≤ width (collarIndex n) := by
    have h : eta≤width (collarIndex n)/4 := min_le_right _ _
    linarith
  have htent : lam+4*eta ≤ VariableEnvelope.v x := by linarith only [hd,h4]
  have hA : lam+4*eta ≤ (1+x)/2 := htent.trans (min_le_left _ _)
  have hC : lam+4*eta ≤ 57/64-3*x/2 := by
    have H := htent.trans ((min_le_right _ _).trans (min_le_right _ _))
    change lam+4*eta ≤ 57/64-3/2*x at H
    linarith
  have hmid := redundant_line_slack hb hen
  have hM : lam+4*eta ≤ (32-34*x)/39 := by linarith only [htent,hmid]
  have hcap : lam+4*eta ≤ 153/256 := htent.trans (VariableEnvelope.v_le_cap x)
  have hx0 : 0≤x := (by norm_num [a] : (0:ℝ)≤a).trans hxb.1
  exact ⟨hcode,(rootHistory_sameQ ho).trans hQ.symm,hlow,by linarith only [htent,he],
    scaled_singleton_interval hlow.le hx0 hxb.2 he (min_le_left _ _) hA hM hC hcap
      hq hq' hres hres' hy hy' hz hz'⟩

def nativeCoefficient (upper : Bool) (N cap B : ℕ) (Q s : ℝ) (d : ℕ) :=
  let R := Q/(B:ℝ)
  let w := cutoff Q B s
  if upper then actualSmallRosserPlus (N*B) cap w R d else actualSmallRosserMinus (N*B) cap w R d

def completeWord {N : ℕ} (o : Occurrence N) (d : ℕ) := o.current.old ++ d.primeFactorsList.reverse

/-- Attach every active native arithmetic tail, with its original sign
and Q/B cutoff. On a genuine lower comparison s≥2 supplies the initial
square that the lower parity alone would leave unpaid. -/
theorem native_word_support {N n m p cap d : ℕ} {k : Root} {t s : ℝ} {c : RootKey n m}
    {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (hen : rootSource k (physicalPrime N p)=.enhanced) (upper : Bool)
    (hs : upper=false → 2≤s)
    (hd : nativeCoefficient upper N cap (parentProduct o.current.old) (cellQ N n c.1) s d≠0) :
    let Q := cellQ N n c.1
    let B := parentProduct o.current.old
    actualDwellSupport Q (completeWord o d) ∧
    actualDwellSupport (Q/(p:ℝ)) (completeWord o d).tail ∧
    (completeWord o d).prod = B*d ∧
    (∀ z∈completeWord o d, z.Prime) ∧
    (completeWord o d).head? = some p := by
  dsimp only
  let Q := cellQ N n c.1
  let B := parentProduct o.current.old
  let R := Q/(B:ℝ)
  let w := cutoff Q B s
  have hband := (Finset.mem_filter.mp hp).1
  have hpr := original_band_prime hband
  have hgeom := original_band_geometry hN hband
  have hcoh := rootHistory_coherent (by omega) ht hu (precision_error hn) hpr hgeom ho
  have geom := rootHistory_support (by omega) ht hu (precision_error hn) hpr hgeom ho
  have hQ := (original_fibre_geometry hN ht hu (precision_error hn) hp).1
  have hB : 0<B := geom.1.2.1
  have hNreal : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hR : 1<R := by change 1<cellQ N n c.1/(B:ℝ); rw [hQ]; exact (parentWindow_logs geom.1).2.1
  have hpred : actualDwellSupport R d.primeFactorsList.reverse ∧ d≠0 := by
    cases upper with
    | true =>
      have h : actualSmallRosserPlus (N*B) cap w R d≠0 := hd
      exact ⟨actual_plus_residual_well h,(actualSmallRosserSupport_squarefree _ _ _ (actualSmallRosserPlus_active h).1).ne_zero⟩
    | false =>
      have h : actualSmallRosserMinus (N*B) cap w R d≠0 := hd
      have h2 : 2≤s := hs rfl
      have hs0 : 0<s := by linarith
      have hw : w^2≤R := by
        change (R^(1/s))^2≤R
        rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hR.le)]
        calc
          _ ≤ R^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hR.le (by
            have h := (div_le_one hs0).mpr h2
            convert h using 1 <;> push_cast <;> ring)
          _ = R := Real.rpow_one R
      exact ⟨P2EnhancedNativeLowerAtomSupport.actual_minus_residual_well h hw,
        (actualSmallRosserSupport_squarefree _ _ _ (actualSmallRosserMinus_active h).1).ne_zero⟩
  have oldp (z) (hz : z∈o.current.old) := (hcoh.letters z hz).1
  have hg := (enhanced_history_physical_gates hn hN ht hu hband hen ho).1
  change SquareGates o.current.node.physical.total 0 (word o.current.node.physical) at hg
  rw [rootHistory_integer_word ho] at hg
  have hg' := squareGates_to_integer hNreal o.current.old (fun z hz => (oldp z hz).pos)
    (T:=0) (B:=1) (by simp) hg
  have old : actualDwellSupport Q o.current.old := by
    intro i hi
    have h := integerSquareGates_at _ hg' i hi
    rw [rootHistory_sameQ ho,←hQ] at h
    simpa only [Nat.one_mul,actualNatList_cast_prod] using h
  have whole : actualDwellSupport Q (completeWord o d) :=
    append_square_support _ _ old hpred.1 (by
      change (B:ℝ)*(Q/(B:ℝ))≤Q
      rw [mul_comm,div_mul_cancel₀ Q (Nat.cast_ne_zero.mpr hB.ne')])
  have hw : completeWord o d = p :: (letters o.path ++ d.primeFactorsList.reverse) := by
    rw [completeWord,occurrence_old ho,List.cons_append]
  have hrem := actualDwell_selected_prefix_budget [p] (letters o.path ++ d.primeFactorsList.reverse)
    (by simpa only [List.prod_cons,List.prod_nil,mul_one] using hpr.1.pos)
    (by simpa only [List.singleton_append,←hw] using whole)
  refine ⟨whole,by simpa [hw] using hrem,?_,?_,by simp only [hw,List.head?_cons]⟩
  · simp only [completeWord,List.prod_append,List.prod_reverse,Nat.prod_primeFactorsList hpred.2,parentProduct,B]
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact oldp z hz
    · exact Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hz)

private def remainingSlots (r : ℕ) : List (Fin (r+1)) := List.ofFn Fin.succ

def groups {r : ℕ} (w : Fin (r+1) → ℝ) (D A : ℝ) :
    List (Fin (r+1)) × List (Fin (r+1)) × List (Fin (r+1)) :=
  if 1 ≤ D/(A*w 0) then
    let ac := actualTwoCapacityGreedy w A (remainingSlots r)
    (ac.1,[0],ac.2)
  else
    let ab := actualTwoCapacityGreedy w A (0::remainingSlots r)
    (ab.1,ab.2,[])

private theorem wholeSlots (r : ℕ) : (0::remainingSlots r : List (Fin (r+1))) = List.ofFn id := by
  rw [List.ofFn_succ]
  rfl

theorem groups_partition {r : ℕ} (w : Fin (r+1) → ℝ) (D A : ℝ) :
    let out := groups w D A
    (out.1 ++ out.2.1 ++ out.2.2).Perm (List.ofFn id) := by
  dsimp only
  rw [←wholeSlots,groups]
  split_ifs
  · let ac := actualTwoCapacityGreedy w A (remainingSlots r)
    have H := (actualTwoCapacityGreedy_partition w A (remainingSlots r)).perm
    change (ac.1++[0]++ac.2).Perm (0::remainingSlots r)
    have hm : (ac.1++[0]++ac.2).Perm ([0]++(ac.1++ac.2)) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁:=ac.1) (l₂:=[0])).append_right ac.2
    exact hm.trans (by simpa only [List.singleton_append] using H.cons 0)
  · simpa only [List.append_nil] using
      (actualTwoCapacityGreedy_partition w A (0::remainingSlots r)).perm

/-- Every tuple in the original endpoint box uses this one choice of
integer SLOT lists. All arithmetic factors preserve multiplicity. -/
theorem same_groups_all_tuples {r : ℕ} (w : Fin (r+1) → ℝ) (D A : ℝ) :
    let out := groups w D A
    ∀ v : Fin (r+1) → ℕ, (∀ i, (v i : ℝ) ≤ w i) →
    (out.1.map v).prod*(out.2.1.map v).prod*(out.2.2.map v).prod = (List.ofFn v).prod ∧
    ((out.1.map v).prod:ℝ) ≤ (out.1.map w).prod ∧
    ((out.2.1.map v).prod:ℝ) ≤ (out.2.1.map w).prod ∧
    ((out.2.2.map v).prod:ℝ) ≤ (out.2.2.map w).prod := by
  dsimp only
  intro v hv
  have h := ((groups_partition w D A).map v).prod_eq
  have b (l : List (Fin (r+1))) : ((l.map v).prod:ℝ) ≤ (l.map w).prod := by
    rw [←actualNatList_cast_prod]
    simpa only [List.map_map,Function.comp_def] using List.prod_map_le_prod_map₀
      (fun i => (v i:ℝ)) w (fun i _ => Nat.cast_nonneg _) (fun i _ => hv i)
  exact ⟨by simpa only [List.map_append,List.prod_append,List.map_ofFn,Function.comp_id,mul_assoc] using h,
    b _,b _,b _⟩

private theorem allocation {r : ℕ} (w : Fin (r+1) → ℝ) (D A : ℝ)
    (hw : ∀ i, 0<w i) (hA : 1≤A) (hAD : A≤D)
    (hfull : PrefixSquareBound w D (0::remainingSlots r)) :
    let out := groups w D A
    (out.1.map w).prod≤A ∧
    (((out.2.1.map w).prod=w 0 ∧ (out.2.2.map w).prod≤D/(A*w 0)) ∨
      (D/A<w 0 ∧ (out.2.1.map w).prod≤D/A ∧ (out.2.2.map w).prod=1)) := by
  have hA0 := zero_lt_one.trans_le hA
  rw [groups]
  split_ifs with hC
  · have hrem : PrefixSquareBound w (A*(D/(A*w 0))) (remainingSlots r) := by
      have hc : A*(D/(A*w 0))=D/w 0 := by field_simp [hA0.ne',(hw 0).ne']
      rw [hc]
      intro i hi
      have H := hfull (i+1) (by simpa using hi)
      apply (le_div_iff₀ (hw 0)).mpr
      simpa only [List.take_succ_cons,List.map_cons,List.prod_cons,List.getElem_cons_succ,
        mul_left_comm,mul_comm,mul_assoc] using H
    obtain ⟨_,ha,hc⟩ := actualTwoCapacityGreedy_correct w hA hC (remainingSlots r) hrem
    exact ⟨ha,Or.inl ⟨by simp,hc⟩⟩
  · have hB : 1≤D/A := (one_le_div hA0).mpr hAD
    have hb : A*(D/A)=D := by field_simp [hA0.ne']
    obtain ⟨_,ha,hc⟩ := actualTwoCapacityGreedy_correct w hA hB (0::remainingSlots r) (by simpa only [hb] using hfull)
    have hsmall : D/A < w 0 := (div_lt_iff₀ hA0).mpr (by
      simpa only [mul_comm] using (div_lt_one (mul_pos hA0 (hw 0))).mp (lt_of_not_ge hC))
    exact ⟨ha,Or.inr ⟨hsmall,hc,rfl⟩⟩

private theorem endpoint_support {r N : ℕ} (hN : 1<N) (v : Fin (r+1) → ℕ)
    (hp : ∀ i, 0<v i) {lam eta delta : ℝ} (y : Fin (r+1)→ℝ)
    (hfull : actualDwellSupport ((N:ℝ)^lam) (List.ofFn v))
    (hd : 0≤delta) (hy : ∀ i,y i≤actualPrimeTupleLog N v i+delta)
    (hwidth : (((r+1:ℕ):ℝ)+2)*delta ≤ eta) :
    PrefixSquareBound (fun i => (N:ℝ)^y i) ((N:ℝ)^(lam+eta)) (0::remainingSlots r) := by
  let g := actualPrimeTupleLog N v
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hNp := zero_lt_one.trans hNr
  have H := (P2EnhancedSortedDwellMerge.dwell_ofFn_iff _ v).mp hfull
  have powSquare (t : ℝ) : (N:ℝ)^(2*t) = ((N:ℝ)^t)^2 := by
    rw [mul_comm (2:ℝ),Real.rpow_mul hNp.le,Real.rpow_two]
  have pp (i : Fin (r+1)) :
      (∑ j : Fin (r+1) with j.val<i.val,g j)+2*g i≤lam := by
    apply (Real.strictMono_rpow_of_base_gt_one hNr).le_iff_le.mp
    rw [Real.rpow_add hNp,Real.rpow_sum_of_pos hNp,powSquare]
    simpa only [g,actualPrimeTupleLog_rpow hN v hp,Fin.lt_def] using H i
  rw [wholeSlots]
  intro i hi
  have hir : i<r+1 := by simpa using hi
  let k : Fin (r+1) := ⟨i,hir⟩
  have hh := endpoint_square_increase g y hd hy k
  have hnew : (∑ j : Fin (r+1) with j.val<k.val,y j)+2*y k ≤ lam+eta := by
    linarith only [pp k,hh,hwidth]
  have he := Real.rpow_le_rpow_of_exponent_le hNr.le hnew
  rw [Real.rpow_add hNp,Real.rpow_sum_of_pos hNp,powSquare] at he
  simpa only [List.map_take,List.map_ofFn,Function.comp_id,List.prod_take_ofFn,
    List.getElem_ofFn,id_eq,k] using he

/-- The physical root/Member, complete native coefficient and actual
root key furnish the deterministic endpoint factors with all three
monomials. Quantification over A includes both original capacity branches.
The width refers to the complete rank, including the native divisor. -/
theorem actual_native_whole_box {N n m p cap d r : ℕ} {k : Root} {t s : ℝ} {c : RootKey n m}
    {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (hen : rootSource k (physicalPrime N p)=.enhanced)
    (hkeep : ¬collar n (collarIndex n) (physicalPrime N p))
    (upper : Bool) (hs : upper=false → 2≤s)
    (hd : nativeCoefficient upper N cap (parentProduct o.current.old) (cellQ N n c.1) s d≠0)
    (v : Fin (r+1)→ℕ) (hv : List.ofFn v=completeWord o d)
    (y : Fin (r+1)→ℝ) {delta : ℝ} (hdelta : 0≤delta)
    (hwidth : (((r+1:ℕ):ℝ)+2)*delta≤radius (collarIndex n))
    (hlo : ∀ i,actualPrimeTupleLog N v i≤y i) (hhi : ∀ i,y i≤actualPrimeTupleLog N v i+delta)
    {x q alpha z A : ℝ} (hx : 1<x) (hscale : x^q=(N:ℝ))
    (hq : 1≤q) (hq' : q≤1+radius (collarIndex n)/4) (hres : q≤alpha)
    (hres' : alpha≤1+radius (collarIndex n)/2)
    (hz : 0<z) (hz' : z≤radius (collarIndex n)/8)
    (hA : 1≤A) (hAup : A≤x^(1/3-z/2)) :
    let lam := o.current.node.physical.total
    let eta := radius (collarIndex n)
    let w := fun i => (N:ℝ)^y i
    let out := groups w ((N:ℝ)^(lam+eta)) A
    let a1 := (out.1.map w).prod
    let b := (out.2.1.map w).prod
    let c3 := (out.2.2.map w).prod
    (out.1.map v).prod*(out.2.1.map v).prod*(out.2.2.map v).prod=parentProduct o.current.old*d ∧
    a1≤A ∧ A^2*b*c3^2≤x^(1-3*z) ∧
    x^(7*alpha/32)*A*a1*b^5*c3^2≤x^(2-4*z) ∧
    (A*c3/b)^(7/16:ℝ)*A*a1*b^5*c3^2≤x^(2-39*z/8) := by
  dsimp only
  let lam := o.current.node.physical.total
  let eta := radius (collarIndex n)
  let theta := q*(lam+eta)+2*z
  let w := fun i => (N:ℝ)^y i
  let D := (N:ℝ)^(lam+eta)
  let out := groups w D A
  have src := native_word_support hN hn ht hu hp ho hen upper hs hd
  have hvp (i) : (v i).Prime := src.2.2.2.1 _ (by
    rw [←hv]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hroot : v 0=p := by
    have h := src.2.2.2.2
    rw [←hv,List.ofFn_succ] at h
    simpa only [List.head?_cons,Option.some.injEq] using h
  have hdEta : delta≤eta := by
    have hlen : (1:ℝ)≤((r+1:ℕ):ℝ)+2 := by
      push_cast
      linarith only [Nat.cast_nonneg (α:=ℝ) r]
    calc
      delta = 1*delta := (one_mul _).symm
      _ ≤ (((r+1:ℕ):ℝ)+2)*delta := mul_le_mul_of_nonneg_right hlen hdelta
      _ ≤ eta := hwidth
  have hx0 : physicalPrime N p≤y 0 := by simpa only [actualPrimeTupleLog,physicalPrime,hroot] using hlo 0
  have hx1 : y 0≤physicalPrime N p+eta := by
    have hi := (hhi 0).trans (add_le_add_left hdEta _)
    simpa only [actualPrimeTupleLog,physicalPrime,hroot] using hi
  obtain ⟨_,hQ,hl,_,hθlo,hθhi,hbl,hbu⟩ :=
    actual_chart_interval hN hn ht hu hp ho hen hkeep hq hq' hres hres' hx0 hx1 hz hz'
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hw (i) : 0<w i := Real.rpow_pos_of_pos hNp _
  have hb : w 0=x^(q*y 0) := by
    dsimp only [w]
    rw [Real.rpow_mul (zero_lt_one.trans hx).le,hscale]
  have hD : D=x^(theta-2*z) := by
    dsimp only [D,theta]
    rw [add_sub_cancel_right,Real.rpow_mul (zero_lt_one.trans hx).le,hscale]
  have he := radius_pos (collarIndex n)
  have hz12 : z≤1/12 := by
    have hh : eta≤1/100 := min_le_left _ _
    linarith only [hz',hh]
  have hAD : A≤D := by
    rw [hD]
    apply hAup.trans (Real.rpow_le_rpow_of_exponent_le hx.le _)
    linarith only [hθlo,hz12]
  have hwell := endpoint_support (by omega : 1<N) v (fun i=>(hvp i).pos) y
    (lam:=lam) (eta:=eta) (by rw [hv,hQ]; exact src.1) hdelta hhi hwidth
  have alloc := allocation w D A hw hA hAD hwell
  have ha (l : List (Fin (r+1))) : 0<(l.map w).prod :=
    List.prod_pos (fun a ha => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha; exact hw i)
  have hMlo : x^(2*theta-1)≤w 0 := by
    rw [hb]
    exact Real.rpow_le_rpow_of_exponent_le hx.le hbl.le
  have hMhi : w 0≤x^(actualSelectedSubproductUpper alpha theta) := by
    rw [hb]
    exact Real.rpow_le_rpow_of_exponent_le hx.le hbu.le
  have size (i) : (v i:ℝ)≤w i := by
    rw [←actualPrimeTupleLog_rpow (by omega : 1<N) v (fun j=>(hvp j).pos) i]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega)) (hlo i)
  have eq := (same_groups_all_tuples w D A v size).1
  rw [hv,src.2.2.1] at eq
  refine ⟨eq,alloc.1,?_⟩
  rcases alloc.2 with ⟨hmid,hr⟩ | ⟨hsmall,hm,hr⟩
  · have hcap : A*(out.2.1.map w).prod*(out.2.2.map w).prod ≤ x^(theta-2*z) := by
      rw [hmid,←hD,mul_comm (A*w 0)]
      exact (le_div_iff₀ (mul_pos (zero_lt_one.trans_le hA) (hw 0))).mp hr
    obtain ⟨h1,h2,h3⟩ := selectedPair_monomials hx (zero_lt_one.trans_le hA)
      (ha out.1) (ha out.2.1) (ha out.2.2) hcap (by rw [hmid]; exact hMlo)
      (by rw [hmid]; exact hMhi) alloc.1
    exact ⟨h1.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),h2,h3⟩
  · have hA0 := zero_lt_one.trans_le hA
    have hD0 : 0<D := Real.rpow_pos_of_pos hNp _
    have hAB : A*(D/A)=x^(theta-2*z) := by rw [mul_comm,div_mul_cancel₀ _ hA0.ne',←hD]
    have H := twoFactorRepair_monomials hx hz12 (by linarith only [hθhi] : theta≤5/8)
      hA0 (div_pos hD0 hA0) (ha out.1) (ha out.2.1) hAB hAup (hsmall.le.trans hMhi) alloc.1 hm
    simpa only [hr,one_pow,mul_one] using H

end
end ImbalancedChen.Part5OriginalH430EnhancedMemberFactors
