import ImbalancedChen.P4ASixTentRange32Moments
import ImbalancedChen.ActualThirdOriginalP4ASixTentSymmetricLeaf

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
All-six affine OLD, direct rational weight, and original signed clipping for
the TRUE originalLn32 range-reduction operation tree. The source q integer
guard supplier discharges positive divisors; no unit-log value is substituted.
The final symmetric consumer uses the paired true-chord integral theorem.
-/
namespace ImbalancedChen.OriginalThirdP4ASixTentRange32OldWeight

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdRoundedOldWeightSourceOnly OriginalThirdPositiveLogSourceOnly
open OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly OriginalThirdP4ASymmetricTentPrerequisites
open OriginalThirdP4ABalancedSymmetricLeaf OriginalThirdP4ASixTentSymmetricLeaf
open OriginalThirdP4ASixTentRange32Moments
open OriginalThirdBelowMuBRoundedSourceOnly

/-- Exact source affine OLD operation order: rational A, signed ex product,
signed ey product, reciprocal-z product, then rational E addition. Both logs
come from the real range32 definitions in the moments module. -/
def tentOld32 (s : TentSum) (k : TentSide) (a b : BoxPoint) : IV :=
  add (mul (add (add (ofReal (planeConst k))
    (mul (ordinaryEx32 a b) (ofReal (oldX s k))))
    (mul (ordinaryEy32 a b) (ofReal (oldY s k))))
    (ordinaryInvZ32 a b)) (ofReal (oldZ s k))

/-- Literal direct positive rational division, not interval reciprocal
division. Original negative endpoint products and floor/UP are retained. -/
def tentWeight32 (s : TentSum) (k : TentSide) (a b : BoxPoint) (low high : ℚ) : IV :=
  OriginalThirdRoundedOldWeightSourceOnly.divRat
    (sub (tentOld32 s k a b) (ofReal (low:ℝ))) (high-low)

def gridTentOld32 (s : TentSum) (k : TentSide) (lower upper : Fin 3 → ℤ) : IV :=
  add (mul (add (add (ofReal (planeConst k))
    (mul (gridCoordinateEx32 lower upper 0) (ofReal (oldX s k))))
    (mul (gridCoordinateEx32 lower upper 1) (ofReal (oldY s k))))
    (gridInvZ32 lower upper)) (ofReal (oldZ s k))

def gridTentWeight32 (s : TentSum) (k : TentSide) (lower upper : Fin 3 → ℤ)
    (low high : ℚ) : IV :=
  OriginalThirdRoundedOldWeightSourceOnly.divRat
    (sub (gridTentOld32 s k lower upper) (ofReal (low:ℝ))) (high-low)

/-- Exact saved-integer operation ABI, retaining every original interval
rounding step. Neither interval addition nor multiplication is reassociated. -/
theorem tentOld32_grid_abi
    (s : TentSum) (k : TentSide) (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(upper i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lower i) (hwidth : ∀ i,lower i<upper i) :
    tentOld32 s k (realBox a) (realBox b)=gridTentOld32 s k lower upper := by
  have hl (i : Fin 3) : 0<lower i :=
    lt_of_lt_of_le (by norm_num [sourceH]) (hH i)
  have hu : 0<upper 2 := (hl 2).trans (hwidth 2)
  unfold tentOld32 gridTentOld32
  rw [ordinaryEx32_grid_abi lower upper a b haBind hbBind (hl 0).ne',
    ordinaryEy32_grid_abi lower upper a b haBind hbBind (hl 1).ne',
    ordinaryInvZ32_grid_abi lower upper a b haBind hbBind (hl 2) hu]

theorem tentWeight32_grid_abi
    (s : TentSum) (k : TentSide) (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (low high : ℚ)
    (haBind : ∀ i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(upper i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lower i) (hwidth : ∀ i,lower i<upper i) :
    tentWeight32 s k (realBox a) (realBox b) low high=
      gridTentWeight32 s k lower upper low high := by
  unfold tentWeight32 gridTentWeight32
  rw [tentOld32_grid_abi s k lower upper a b haBind hbBind hH hwidth]

/-- Real original affine expectation enclosed by the actual range32 OLD
tree. Operand enclosure facts are supplied by the moments module. -/
theorem tentOld32_encloses
    (s : TentSum) (k : TentSide) {a b : BoxPoint}
    (hlx : Encloses (ordinaryLog32 a b 0) (Real.log (b 0/a 0)))
    (hly : Encloses (ordinaryLog32 a b 1) (Real.log (b 1/a 1)))
    (hpx : 0<(ordinaryLog32 a b 0).lo) (hpy : 0<(ordinaryLog32 a b 1).lo) :
    Encloses (tentOld32 s k a b) (tentOldMean s k a b) := by
  have hx := ordinaryEx32_encloses hlx hpx
  have hy := ordinaryEy32_encloses hly hpy
  have hz := ordinaryInvZ32_encloses a b
  have h := add_sound (mul_sound
    (add_sound (add_sound (ofReal_sound (planeConst k))
      (mul_sound hx (ofReal_sound (oldX s k))))
      (mul_sound hy (ofReal_sound (oldY s k)))) hz) (ofReal_sound (oldZ s k))
  have heq : (planeConst k+boxEX a b*oldX s k+boxEY a b*oldY s k)*
      boxEZInv a b+oldZ s k=tentOldMean s k a b := by unfold tentOldMean; ring
  simpa only [tentOld32,heq] using h

theorem tentWeight32_encloses
    (s : TentSum) (k : TentSide) (a b : BoxPoint) (low high : ℚ)
    (ha : ∀ i,0<a i) (hab : ∀ i,a i<b i) (hres : 0<oldNumerator s k b)
    (hlow : (low:ℝ)=tentOldLow s k b) (hhigh : (high:ℝ)=tentOldHigh s k a)
    (hlx : Encloses (ordinaryLog32 a b 0) (Real.log (b 0/a 0)))
    (hly : Encloses (ordinaryLog32 a b 1) (Real.log (b 1/a 1)))
    (hpx : 0<(ordinaryLog32 a b 0).lo) (hpy : 0<(ordinaryLog32 a b 1).lo) :
    Encloses (tentWeight32 s k a b low high)
      ((tentOldMean s k a b-tentOldLow s k b)/(tentOldHigh s k a-tentOldLow s k b)) := by
  have hspan := original_tent_old_span s k a b ha hab hres
  have hq : (0:ℚ)<high-low := by
    have hr : (0:ℝ)<((high-low:ℚ):ℝ) := by
      simpa only [Rat.cast_sub,hlow,hhigh] using sub_pos.mpr hspan
    exact_mod_cast hr
  have hw := OriginalThirdRoundedOldWeightSourceOnly.divRat_sound
    (sub_sound (tentOld32_encloses s k hlx hly hpx hpy) (ofReal_sound (low:ℝ))) hq
  simpa only [tentWeight32,Rat.cast_sub,hlow,hhigh] using hw

/-- The true square-law weight lies in [0,1] by the actual affine range and
moment theorem. No desired rounded range or integral estimate is assumed. -/
theorem tent_square_weight_mem_unit
    (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (ha : ∀ i,0<a i) (hab : ∀ i,a i<b i) (hres : 0<oldNumerator s k b) :
    (tentOldMean s k a b-tentOldLow s k b)/(tentOldHigh s k a-tentOldLow s k b)∈Icc 0 1 := by
  have hr := tentOldMean_mem_range s k a b ha hab hres
  have hs := sub_pos.mpr (original_tent_old_span s k a b ha hab hres)
  constructor
  · exact div_nonneg (sub_nonneg.mpr hr.1) hs.le
  · exact (div_le_one hs).2 (by linarith [hr.2])

/-- Signed clipping works for arbitrary fl/fh, including negative slope.
The caller supplies only the original range32 primitive facts, not an OLD
mean, raw weight, clipped chord, or target leaf estimate. -/
theorem tentMeanHigh32_sound
    (s : TentSum) (k : TentSide) (a b : BoxPoint) (low high : ℚ) (fl fh out : ℤ)
    (ha : ∀ i,0<a i) (hab : ∀ i,a i<b i) (hres : 0<oldNumerator s k b)
    (hlow : (low:ℝ)=tentOldLow s k b) (hhigh : (high:ℝ)=tentOldHigh s k a)
    (hlx : Encloses (ordinaryLog32 a b 0) (Real.log (b 0/a 0)))
    (hly : Encloses (ordinaryLog32 a b 1) (Real.log (b 1/a 1)))
    (hpx : 0<(ordinaryLog32 a b 0).lo) (hpy : 0<(ordinaryLog32 a b 1).lo) :
    max 0 (value out-tentOldChord s k a b (value fl) (value fh))≤
      value (meanHigh (tentWeight32 s k a b low high).lo
        (tentWeight32 s k a b low high).hi fl fh out) := by
  have hw := tentWeight32_encloses s k a b low high ha hab hres hlow hhigh hlx hly hpx hpy
  have hr := tent_square_weight_mem_unit s k a b ha hab hres
  simpa only [tentOldChord] using
    meanHigh_sound (fl:=fl) (fh:=fh) (out:=out) hr.1 hr.2 hw.1 hw.2

/-- Arbitrary s/k on the original global coordinate grid: actual range32
soundness and positive divisors are both supplied from integer H/R bounds.
No ordering or below-mu assumption is needed for this arithmetic supplier. -/
theorem stored_global_tentOld32_encloses
    (s : TentSum) (k : TentSide) (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(upper i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lower i) (hwidth : ∀ i,lower i<upper i)
    (hR : ∀ i,upper i≤sourceR) :
    Encloses (tentOld32 s k (realBox a) (realBox b))
      (tentOldMean s k (realBox a) (realBox b)) := by
  have hl := stored_global_log32_sound lower upper a b haBind hbBind hH hwidth hR
  have hp := stored_global_log32_guards lower upper a b haBind hbBind hH hwidth hR
  exact tentOld32_encloses s k (hl 0) (hl 1) hp.1 hp.2

/-- Global original-grid clipping wrapper for ordinary and symmetric callers.
The primitive log and log.lo guard arguments of the arithmetic lemma are
entirely discharged by the actual integer-bound range32 suppliers. -/
theorem stored_global_tentMeanHigh32_sound
    (s : TentSum) (k : TentSide) (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (low high : ℚ) (fl fh out : ℤ)
    (haBind : ∀ i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(upper i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lower i) (hwidth : ∀ i,lower i<upper i)
    (hR : ∀ i,upper i≤sourceR)
    (ha : ∀ i,0<realBox a i) (hab : ∀ i,realBox a i<realBox b i)
    (hres : 0<oldNumerator s k (realBox b))
    (hlow : (low:ℝ)=tentOldLow s k (realBox b))
    (hhigh : (high:ℝ)=tentOldHigh s k (realBox a)) :
    max 0 (value out-tentOldChord s k (realBox a) (realBox b) (value fl) (value fh))≤
      value (meanHigh (tentWeight32 s k (realBox a) (realBox b) low high).lo
        (tentWeight32 s k (realBox a) (realBox b) low high).hi fl fh out) := by
  have hl := stored_global_log32_sound lower upper a b haBind hbBind hH hwidth hR
  have hp := stored_global_log32_guards lower upper a b haBind hbBind hH hwidth hR
  exact tentMeanHigh32_sound s k (realBox a) (realBox b) low high fl fh out
    ha hab hres hlow hhigh (hl 0) (hl 1) hp.1 hp.2

/-- Cutoff, original symmetric ordering and b<=mu give the actual <=32
range. This does not impose the false <=2 restriction on seed-size ratios. -/
theorem symmetric_ratio_le_32 {a b c d : ℝ} (hg : SymmetricFullBox a b c d)
    (hmu : b≤VariableEnvelope.mu) : b/a≤32 := by
  have ha := (symmetric_positive hg).1
  apply (div_le_iff₀ ha).2
  have hcut : (1:ℝ)/100≤a := hg.cutoff.trans (hg.width_z.le.trans hg.z_below_xy)
  norm_num [VariableEnvelope.mu] at hmu
  linarith

/-- The actual q range32 INTEGER supplier, not a caller log.lo guard,
supplies positivity on the stored symmetric x/y operand. -/
theorem symmetric_log32_enclosure_and_guard
    (x0 x1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) :
    Encloses (originalLn32 ((b:ℝ)/(a:ℝ))) (Real.log ((b:ℝ)/(a:ℝ))) ∧
      0<(originalLn32 ((b:ℝ)/(a:ℝ))).lo := by
  have h32 := symmetric_ratio_le_32 hg hmu
  have h1 : (1:ℝ)≤(b:ℝ)/(a:ℝ) :=
    (le_div_iff₀ (symmetric_positive hg).1).2 (by linarith [hg.width_xy])
  refine ⟨originalLn32_sound h1 h32,?_⟩
  exact symmetric_source_log32_guard x0 x1 a b ha hb (symmetric_positive hg).1
    hg.width_xy (by simpa only [VariableEnvelope.mu] using hmu) h32

/-- Concrete saved-grid OLD enclosure: neither primitive log soundness nor
any positive divisor guard remains a premise. Both x/y calls are preserved. -/
theorem stored_symmetric_tentOld32_encloses
    (s : TentSum) (k : TentSide) (x0 x1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) :
    Encloses (tentOld32 s k (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ)))
      (tentOldMean s k (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))) := by
  have hl := symmetric_log32_enclosure_and_guard x0 x1 a b c d ha hb hg hmu
  exact tentOld32_encloses s k hl.1 hl.1 hl.2 hl.2

/-- The complete original nonnegative mean_upper integer, before the
separate range32 mass/UP stage. NEW32 is the moments module's TRUE tree. -/
def symmetricMeanHigh32 (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) : ℤ :=
  let low := savedTentLow s k x1 z1
  let high := savedTentHigh s k x0 z0
  let left := symmetricLeft (a:ℝ) (c:ℝ)
  let right := symmetricRight (b:ℝ) (d:ℝ)
  let fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ)
  let out := readQueryHi160 (assembledRead table.blocks) (ordinaryNew32 left right).hi P160
  let wt := tentWeight32 s k left right low high
  meanHigh wt.lo wt.hi fl fh out

/-- Every original symmetric below-mu tent branch, with q-integer supplied
positive range32 divisors and SAME-reader queries. The paired true chords
supply the actual OLD lower bound without ordering the query approximations.
There is no caller log.lo guard, log enclosure, hquery, mean enclosure,
weight/clipping estimate, desired leaf inequality, or K bound. -/
theorem original_symmetric_tent_range32_mean_upper
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hbranch : literalSymmetricBranch s k x0 x1 z0 z1)
    (hroot : literalSymmetricRoot s k x0 x1 z0 z1)
    (hres : literalSymmetricResidual s k x1)
    (hlow : (2:ℚ)≤savedTentLow s k x1 z1) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)*
        value (symmetricMeanHigh32 table s k x0 x1 z0 z1 a b c d) := by
  have hguards := original_selected_tent_guard_bridge s k ![x0,x0,z0] ![x1,x1,z1]
    (48000*2^24) 481573208064
    (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))
    rfl rfl (symmetric_grid_bind x0 z0 a c ha hc) (symmetric_grid_bind x1 z1 b d hb hd)
    (by simpa only [literalSymmetricBranch,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hbranch)
    (by simpa only [literalSymmetricRoot,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hroot)
    (by simpa only [literalSymmetricResidual,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hres)
  have hz0 := positive_grid_binding z0 c hc (symmetric_positive hg).2
  have hz1 := positive_grid_binding z1 d hd ((symmetric_positive hg).2.trans hg.width_z)
  have hloEq : (savedTentLow s k x1 z1:ℝ)=
      tentOldLow s k (symmetricRight (b:ℝ) (d:ℝ)) :=
    saved_tent_endpoint_cast s k x1 z1 b d hb hd hz1
  have hhiEq : (savedTentHigh s k x0 z0:ℝ)=
      tentOldHigh s k (symmetricLeft (a:ℝ) (c:ℝ)) :=
    saved_tent_endpoint_cast s k x0 z0 a c ha hc hz0
  have hloR : (2:ℝ)≤(savedTentLow s k x1 z1:ℝ) := by exact_mod_cast hlow
  have hl := symmetric_log32_enclosure_and_guard x0 x1 a b c d ha hb hg hmu
  let left := symmetricLeft (a:ℝ) (c:ℝ)
  let right := symmetricRight (b:ℝ) (d:ℝ)
  let low := savedTentLow s k x1 z1
  let high := savedTentHigh s k x0 z0
  let fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ)
  let out := readQueryHi160 (assembledRead table.blocks) (ordinaryNew32 left right).hi P160
  have hfl := (stored_rat_query_encloses table low).1
  have hfh := (stored_rat_query_encloses table high).1
  have hnewInterval : Encloses (ordinaryNew32 left right)
      (newMean (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) :=
    ordinaryNew32_symmetric_encloses hl.1 hl.1 hl.2 hl.2
  have hnewQuery := (CheckedBlockTable.query_encloses_all table
    (ordinaryNew32 left right).hi P160 P160_pos).2
  have hnewArg : newMean (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)≤
      ((ordinaryNew32 left right).hi:ℝ)/(P160:ℝ) := hnewInterval.2
  have hnew : actualExtendedThirdLowerFactor
      (newMean (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))≤value out := by
    apply (monotone_actualExtendedThirdLowerFactor hnewArg).trans
    simpa only [out,value,P160,Int.cast_pow,Int.cast_ofNat] using hnewQuery
  have hleaf := all_symmetric_tent_exact_leaf_upper s k hg hmu hguards.1 hguards.2.1 hguards.2.2
    (by simpa only [←hloEq] using hloR)
    (by simpa only [←hloEq] using hfl) (by simpa only [←hhiEq] using hfh) hnew
  have hround := tentMeanHigh32_sound s k left right low high fl fh out
    (symmetric_left_positive hg) (symmetric_widths hg) hguards.2.2
    hloEq hhiEq hl.1 hl.1 hl.2 hl.2
  have hfinal := hleaf.trans
    (mul_le_mul_of_nonneg_left hround (symmetric_prism_mass_pos hg).le)
  exact hfinal

end
end ImbalancedChen.OriginalThirdP4ASixTentRange32OldWeight
