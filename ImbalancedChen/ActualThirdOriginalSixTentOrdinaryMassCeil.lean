import ImbalancedChen.ActualThirdOriginalSixTentRoundedConsumer
import ImbalancedChen.ActualThirdOriginalSymmetricMassCeil
import ImbalancedChen.ActualThirdOriginalStoredNodeQueryLookup
import ImbalancedChen.ActualThirdOriginalStoredQueryAllBranches

/-!
SOURCEONLY / HOLD_ELABORATION / UNCOMPILED / MAIN OPEN30.
V2 replacement proposed module: ActualThirdOriginalSixTentOrdinaryMassCeil.
Supersedes the frozen 13749-byte V1; do not import both copies.
The all-query import means the 20261024w StoredQueryAllBranches draft,
SHA256 839167b1e610ba542a19d5f4d6256cbd4ec0bcadb5e1b65b3c71c9517daab904.
The first import means EXACTLY the frozen 20261024u consumer draft, SHA256
 dd02c2b62254a26447485de0aba9c6fe00004bbf365b07684911cdac59fa5a1b.
ROOT must install/qualify its q guard-bridge dependency and that consumer first.

Original producer SHA256 005fcc24c3431753e2530ab90f70e80d2256b3691cd45d14e13eb9191b0caa7c.
This is ONE ordinary six-tent low>=2 mean_upper candidate through its exact
stored-reader queries on ALL query branches, full mass.hi and final UP(high*mass.hi,P160).
CheckedBlockTable remains an explicit all-40 SAME-reader obligation.
No executable max-score/tie selector, saved leaf, all-min cell output, dispatch,
cover, tree, global allowance, lower compilation or main theorem is claimed.
-/
namespace ImbalancedChen.OriginalThirdSixTentOrdinaryMassCeilSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedOldWeightSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

/-- Exactly ln(F(x1,x0))*ln(F(y1,y0))*F(4*D*(z1-z0),z0*z1).
The two distinct logs and the left-associated V multiplications are retained.
The ordinary geometry below implies the producer's symmetric flag is false. -/
def literalOrdinaryMass (lo hi : Fin 3 → ℤ) : IV :=
  mul (mul (originalLnUnit ((hi 0:ℝ)/(lo 0:ℝ)))
    (originalLnUnit ((hi 1:ℝ)/(lo 1:ℝ)))) (literalMassZ (lo 2) (hi 2))

/-- The one mean_upper candidate's original integer mass ceiling. -/
def literalOrdinaryUpper (lo hi : Fin 3 → ℤ) (high : ℤ) : ℤ :=
  up (high*(literalOrdinaryMass lo hi).hi) P160

private theorem raw_positive (v : Fin 3 → ℤ) (D : ℤ) (p : BoxPoint)
    (hD : D=48000*2^24) (hp : ∀ i, p i=(v i:ℝ)/(D:ℝ))
    (hpositive : ∀ i, 0<p i) (i : Fin 3) : 0<v i := by
  have hDr : (0:ℝ)<(D:ℝ) := by rw [hD]; norm_num
  have h : (0:ℝ)<(v i:ℝ)/(D:ℝ) := by
    simpa only [← hp i] using hpositive i
  have hv : (0:ℝ)<(v i:ℝ) := (div_pos_iff_of_pos_right hDr).1 h
  exact_mod_cast hv

/-- Full ordinary mass: factor4 is paid once by literalMassZ. Both source
logs are enclosed by their unchanged 256-term no-range-reduction branch. -/
theorem literal_ordinary_mass_encloses
    (lo hi : Fin 3 → ℤ) (D : ℤ) (a b : BoxPoint)
    (hD : D=48000*2^24)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D:ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hratio : ∀ i : Fin 2, b i.castSucc/a i.castSucc≤2) :
    Encloses (literalOrdinaryMass lo hi) (4*boxMass a b) := by
  have hDr : (0:ℝ)<(D:ℝ) := by rw [hD]; norm_num
  have hposLo : ∀ i, 0<lo i := raw_positive lo D a hD haBind ha
  have hposHi : ∀ i, 0<hi i := raw_positive hi D b hD hbBind
    (fun i => (ha i).trans (hab i))
  have hratioEq (i : Fin 3) : b i/a i=(hi i:ℝ)/(lo i:ℝ) := by
    have hlo : (0:ℝ)<(lo i:ℝ) := by exact_mod_cast hposLo i
    rw [haBind i,hbBind i]
    exact producer_log_ratio (D:ℝ) (lo i:ℝ) (hi i:ℝ) hDr.ne' hlo.ne'
  have hlog (i : Fin 2) :
      Encloses (originalLnUnit ((hi i.castSucc:ℝ)/(lo i.castSucc:ℝ)))
        (Real.log (b i.castSucc/a i.castSucc)) := by
    rw [← hratioEq i.castSucc]
    exact original_positive256_ln_sound
      ((le_div_iff₀ (ha i.castSucc)).2 (by linarith [hab i.castSucc])) (hratio i)
  have hz0 : (0:ℝ)<(lo 2:ℝ) := by exact_mod_cast hposLo 2
  have hz1 : (0:ℝ)<(hi 2:ℝ) := by exact_mod_cast hposHi 2
  have hfactor :
      (((4*(48000*2^24:ℤ)*(hi 2-lo 2):ℤ):ℝ)/((lo 2*hi 2:ℤ):ℝ))=
        4*(b 2-a 2)/(a 2*b 2) := by
    rw [haBind 2,hbBind 2,hD]
    push_cast
    field_simp [hz0.ne',hz1.ne'] <;> ring
  have hraw := mul_sound (mul_sound (hlog 0) (hlog 1))
    (literalMassZ_sound (hposLo 2) (hposHi 2))
  have heq : Real.log (b 0/a 0)*Real.log (b 1/a 1)*
      (((4*(48000*2^24:ℤ)*(hi 2-lo 2):ℤ):ℝ)/((lo 2*hi 2:ℤ):ℝ))=
        4*boxMass a b := by
    rw [hfactor]
    unfold boxMass zMass
    ring
  rw [heq] at hraw
  exact hraw

/-- Under this actual ordinary geometry the raw x/y endpoints cannot have
both equalities used by symmetric=x0==y0 and x1==y1 and z1<=y0. -/
theorem ordinary_raw_not_symmetric
    (lo hi : Fin 3 → ℤ) (D : ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D:ℝ))
    (hab : ∀ i, a i<b i) (hyx : b 1≤a 0) :
    ¬(lo 0=lo 1 ∧ hi 0=hi 1) := by
  rintro ⟨hlo,hhi⟩
  have hae : a 0=a 1 := by rw [haBind 0,haBind 1,hlo]
  linarith [hab 1]

/-- Strict residual and positive widths identify and strictly order the SAME
original Fraction endpoints. No analytic endpoint choice is supplied. -/
theorem literal_tent_endpoint_span
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ)
    (D : ℤ) (a b : BoxPoint) (hD : D=48000*2^24)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D:ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hres : 0<oldNumerator s k b) :
    (literalTentEndpoint s k hi D:ℝ)<(literalTentEndpoint s k lo D:ℝ) := by
  have hDr : (0:ℝ)<(D:ℝ) := by rw [hD]; norm_num
  have hlo := raw_positive lo D a hD haBind ha 2
  have hhi := raw_positive hi D b hD hbBind (fun i => (ha i).trans (hab i)) 2
  have hloR : (0:ℝ)<(lo 2:ℝ) := by exact_mod_cast hlo
  have hhiR : (0:ℝ)<(hi 2:ℝ) := by exact_mod_cast hhi
  rw [literalTentEndpoint_cast s k hi D b hDr.ne' hhiR.ne' hbBind,
    literalTentEndpoint_cast s k lo D a hDr.ne' hloR.ne' haBind]
  exact original_tent_old_span s k a b ha hab hres

/-- The remaining low>=2 requirement is the actual OLD chord domain.
Together with the internally proved strict span, it pays ALL three original
mean_upper dispatch tests on exact Fractions: no crossing rejection, no
high<=2 early return, and no low==high fallback. It is not a query-range gate. -/
theorem ordinary_strict_chord_dispatch {low high : ℚ}
    (hlow : 2≤(low:ℝ)) (hspan : (low:ℝ)<(high:ℝ)) :
    ¬high≤2 ∧ ¬(low<2 ∧ 2<high) ∧ low≠high := by
  have hloQ : (2:ℚ)≤low := by exact_mod_cast hlow
  have hspanQ : low<high := by exact_mod_cast hspan
  refine ⟨not_le_of_gt (lt_of_le_of_lt hloQ hspanQ),?_,ne_of_lt hspanQ⟩
  rintro ⟨hl,_⟩
  exact (not_lt_of_ge hloQ) hl

/-- The SAME original reader at any exact Fraction: its own positive
canonical denominator supplies the only query-enclosure premise.
Both the zero clamp (including q=2) and terminal Hhi branch are retained. -/
theorem ordinary_fraction_query_encloses (table : CheckedBlockTable) (q : ℚ) :
    value (readQueryLo160 (assembledRead table.blocks) q.num (q.den:ℤ))≤
        actualExtendedThirdLowerFactor (q:ℝ) ∧
      actualExtendedThirdLowerFactor (q:ℝ)≤
        value (readQueryHi160 (assembledRead table.blocks) q.num (q.den:ℤ)) := by
  simpa only [value,P160,Int.cast_pow,Int.cast_ofNat] using
    CheckedBlockTable.rational_query_encloses_all table q

/-- SAME-reader assembly of both exact Fraction OLD queries and the original
NEW query at its UNREDUCED pair (new.hi,P160). There are no query-domain gates:
Fraction.den_pos and P160_pos discharge the true positive-denominator guards.
No query result, mean enclosure or desired integral bound is a premise. -/
theorem ordinary_three_stored_queries
    (table : CheckedBlockTable) (a b : BoxPoint) (low high : ℚ) :
    value (readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ))≤
        actualExtendedThirdLowerFactor (low:ℝ) ∧
      value (readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ))≤
        actualExtendedThirdLowerFactor (high:ℝ) ∧
      actualExtendedThirdLowerFactor (ordinaryNewQuery a b:ℝ)≤
        value (readQueryHi160 (assembledRead table.blocks) (ordinaryNew a b).hi P160) := by
  have hfl := (ordinary_fraction_query_encloses table low).1
  have hfh := (ordinary_fraction_query_encloses table high).1
  have hout := (CheckedBlockTable.query_encloses_all table (ordinaryNew a b).hi
    P160 P160_pos).2
  refine ⟨hfl,hfh,?_⟩
  simpa only [ordinaryNewQuery,Rat.cast_div,Rat.cast_intCast,value,P160,
    Int.cast_pow,Int.cast_ofNat] using hout

/-- Original ordinary tent candidate: literal integer branch/root/residual
 -> exact Fraction endpoints -> original OLD/NEW queries -> rounded/clipped
meanHigh -> literal full mass.hi -> final original integer UP.
The selected s/k and the all-40 table are honest remaining input obligations.
The saved fl/fh/out fields must equal those SAME-reader query expressions. -/
theorem original_selected_tent_stored_integer_upper
    (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ)
    (D T : ℤ) (a b : BoxPoint) (low high : ℚ) (fl fh out : ℤ)
    (hD : D=48000*2^24) (hT : T=481573208064)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D:ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (hbranch : match k with
      | .rise => -50*D+256*(literalTentX s*hi 0+literalTentY s*hi 1+literalTentZ s*hi 2)≤0
      | .fall => ¬(-50*D+256*(literalTentX s*hi 0+literalTentY s*hi 1+literalTentZ s*hi 2)≤0) ∧
          0≤-50*D+256*(literalTentX s*lo 0+literalTentY s*lo 1+literalTentZ s*lo 2))
    (hroot : match k with
      | .rise => D+literalTentX s*hi 0+literalTentY s*hi 1+literalTentZ s*hi 2≤2*T
      | .fall => 57*D-96*(literalTentX s*lo 0+literalTentY s*lo 1+literalTentZ s*lo 2)≤64*T)
    (hres : match k with
      | .rise => 0<D+(literalTentX s-2)*hi 0+(literalTentY s-2)*hi 1
      | .fall => 0<57*D+(-96*literalTentX s-64)*hi 0+(-96*literalTentY s-64)*hi 1)
    (hlowLiteral : low=literalTentEndpoint s k hi D)
    (hhighLiteral : high=literalTentEndpoint s k lo D)
    (hlow : 2≤(low:ℝ))
    (hratio : ∀ i : Fin 2, b i.castSucc/a i.castSucc≤2)
    (hpositive : ∀ i : Fin 2, 0<(originalLnUnit (b i.castSucc/a i.castSucc)).lo)
    (hflSaved : fl=readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ))
    (hfhSaved : fh=readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ))
    (houtSaved : out=readQueryHi160 (assembledRead table.blocks) (ordinaryNew a b).hi P160) :
    (∫ t in compactRegion ∩ Icc a b, compactKernel t)≤
      value (literalOrdinaryUpper lo hi (meanHigh
        (ordinaryTentWeight s k a b low high).lo
        (ordinaryTentWeight s k a b low high).hi fl fh out)) := by
  have hnotSym := ordinary_raw_not_symmetric lo hi D a b haBind hbBind hab hyx
  have hbelow : a 0<VariableEnvelope.mu := (hab 0).trans_le hmu
  have hguards := original_selected_tent_guard_bridge
    s k lo hi D T a b hD hT haBind hbBind hbranch hroot hres
  have hspan : (low:ℝ)<(high:ℝ) := by
    rw [hlowLiteral,hhighLiteral]
    exact literal_tent_endpoint_span s k lo hi D a b hD haBind hbBind ha hab hguards.2.2
  have hdispatch := ordinary_strict_chord_dispatch hlow hspan
  obtain ⟨hfl,hfh,hquery⟩ := ordinary_three_stored_queries table a b low high
  have hfl' : value fl≤actualExtendedThirdLowerFactor (low:ℝ) := by
    rw [hflSaved]
    exact hfl
  have hfh' : value fh≤actualExtendedThirdLowerFactor (high:ℝ) := by
    rw [hfhSaved]
    exact hfh
  have hquery' : actualExtendedThirdLowerFactor (ordinaryNewQuery a b:ℝ)≤value out := by
    rw [houtSaved]
    exact hquery
  have hleaf := original_selected_tent_rounded_mean_upper s k lo hi D T a b low high
    fl fh out hD hT haBind hbBind ha hab hcut hyx hzy hmu hfull hbranch hroot hres
    hlowLiteral hhighLiteral hlow hratio hpositive hfl' hfh' hquery'
  have hmass := (literal_ordinary_mass_encloses lo hi D a b hD haBind hbBind ha hab hratio).2
  have hhigh : 0≤value (meanHigh
      (ordinaryTentWeight s k a b low high).lo
      (ordinaryTentWeight s k a b low high).hi fl fh out) := by
    rw [meanHigh,value_max,value_zero]
    exact le_max_left _ _
  calc
    (∫ t in compactRegion ∩ Icc a b, compactKernel t)≤
        4*boxMass a b*value (meanHigh
          (ordinaryTentWeight s k a b low high).lo
          (ordinaryTentWeight s k a b low high).hi fl fh out) := hleaf
    _ ≤ value (literalOrdinaryMass lo hi).hi*value (meanHigh
          (ordinaryTentWeight s k a b low high).lo
          (ordinaryTentWeight s k a b low high).hi fl fh out) :=
      mul_le_mul_of_nonneg_right hmass hhigh
    _ = value (meanHigh
          (ordinaryTentWeight s k a b low high).lo
          (ordinaryTentWeight s k a b low high).hi fl fh out)*
        value (literalOrdinaryMass lo hi).hi := by ring
    _ ≤ value (literalOrdinaryUpper lo hi (meanHigh
          (ordinaryTentWeight s k a b low high).lo
          (ordinaryTentWeight s k a b low high).hi fl fh out)) :=
      literal_product_UP_ge _ _

end
end ImbalancedChen.OriginalThirdSixTentOrdinaryMassCeilSourceOnly