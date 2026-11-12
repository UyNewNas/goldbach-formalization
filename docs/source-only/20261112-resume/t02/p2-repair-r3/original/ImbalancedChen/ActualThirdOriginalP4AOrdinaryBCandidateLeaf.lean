import ImbalancedChen.ActualThirdOriginalBelowMuBMassCeil
import ImbalancedChen.ActualThirdOriginalStoredQueryAllBranches
import ImbalancedChen.ActualThirdOriginalPositive256LogRange32IntegerGuard

/-!
SOURCEONLY / UNCOMPILED / MAIN OPEN30.
The first import means the existing frozen 20261024m B ordinary-mass-ceil
draft and its B-rounded / Positive256LogRange32 dependencies. The second
means frozen 20261024w StoredQueryAllBranches. No table data is re-emitted.
This is the original baseline tuple (153,0,0,-96,256), not a tent tuple.
Only its ordinary low>=2 strict-chord branch is claimed. The selector's
winning tuple and the final box minimum remain separate.
-/
namespace ImbalancedChen.OriginalThirdP4AOrdinaryBCandidateSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdBelowMuBRoundedSourceOnly
open OriginalThirdBelowMuBMassCeilSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

/-- Literal original F(a*D+(b-q)*x+(d-q)*y+(e-q)*z,q*z)
for (a,b,d,e,q)=(153,0,0,-96,256). -/
def literalBEndpoint (v : Fin 3 → ℤ) (D : ℤ) : ℚ :=
  ((153*D-256*v 0-256*v 1-352*v 2:ℤ):ℚ)/((256*v 2:ℤ):ℚ)

/-- Raw saved-grid Fraction equals the existing B OLD endpoint expression.
The nonzero z condition is essential because subtraction follows division. -/
theorem literalBEndpoint_eq_bLowQ
    (v : Fin 3 → ℤ) (p : Fin 3 → ℚ)
    (hp : ∀ i, p i=(v i:ℚ)/((48000*2^24:ℤ):ℚ)) (hz : v 2≠0) :
    bLowQ p=literalBEndpoint v (48000*2^24) := by
  have hzQ : (v 2:ℚ)≠0 := by exact_mod_cast hz
  have hDq : (((48000*2^24:ℤ):ℚ))≠0 := by norm_num
  simp only [bLowQ,literalBEndpoint,hp]
  push_cast
  field_simp [hzQ,hDq] <;> ring

theorem literalBEndpoint_eq_bHighQ
    (v : Fin 3 → ℤ) (p : Fin 3 → ℚ)
    (hp : ∀ i, p i=(v i:ℚ)/((48000*2^24:ℤ):ℚ)) (hz : v 2≠0) :
    bHighQ p=literalBEndpoint v (48000*2^24) := by
  change bLowQ p=literalBEndpoint v (48000*2^24)
  exact literalBEndpoint_eq_bLowQ v p hp hz

/-- Exact root-filter test for B. It always survives for a nonnegative
lower z coordinate at the original D/T, including equality z=0. -/
theorem ordinary_B_literal_root (lo : Fin 3 → ℤ) (hz : 0≤lo 2) :
    153*(48000*2^24:ℤ)-96*lo 2≤256*481573208064 := by
  have hc : 153*(48000*2^24:ℤ)≤256*481573208064 := by norm_num
  nlinarith only [hz,hc]

/-- The producer's b>q and d>q rejection tests both fail for B. -/
theorem ordinary_B_literal_coefficient_guards :
    ¬(0:ℤ)>256 ∧ ¬(0:ℤ)>256 := by
  norm_num

/-- The original low_num positivity test, without assuming the residual.
These are exactly the integer mu bounds on the two upper coordinates. -/
theorem ordinary_B_literal_residual (hi : Fin 3 → ℤ)
    (hx : 128*hi 0≤25*(48000*2^24:ℤ))
    (hy : 128*hi 1≤25*(48000*2^24:ℤ)) :
    0<153*(48000*2^24:ℤ)-256*hi 0-256*hi 1 := by
  have hD : (0:ℤ)<48000*2^24 := by norm_num
  nlinarith only [hx,hy,hD]

/-- The real affine B leaf, with its strict span proved from geometry.
The actual cap-minorant and OLD range are supplied by the existing B
analytic module, rather than accepted as semantic caller hypotheses. -/
theorem ordinary_B_full_leaf_old_chord_upper (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (flo fhi out : ℝ) (hlo : 2≤bOldLow b)
    (hfl : flo≤actualExtendedThirdLowerFactor (bOldLow b))
    (hfh : fhi≤actualExtendedThirdLowerFactor (bOldHigh a))
    (hout : actualExtendedThirdLowerFactor
      ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1)≤out) :
    (∫ t in compactRegion ∩ Icc a b, compactKernel t)≤
      4*boxMass a b*max 0 (out-bOldChord a b flo fhi) := by
  exact original_below_mu_B_leaf_candidate a b ha hab hcut hyx hzy hmu hfull
    flo fhi out hlo (below_mu_B_old_span a b ha hab hyx hmu) hfl hfh hout

/-- Binding of both literal original Fractions to the saved rational
coordinate rows. No value of the factor or any saved query is assumed. -/
theorem ordinary_B_endpoints_eq_literal
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i, a i=(lo i:ℚ)/((48000*2^24:ℤ):ℚ))
    (hbBind : ∀ i, b i=(hi i:ℚ)/((48000*2^24:ℤ):ℚ))
    (ha2 : 0<realBox a 2) (hb2 : 0<realBox b 2) :
    bLowQ b=literalBEndpoint hi (48000*2^24) ∧
      bHighQ a=literalBEndpoint lo (48000*2^24) := by
  have hlo2 : lo 2≠0 := by
    intro hz
    have ha0 : a 2=0 := by rw [haBind 2,hz]; simp
    have hbad : (0:ℝ)<0 := by simpa only [realBox,ha0,Rat.cast_zero] using ha2
    exact (lt_irrefl (0:ℝ)) hbad
  have hhi2 : hi 2≠0 := by
    intro hz
    have hb0 : b 2=0 := by rw [hbBind 2,hz]; simp
    have hbad : (0:ℝ)<0 := by simpa only [realBox,hb0,Rat.cast_zero] using hb2
    exact (lt_irrefl (0:ℝ)) hbad
  exact ⟨literalBEndpoint_eq_bLowQ hi b hbBind hhi2,
    literalBEndpoint_eq_bHighQ lo a haBind hlo2⟩

/-- All non-chord B source tests, transported from the actual stored-row
geometry. Thus root/residual conclusions need not be assumed by a caller. -/
theorem ordinary_B_saved_source_guards
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i, a i=(lo i:ℚ)/((48000*2^24:ℤ):ℚ))
    (hbBind : ∀ i, b i=(hi i:ℚ)/((48000*2^24:ℤ):ℚ))
    (ha2 : 0<realBox a 2) (hab0 : realBox a 0<realBox b 0)
    (hyx : realBox b 1≤realBox a 0)
    (hmu : realBox b 0≤VariableEnvelope.mu) :
    153*(48000*2^24:ℤ)-96*lo 2≤256*481573208064 ∧
      0<153*(48000*2^24:ℤ)-256*hi 0-256*hi 1 := by
  have hD : (0:ℝ)<((48000*2^24:ℤ):ℝ) := by norm_num
  have haR : realBox a 2=(lo 2:ℝ)/((48000*2^24:ℤ):ℝ) := by
    dsimp only [realBox]
    rw [haBind 2]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hbR (i : Fin 3) : realBox b i=(hi i:ℝ)/((48000*2^24:ℤ):ℝ) := by
    dsimp only [realBox]
    rw [hbBind i]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hzR : (0:ℝ)<(lo 2:ℝ) :=
    (div_pos_iff_of_pos_right hD).1 (by simpa only [haR] using ha2)
  have hz : (0:ℤ)<lo 2 := by exact_mod_cast hzR
  have hymu : realBox b 1≤VariableEnvelope.mu := hyx.trans (hab0.le.trans hmu)
  have hxR : (128:ℝ)*(hi 0:ℝ)≤25*((48000*2^24:ℤ):ℝ) := by
    have hx := (div_le_iff₀ hD).1
      (by simpa only [hbR 0,VariableEnvelope.mu] using hmu :
        (hi 0:ℝ)/((48000*2^24:ℤ):ℝ)≤25/128)
    linarith only [hx]
  have hyR : (128:ℝ)*(hi 1:ℝ)≤25*((48000*2^24:ℤ):ℝ) := by
    have hy := (div_le_iff₀ hD).1
      (by simpa only [hbR 1,VariableEnvelope.mu] using hymu :
        (hi 1:ℝ)/((48000*2^24:ℤ):ℝ)≤25/128)
    linarith only [hy]
  have hx : 128*hi 0≤25*(48000*2^24:ℤ) := by exact_mod_cast hxR
  have hy : 128*hi 1≤25*(48000*2^24:ℤ) := by exact_mod_cast hyR
  exact ⟨ordinary_B_literal_root lo hz.le,ordinary_B_literal_residual hi hx hy⟩

/-- Each field is the producer query on one immutable checked table. -/
def bStoredFl (table : CheckedBlockTable) (b : Fin 3 → ℚ) : ℤ :=
  readQueryLo160 (assembledRead table.blocks) (bLowQ b).num ((bLowQ b).den:ℤ)
def bStoredFh (table : CheckedBlockTable) (a : Fin 3 → ℚ) : ℤ :=
  readQueryLo160 (assembledRead table.blocks) (bHighQ a).num ((bHighQ a).den:ℤ)
def bStoredOut (table : CheckedBlockTable) (a b : Fin 3 → ℚ) : ℤ :=
  readQueryHi160 (assembledRead table.blocks)
    (roundedNew (realBox a) (realBox b)
      (originalLn32 (realBox b 0/realBox a 0))
      (originalLn32 (realBox b 1/realBox a 1))).hi P160

theorem bStoredFl_eq_literal (table : CheckedBlockTable)
    (hi : Fin 3 → ℤ) (b : Fin 3 → ℚ)
    (hbBind : ∀ i, b i=(hi i:ℚ)/((48000*2^24:ℤ):ℚ)) (hz : hi 2≠0) :
    bStoredFl table b=readQueryLo160 (assembledRead table.blocks)
      (literalBEndpoint hi (48000*2^24)).num
      ((literalBEndpoint hi (48000*2^24)).den:ℤ) := by
  unfold bStoredFl
  rw [literalBEndpoint_eq_bLowQ hi b hbBind hz]

theorem bStoredFh_eq_literal (table : CheckedBlockTable)
    (lo : Fin 3 → ℤ) (a : Fin 3 → ℚ)
    (haBind : ∀ i, a i=(lo i:ℚ)/((48000*2^24:ℤ):ℚ)) (hz : lo 2≠0) :
    bStoredFh table a=readQueryLo160 (assembledRead table.blocks)
      (literalBEndpoint lo (48000*2^24)).num
      ((literalBEndpoint lo (48000*2^24)).den:ℤ) := by
  unfold bStoredFh
  rw [literalBEndpoint_eq_bHighQ lo a haBind hz]

/-- All original query branches, including high>12 and NEW zero clamp.
The OLD Fraction denominators and unreduced NEW P160 denominator supply
their own positive-denominator guards internally. -/
theorem ordinary_B_three_stored_queries
    (table : CheckedBlockTable) (a b : Fin 3 → ℚ) :
    value (bStoredFl table b)≤actualExtendedThirdLowerFactor (bOldLow (realBox b)) ∧
    value (bStoredFh table a)≤actualExtendedThirdLowerFactor (bOldHigh (realBox a)) ∧
    actualExtendedThirdLowerFactor
      (newQuery (realBox a) (realBox b)
        (originalLn32 (realBox b 0/realBox a 0))
        (originalLn32 (realBox b 1/realBox a 1)):ℝ)≤value (bStoredOut table a b) := by
  have hfl := (CheckedBlockTable.rational_query_encloses_all table (bLowQ b)).1
  have hfh := (CheckedBlockTable.rational_query_encloses_all table (bHighQ a)).1
  have hout := (CheckedBlockTable.query_encloses_all table
    (roundedNew (realBox a) (realBox b)
      (originalLn32 (realBox b 0/realBox a 0))
      (originalLn32 (realBox b 1/realBox a 1))).hi P160 P160_pos).2
  refine ⟨?_,?_,?_⟩
  · simpa only [bStoredFl,value,P160,Int.cast_pow,Int.cast_ofNat,cast_bLowQ] using hfl
  · simpa only [bStoredFh,value,P160,Int.cast_pow,Int.cast_ofNat,cast_bHighQ] using hfh
  · simpa only [bStoredOut,newQuery,Rat.cast_div,Rat.cast_intCast,value,
      P160,Int.cast_pow,Int.cast_ofNat] using hout

/-- Consumer API for the exact selector's B winner. It covers arbitrary
original ordinary B boxes, preserving ln's original range32 implementation,
the two original positive integer divisors, OLD low>=2 and full geometry.
The exact OLD/NEW queries, rounded chord, full mass.hi and final integer UP
are proved internally. A selected-winner proof may be supplied by the
selector separately; no selected tuple or saved target is assumed here. -/
theorem ordinary_B_stored_integer_upper
    (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i, a i=(lo i:ℚ)/((48000*2^24:ℤ):ℚ))
    (hbBind : ∀ i, b i=(hi i:ℚ)/((48000*2^24:ℤ):ℚ))
    (ha : ∀ i, 0<realBox a i) (hab : ∀ i, realBox a i<realBox b i)
    (hcut : (1:ℝ)/100≤realBox a 2)
    (hyx : realBox b 1≤realBox a 0) (hzy : realBox b 2≤realBox a 1)
    (hmu : realBox b 0≤VariableEnvelope.mu)
    (hfull : realBox b 0+realBox b 1+3*realBox b 2≤thirdPrefixTheta)
    (hpx : 0<(originalLn32 (realBox b 0/realBox a 0)).lo)
    (hpy : 0<(originalLn32 (realBox b 1/realBox a 1)).lo)
    (hlo : 2≤bOldLow (realBox b)) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (literalOrdinaryUpper lo hi (meanHigh
        (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
          (originalLn32 (realBox b 1/realBox a 1))).lo
        (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
          (originalLn32 (realBox b 1/realBox a 1))).hi
        (bStoredFl table b) (bStoredFh table a) (bStoredOut table a b))) := by
  have hbind := ordinary_B_endpoints_eq_literal lo hi a b haBind hbBind
    (ha 2) ((ha 2).trans (hab 2))
  have hguards := ordinary_B_saved_source_guards lo hi a b haBind hbBind
    (ha 2) (hab 0) hyx hmu
  obtain ⟨hfl,hfh,hquery⟩ := ordinary_B_three_stored_queries table a b
  exact original_below_mu_B_leaf_integer_upper lo hi a b
    (bStoredFl table b) (bStoredFh table a) (bStoredOut table a b)
    haBind hbBind ha hab hcut hyx hzy hmu hfull hpx hpy hlo hfl hfh hquery

/-- Original-grid entry point: even the raw ln32 integer divisor guards
are supplied by the existing genuine guard theorem. Only the OLD chord's
actual low>=2 condition and original ordinary/full geometry remain. -/
theorem ordinary_B_stored_integer_upper_of_grid
    (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i, a i=(lo i:ℚ)/((48000*2^24:ℤ):ℚ))
    (hbBind : ∀ i, b i=(hi i:ℚ)/((48000*2^24:ℤ):ℚ))
    (ha : ∀ i, 0<realBox a i) (hab : ∀ i, realBox a i<realBox b i)
    (hcut : (1:ℝ)/100≤realBox a 2)
    (hyx : realBox b 1≤realBox a 0) (hzy : realBox b 2≤realBox a 1)
    (hmu : realBox b 0≤VariableEnvelope.mu)
    (hfull : realBox b 0+realBox b 1+3*realBox b 2≤thirdPrefixTheta)
    (hlo : 2≤bOldLow (realBox b)) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (literalOrdinaryUpper lo hi (meanHigh
        (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
          (originalLn32 (realBox b 1/realBox a 1))).lo
        (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
          (originalLn32 (realBox b 1/realBox a 1))).hi
        (bStoredFl table b) (bStoredFh table a) (bStoredOut table a b))) := by
  have hr := below_mu_B_log_ratios (realBox a) (realBox b)
    ha hab hcut hyx hzy hmu
  have hg := original_stored_ordinary_log32_guards lo hi a b haBind hbBind
    ha hab hyx (by simpa only [VariableEnvelope.mu] using hmu) hr.1.2 hr.2.2
  exact ordinary_B_stored_integer_upper table lo hi a b haBind hbBind
    ha hab hcut hyx hzy hmu hfull hg.1 hg.2 hlo

end
end ImbalancedChen.OriginalThirdP4AOrdinaryBCandidateSourceOnly
