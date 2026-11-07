import ImbalancedChen.ActualThirdOriginalOrdinaryOldChord

/-!
SOURCEONLY / HOLD_ELABORATION / MAIN OPEN30.
The actual below-mu B(z) plane in original minorant(), for an ordinary full
leaf. Derive the real old range and cap minorant instead of assuming either.
Append once to the exact ordinary OLD chord parent; no new imports required.
-/
namespace ImbalancedChen.OriginalThirdBelowMuBCandidateSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdOldChordMeanSourceOnly
open OriginalThirdCompactPartitionSourceOnly

/-- Original tuple (153,0,0,-96,256), after subtracting x+y+z and dividing by z.
The constant is (e-q)/q=(-96-256)/256=-11/8. -/
def bOldArgument (t : BoxPoint) : ℝ :=
  affineArgument (153/256) (-1) (-1) (-11/8) t

def bOldLow (b : BoxPoint) : ℝ := bOldArgument b
def bOldHigh (a : BoxPoint) : ℝ := bOldArgument a

def bOldMean (a b : BoxPoint) : ℝ :=
  (153/256-boxEX a b-boxEY a b)*boxEZInv a b-11/8

def bOldChord (a b : BoxPoint) (flo fhi : ℝ) : ℝ :=
  flo+(bOldMean a b-bOldLow b)/(bOldHigh a-bOldLow b)*(fhi-flo)

/-- On the true below-mu ordered box B survives the actual gated envelope and
the root minimum. Equality at mu uses the manuscript's full-envelope side. -/
theorem below_mu_B_le_actual_cap (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu) {t : BoxPoint} (ht : t∈Icc a b) :
    VariableEnvelope.B (t 2)≤
      actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) := by
  have hz : 0<t 2 := (ha 2).trans_le (ht.1 2)
  have hzy' : t 2≤t 1 := (ht.2 2).trans (hzy.trans (ht.1 1))
  have hyx' : t 1≤t 0 := (ht.2 1).trans (hyx.trans (ht.1 0))
  have hxmu : t 0≤VariableEnvelope.mu := (ht.2 0).trans hmu
  have hordered : VariableEnvelope.Ordered (t 0) (t 1) (t 2) :=
    ⟨hz.le,hzy',hyx',hxmu⟩
  unfold actualExtendedThirdBufferedCap thirdPrefixBufferedCap
  simp only [mul_zero,sub_zero]
  apply le_min
  · dsimp [VariableEnvelope.B,VariableEnvelope.cap,thirdPrefixTheta]
    linarith
  · rw [actualExtendedThirdEnvelope_eq_six hordered]
    exact VariableEnvelope.B_le_six (t 0) (t 1) (t 2)

/-- The original residual-numerator check is automatic for this plane below
mu. Both OLD endpoint inequalities follow from positive denominators and the
signs -1,-1 of the x,y coefficients; no argument-range premise is accepted. -/
theorem below_mu_B_old_range (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hyx : b 1≤a 0) (hmu : b 0≤VariableEnvelope.mu)
    {t : BoxPoint} (ht : t∈Icc a b) :
    bOldArgument t∈Icc (bOldLow b) (bOldHigh a) := by
  have hz : 0<t 2 := (ha 2).trans_le (ht.1 2)
  have hb1mu : b 1≤VariableEnvelope.mu :=
    hyx.trans ((hab 0).le.trans hmu)
  have hnum : 0<(153:ℝ)/256-b 0-b 1 := by
    dsimp [VariableEnvelope.mu] at hmu hb1mu
    linarith
  have hlow : (153:ℝ)/256-b 0-b 1≤(153:ℝ)/256-t 0-t 1 := by
    linarith [ht.2 0,ht.2 1]
  have hhigh : (153:ℝ)/256-t 0-t 1≤(153:ℝ)/256-a 0-a 1 := by
    linarith [ht.1 0,ht.1 1]
  have hl := div_le_div₀ (hnum.le.trans hlow) hlow hz (ht.2 2)
  have hh := div_le_div₀ ((hnum.le.trans hlow).trans hhigh) hhigh (ha 2) (ht.1 2)
  constructor
  · simp only [bOldLow,bOldArgument,affineArgument,neg_one_mul,← sub_eq_add_neg]
    linarith [hl]
  · simp only [bOldHigh,bOldArgument,affineArgument,neg_one_mul,← sub_eq_add_neg]
    linarith [hh]

/-- Nondegenerate original ordinary B boxes have a strict OLD span. Thus the
equal-span exception is absent from this branch; it need not be postulated. -/
theorem below_mu_B_old_span (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hyx : b 1≤a 0) (hmu : b 0≤VariableEnvelope.mu) :
    bOldLow b<bOldHigh a := by
  have hb2 : 0<b 2 := (ha 2).trans (hab 2)
  have hb1mu : b 1≤VariableEnvelope.mu :=
    hyx.trans ((hab 0).le.trans hmu)
  have hnum : 0<(153:ℝ)/256-b 0-b 1 := by
    dsimp [VariableEnvelope.mu] at hmu hb1mu
    linarith
  have hnumlt : (153:ℝ)/256-b 0-b 1<(153:ℝ)/256-a 0-a 1 := by
    linarith [hab 0,hab 1]
  have hfirst := (div_lt_div_iff_of_pos_right hb2).2 hnumlt
  have hsecond := div_le_div₀ (hnum.trans hnumlt).le
    (le_refl ((153:ℝ)/256-a 0-a 1)) (ha 2) (hab 2).le
  simp only [bOldLow,bOldHigh,bOldArgument,affineArgument,neg_one_mul,← sub_eq_add_neg]
  linarith [hfirst.trans_le hsecond]

/-- The B argument is below the ACTUAL old argument, not merely below a
reduced surrogate. Its cap inequality was supplied from the gated definition. -/
theorem below_mu_B_old_minorant (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu) {t : BoxPoint} (ht : t∈Icc a b) :
    bOldArgument t≤actualOldArgument t := by
  have hz : 0<t 2 := (ha 2).trans_le (ht.1 2)
  have hc := below_mu_B_le_actual_cap a b ha hyx hzy hmu ht
  have heq : bOldArgument t=
      (VariableEnvelope.B (t 2)-t 0-t 1-t 2)/t 2 := by
    unfold bOldArgument affineArgument VariableEnvelope.B VariableEnvelope.cap
    field_simp [hz.ne']
    ring
  rw [heq]
  unfold actualOldArgument
  exact (div_le_div_iff_of_pos_right hz).2 (by linarith)

/-- The original ordinary OLD mean for this actual plane is an integral
identity under the original reciprocal density; it is not an input bound. -/
theorem below_mu_B_old_mean (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i) :
    (∫ t, bOldArgument t ∂boxProbability a b)=bOldMean a b := by
  unfold bOldArgument
  rw [boxProbability_affine_mean a b ha hab]
  unfold bOldMean
  ring

/-- One genuinely missing original mean_upper branch: the below-mu ordinary
full leaf with selected B plane and 2<=low<high. Geometry supplies both old
range and old-minorant obligations internally. Only genuine factor query
values and the NEW upper-query transport remain as numerical interfaces. -/
theorem original_below_mu_B_leaf_candidate (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (flo fhi out : ℝ) (hlo : 2≤bOldLow b) (hspan : bOldLow b<bOldHigh a)
    (hfl : flo≤actualExtendedThirdLowerFactor (bOldLow b))
    (hfh : fhi≤actualExtendedThirdLowerFactor (bOldHigh a))
    (hout : actualExtendedThirdLowerFactor
      ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1)≤out) :
    (∫ t in compactRegion ∩ Icc a b, compactKernel t)≤
      4*boxMass a b*max 0 (out-bOldChord a b flo fhi) := by
  have hrho : b 0≤thirdPrefixRho := hmu.trans (by
    norm_num [VariableEnvelope.mu,thirdPrefixRho])
  have hrange : ∀ t∈Icc a b,
      affineArgument (153/256) (-1) (-1) (-11/8) t∈
        Icc (bOldLow b) (bOldHigh a) := by
    intro t ht
    exact below_mu_B_old_range a b ha hab hyx hmu ht
  have hminor : ∀ t∈Icc a b,
      affineArgument (153/256) (-1) (-1) (-11/8) t≤actualOldArgument t := by
    intro t ht
    exact below_mu_B_old_minorant a b ha hyx hzy hmu ht
  have hleaf := ordinary_full_leaf_old_chord_upper a b ha hab hcut hyx hzy hrho hfull
    (153/256) (-1) (-1) (-11/8) (bOldLow b) (bOldHigh a) flo fhi out
    hlo hspan hrange hminor hfl hfh hout
  have hchord : oldChordMean a b (153/256) (-1) (-1) (-11/8)
      (bOldLow b) (bOldHigh a) flo fhi=bOldChord a b flo fhi := by
    unfold oldChordMean oldAffineMean bOldChord bOldMean
    ring
  rw [hchord] at hleaf
  exact hleaf

/-- The analytic B-plane candidate with NO assumed NEW mean upper bound.
The actual factor at the proved Jensen mean is the resulting upper value.
The stored producer replaces it by an outward upper query; that further
arithmetic/query transport is not silently assumed by this endpoint. -/
theorem original_below_mu_B_leaf_exact_candidate (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (flo fhi : ℝ) (hlo : 2≤bOldLow b)
    (hfl : flo≤actualExtendedThirdLowerFactor (bOldLow b))
    (hfh : fhi≤actualExtendedThirdLowerFactor (bOldHigh a)) :
    (∫ t in compactRegion ∩ Icc a b, compactKernel t)≤
      4*boxMass a b*max 0
        (actualExtendedThirdLowerFactor
          ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1)-
        bOldChord a b flo fhi) := by
  exact original_below_mu_B_leaf_candidate a b ha hab hcut hyx hzy hmu hfull
    flo fhi _ hlo (below_mu_B_old_span a b ha hab hyx hmu) hfl hfh le_rfl

end
end ImbalancedChen.OriginalThirdBelowMuBCandidateSourceOnly
