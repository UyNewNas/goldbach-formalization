import ImbalancedChen.ActualThirdOriginalLiteralTentSelectorGuardBridge
import ImbalancedChen.ActualThirdOriginalRoundedOldWeight

/-!
SOURCEONLY / HOLD_ELABORATION / UNCOMPILED / MAIN OPEN30.
One ordinary six-tent mean_upper consumer, in the original P160 units.
The first import is the separate 20261024q guard-bridge SOURCEONLY draft;
ROOT must install/qualify that dependency before compiling this file.

Exact producer: numerical-third-compact-independent-20261010.py, SHA256
005fcc24c3431753e2530ab90f70e80d2256b3691cd45d14e13eb9191b0caa7c,
minorant/mean_upper lines 99--133. This file covers the ordinary low>=2
strict-chord branch only. It does not assert a saved row, table query,
max-score selector, mass ceiling, other mean_upper branch or certificate.
-/
namespace ImbalancedChen.OriginalThirdSixTentRoundedConsumerSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedOldWeightSourceOnly
open OriginalThirdCompactPartitionSourceOnly

/-- Literal ex/ey: V(width)/ln(ratio), with the original reciprocal-V division. -/
def ordinaryEx (a b : BoxPoint) (i : Fin 3) : IV :=
  divide (ofReal (b i-a i)) (originalLnUnit (b i/a i))

/-- Literal new=(V(TH)-ex-ey)*invz-1. -/
def ordinaryNew (a b : BoxPoint) : IV :=
  sub (mul (sub (sub (ofReal thirdPrefixTheta) (ordinaryEx a b 0))
    (ordinaryEx a b 1)) (ofReal (boxEZInv a b))) (ofReal 1)

/-- The ordinary (not ordered-max) OLD line of the original producer.
For rational scalar * interval, __rmul__ puts the interval operand first. -/
def ordinaryTentOld (s : TentSum) (k : TentSide) (a b : BoxPoint) : IV :=
  add (mul (add (add (ofReal (planeConst k))
    (mul (ordinaryEx a b 0) (ofReal (oldX s k))))
    (mul (ordinaryEx a b 1) (ofReal (oldY s k))))
    (ofReal (boxEZInv a b))) (ofReal (oldZ s k))

/-- low/high are the producer's exact rational endpoints, before V.co. -/
def ordinaryTentWeight (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (low high : ℚ) : IV :=
  divRat (sub (ordinaryTentOld s k a b) (ofReal (low : ℝ))) (high-low)

/-- Exact argument to sieve.at(new.hi,P), including P=2^160. -/
def ordinaryNewQuery (a b : BoxPoint) : ℚ :=
  ((ordinaryNew a b).hi : ℚ)/(P160 : ℚ)

/-- Literal Fraction old endpoint from the selected original tuple p:
F(a*D+(b-q)*v0+(d-q)*v1+(e-q)*v2,q*v2).
The SAME function is evaluated at hi for low and at lo for high. -/
def literalTentEndpoint (s : TentSum) (k : TentSide) (v : Fin 3 → ℤ)
    (D : ℤ) : ℚ :=
  match k with
  | .rise =>
      ((D+(literalTentX s-2)*v 0+(literalTentY s-2)*v 1+
        (literalTentZ s-2)*v 2 : ℤ) : ℚ)/((2*v 2 : ℤ) : ℚ)
  | .fall =>
      ((57*D+(-96*literalTentX s-64)*v 0+(-96*literalTentY s-64)*v 1+
        (-96*literalTentZ s-64)*v 2 : ℤ) : ℚ)/((64*v 2 : ℤ) : ℚ)

/-- Representation identity; no range, cap or endpoint-factor estimate is input. -/
theorem literalTentEndpoint_cast (s : TentSum) (k : TentSide)
    (v : Fin 3 → ℤ) (D : ℤ) (p : BoxPoint)
    (hD : (D:ℝ)≠0) (hv : (v 2:ℝ)≠0)
    (hp : ∀ i, p i=(v i:ℝ)/(D:ℝ)) :
    (literalTentEndpoint s k v D : ℝ)=tentOldArgument s k p := by
  cases k <;>
    simp only [literalTentEndpoint,Rat.cast_div,Rat.cast_intCast] <;>
    unfold tentOldArgument affineArgument oldX oldY oldZ planeConst planeSlope <;>
    rw [hp 0,hp 1,hp 2,←literalTentX_cast s,←literalTentY_cast s,
      ←literalTentZ_cast s] <;>
    push_cast <;>
    field_simp [hD,hv] <;>
    ring

theorem ordinaryEx_encloses (a b : BoxPoint) (i : Fin 3)
    (ha : 0<a i) (hab : a i<b i) (hratio : b i/a i≤2)
    (hpositive : 0<(originalLnUnit (b i/a i)).lo) :
    Encloses (ordinaryEx a b i) ((b i-a i)/Real.log (b i/a i)) := by
  have hlog := original_positive256_ln_sound
    ((le_div_iff₀ ha).2 (by linarith)) hratio
  exact divide_sound (ofReal_sound (b i-a i)) hlog hpositive

/-- Derives the NEW and OLD enclosures from the literal log/V operations.
No NEW mean, OLD mean or raw weight enclosure is a caller premise. -/
theorem ordinary_tent_means_enclose (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hratio : ∀ i : Fin 2, b i.castSucc/a i.castSucc≤2)
    (hpositive : ∀ i : Fin 2, 0<(originalLnUnit (b i.castSucc/a i.castSucc)).lo) :
    Encloses (ordinaryNew a b)
        ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1) ∧
      Encloses (ordinaryTentOld s k a b) (tentOldMean s k a b) := by
  have hex : Encloses (ordinaryEx a b 0) (boxEX a b) :=
    ordinaryEx_encloses a b 0 (ha 0) (hab 0) (hratio 0) (hpositive 0)
  have hey : Encloses (ordinaryEx a b 1) (boxEY a b) :=
    ordinaryEx_encloses a b 1 (ha 1) (hab 1) (hratio 1) (hpositive 1)
  constructor
  · exact sub_sound (mul_sound
      (sub_sound (sub_sound (ofReal_sound thirdPrefixTheta) hex) hey)
      (ofReal_sound (boxEZInv a b))) (ofReal_sound 1)
  · have h := add_sound (mul_sound
      (add_sound (add_sound (ofReal_sound (planeConst k))
        (mul_sound hex (ofReal_sound (oldX s k))))
        (mul_sound hey (ofReal_sound (oldY s k))))
      (ofReal_sound (boxEZInv a b))) (ofReal_sound (oldZ s k))
    have heq : (planeConst k+boxEX a b*oldX s k+boxEY a b*oldY s k)*
        boxEZInv a b+oldZ s k=tentOldMean s k a b := by
      unfold tentOldMean
      ring
    simpa only [ordinaryTentOld,heq] using h

/-- The actual ordinary reciprocal probability law, not a guessed center,
justifies clipping wt to [0,1]. Strict span follows from the positive
low_num residual and strictly positive box widths, even at low=2. -/
theorem tentOldMean_mem_range (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i) (hres : 0<oldNumerator s k b) :
    tentOldMean s k a b∈Icc (tentOldLow s k b) (tentOldHigh s k a) := by
  let : IsProbabilityMeasure (boxProbability a b) :=
    boxProbability_isProbability a b ha hab
  have hx : ContinuousOn (fun t : BoxPoint => t 0) (Icc a b) :=
    (continuous_apply 0).continuousOn
  have hy : ContinuousOn (fun t : BoxPoint => t 1) (Icc a b) :=
    (continuous_apply 1).continuousOn
  have hz : ContinuousOn (fun t : BoxPoint => t 2) (Icc a b) :=
    (continuous_apply 2).continuousOn
  have hc : ContinuousOn (tentOldArgument s k) (Icc a b) := by
    exact (((continuousOn_const.add (hx.const_mul (oldX s k))).add
      (hy.const_mul (oldY s k))).div hz
      (fun t ht => ((ha 2).trans_le (ht.1 2)).ne')).add continuousOn_const
  have hi := integrable_boxProbability_of_continuousOn a b ha hab hc
  have hr : ∀ᵐ t ∂boxProbability a b,
      tentOldArgument s k t∈Icc (tentOldLow s k b) (tentOldHigh s k a) :=
    (boxProbability_ae_mem a b).mono
      (fun t ht => original_tent_old_range s k a b ha hres ht)
  have hl := integral_mono_ae (integrable_const (tentOldLow s k b)) hi
    (hr.mono (fun _ ht => ht.1))
  have hh := integral_mono_ae hi (integrable_const (tentOldHigh s k a))
    (hr.mono (fun _ ht => ht.2))
  rw [original_tent_old_mean s k a b ha hab] at hl hh
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
    at hl hh
  exact ⟨hl,hh⟩

/-- This consumer retains the original if/elif, root and low_num tests.
The three sieve-query answers refer to their exact original arguments.
Rational equalities bind low/high to the selected plane's original literal
Fraction endpoints; their semantic cast identities are proved internally.

The conclusion is the original integer mean_upper candidate, before mass.hi
and its final UP product. In particular it does not call a symmetric consumer.
The selected s/k and max-score/tie choice remain record-binding obligations. -/
theorem original_selected_tent_rounded_mean_upper
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
    (hfl : value fl≤actualExtendedThirdLowerFactor (low:ℝ))
    (hfh : value fh≤actualExtendedThirdLowerFactor (high:ℝ))
    (hquery : actualExtendedThirdLowerFactor (ordinaryNewQuery a b:ℝ)≤value out) :
    (∫ t in compactRegion ∩ Icc a b, compactKernel t)≤
      4*boxMass a b*value (meanHigh
        (ordinaryTentWeight s k a b low high).lo
        (ordinaryTentWeight s k a b low high).hi fl fh out) := by
  obtain ⟨hactive,hupper,hresidual⟩ := original_selected_tent_guard_bridge
    s k lo hi D T a b hD hT haBind hbBind hbranch hroot hres
  have hDpos : (0:ℝ)<(D:ℝ) := by rw [hD]; norm_num
  have hlo2 : (lo 2:ℝ)≠0 := by
    have hp : (0:ℝ)<(lo 2:ℝ)/(D:ℝ) := by simpa only [← haBind 2] using ha 2
    exact ((div_pos_iff_of_pos_right hDpos).1 hp).ne'
  have hhi2 : (hi 2:ℝ)≠0 := by
    have hp : (0:ℝ)<(hi 2:ℝ)/(D:ℝ) := by
      simpa only [← hbBind 2] using (ha 2).trans (hab 2)
    exact ((div_pos_iff_of_pos_right hDpos).1 hp).ne'
  have hlowBind : (low:ℝ)=tentOldLow s k b := by
    rw [hlowLiteral]
    exact literalTentEndpoint_cast s k hi D b hDpos.ne' hhi2 hbBind
  have hhighBind : (high:ℝ)=tentOldHigh s k a := by
    rw [hhighLiteral]
    exact literalTentEndpoint_cast s k lo D a hDpos.ne' hlo2 haBind
  have hspan := original_tent_old_span s k a b ha hab hresidual
  have hspanQ : (0:ℚ)<high-low := by
    have hreal : (0:ℝ)<((high-low:ℚ):ℝ) := by
      simpa only [Rat.cast_sub,hlowBind,hhighBind] using sub_pos.mpr hspan
    exact_mod_cast hreal
  have hm := ordinary_tent_means_enclose s k a b ha hab hratio hpositive
  have hw : Encloses (ordinaryTentWeight s k a b low high)
      ((tentOldMean s k a b-tentOldLow s k b)/
        (tentOldHigh s k a-tentOldLow s k b)) := by
    simpa only [ordinaryTentWeight,Rat.cast_sub,hlowBind,hhighBind] using
      (divRat_sound (sub_sound hm.2 (ofReal_sound (low:ℝ))) hspanQ)
  have hr := tentOldMean_mem_range s k a b ha hab hresidual
  have hw0 : 0≤(tentOldMean s k a b-tentOldLow s k b)/
      (tentOldHigh s k a-tentOldLow s k b) :=
    div_nonneg (sub_nonneg.mpr hr.1) (sub_pos.mpr hspan).le
  have hw1 : (tentOldMean s k a b-tentOldLow s k b)/
      (tentOldHigh s k a-tentOldLow s k b)≤1 :=
    (div_le_one (sub_pos.mpr hspan)).2 (by linarith [hr.2])
  have hround := meanHigh_sound (fl:=fl) (fh:=fh) (out:=out) hw0 hw1 hw.1 hw.2
  have hmeanQuery :
      (thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1≤
        (ordinaryNewQuery a b:ℝ) := by
    simpa only [ordinaryNewQuery,Rat.cast_div,Rat.cast_intCast,value] using hm.1.2
  have hout := actual_new_mean_upper_of_query a b (ordinaryNewQuery a b)
    (value out) hmeanQuery hquery
  have hrho : b 0≤thirdPrefixRho := hmu.trans (by
    norm_num [VariableEnvelope.mu,thirdPrefixRho])
  have hleaf := ordinary_full_leaf_old_chord_upper a b ha hab hcut hyx hzy hrho hfull
    (planeConst k) (oldX s k) (oldY s k) (oldZ s k)
    (tentOldLow s k b) (tentOldHigh s k a) (value fl) (value fh) (value out)
    (by simpa only [hlowBind] using hlow) hspan
    (fun t ht => original_tent_old_range s k a b ha hresidual ht)
    (fun t ht => original_tent_old_minorant s k a b ha hyx hzy hmu hactive hupper ht)
    (by simpa only [hlowBind] using hfl) (by simpa only [hhighBind] using hfh) hout
  have hc : max 0 (value out-oldChordMean a b
      (planeConst k) (oldX s k) (oldY s k) (oldZ s k)
      (tentOldLow s k b) (tentOldHigh s k a) (value fl) (value fh))≤
        value (meanHigh (ordinaryTentWeight s k a b low high).lo
          (ordinaryTentWeight s k a b low high).hi fl fh out) := by
    simpa only [oldChordMean,oldAffineMean,tentOldMean] using hround
  exact hleaf.trans (mul_le_mul_of_nonneg_left hc
    (mul_nonneg (by norm_num) (boxMass_pos a b ha hab).le))

end
end ImbalancedChen.OriginalThirdSixTentRoundedConsumerSourceOnly
