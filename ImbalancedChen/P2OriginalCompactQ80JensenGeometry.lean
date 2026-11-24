import ImbalancedChen.P2OriginalCompactQ80JensenSelection
import ImbalancedChen.P2OriginalCompactQ80Symmetry
import ImbalancedChen.ActualThirdOriginalP4ASymmetricBLeaf
import ImbalancedChen.ActualThirdOriginalSymmetricClippedMean

/-! SOURCE ONLY / UNCOMPILED.
True moment ranges and cap minorants for the literal selected source plane.
The two probability laws are kept distinct. -/
namespace ImbalancedChen.P2OriginalCompactQ80JensenGeometrySourceOnly

noncomputable section
open Set MeasureTheory
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalCompactQ80SymmetrySourceOnly
open P2OriginalCompactQ80JensenMomentsSourceOnly
open P2OriginalCompactQ80JensenSelectionSourceOnly
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdCompactPartitionSourceOnly

def planeA (p : SourcePlane) : ℝ := (p.a : ℝ)/(p.e : ℝ)
def planeB (p : SourcePlane) : ℝ := ((p.b : ℝ)-(p.e : ℝ))/(p.e : ℝ)
def planeC (p : SourcePlane) : ℝ := ((p.c : ℝ)-(p.e : ℝ))/(p.e : ℝ)
def planeE (p : SourcePlane) : ℝ := ((p.d : ℝ)-(p.e : ℝ))/(p.e : ℝ)
def planeOld (p : SourcePlane) : BoxPoint → ℝ :=
  affineArgument (planeA p) (planeB p) (planeC p) (planeE p)

theorem raw_moments_eq_physical (box : RawBox) (g : Geometry box) :
    realXMean box=(denominator : ℝ)*boxEX (decodeCoordinates box.1) (decodeCoordinates box.2) ∧
    realYMean box=(denominator : ℝ)*boxEY (decodeCoordinates box.1) (decodeCoordinates box.2) ∧
    realInvZMean box=boxEZInv (decodeCoordinates box.1) (decodeCoordinates box.2)/(denominator : ℝ) ∧
    realMaxMean box=(denominator : ℝ)*OriginalThirdTriangleMomentsSourceOnly.maxMean
      (decodeCoordinates box.1 0) (decodeCoordinates box.2 0) := by
  have hD : (denominator : ℝ)≠0 := by norm_num [denominator]
  have hz0 : (box.1 2 : ℝ)≠0 := by exact_mod_cast (g.raw_positive 2).ne'
  have hz1 : (box.2 2 : ℝ)≠0 := by exact_mod_cast ((g.raw_positive 2).trans (g.width 2)).ne'
  have hratio (i : Fin 3) : (box.2 i : ℝ)/denominator/((box.1 i : ℝ)/denominator)=
      (box.2 i : ℝ)/(box.1 i : ℝ) := div_div_div_cancel_right₀ hD _ _
  have hlog (i : Fin 3) : Real.log ((box.2 i : ℝ)/(box.1 i : ℝ))≠0 :=
    (Real.log_pos ((one_lt_div (by exact_mod_cast g.raw_positive i)).2
      (by exact_mod_cast g.width i))).ne'
  refine ⟨?_,?_,?_,?_⟩
  · simp only [realXMean,boxEX,decode_binding,hratio]
    field_simp [hD,hlog 0]
    ring
  · simp only [realYMean,boxEY,decode_binding,hratio]
    field_simp [hD,hlog 1]
    ring
  · simp only [realInvZMean,boxEZInv,decode_binding]
    field_simp [hD,hz0,hz1]
    ring
  · simp only [realMaxMean,OriginalThirdTriangleMomentsSourceOnly.maxMean,
      decode_binding,hratio]
    field_simp [hD,hlog 0]
    ring

theorem ordinary_old_mean_eq (box : RawBox) (g : Geometry box) (p : SourcePlane)
    (hp : 0 < p.e) (hs : ¬aboveSymmetric box) :
    realOldMean box p=oldAffineMean (decodeCoordinates box.1) (decodeCoordinates box.2)
      (planeA p) (planeB p) (planeC p) (planeE p) := by
  obtain ⟨hx,hy,hz,hm⟩ := raw_moments_eq_physical box g
  simp only [realOldMean,if_neg hs,hx,hy,hz,oldAffineMean,planeA,planeB,planeC,planeE]
  field_simp [show (p.e : ℝ)≠0 by exact_mod_cast hp.ne',
    show (denominator : ℝ)≠0 by norm_num [denominator]]
  ring

theorem planeOld_endpoint (v : Fin 3 → ℤ) (p : SourcePlane)
    (hp : 0 < p.e) (hz : 0 < v 2) :
    (((p.a*denominator+(p.b-p.e)*v 0+(p.c-p.e)*v 1+(p.d-p.e)*v 2 : ℤ) : ℚ)/
      ((p.e*v 2 : ℤ) : ℚ) : ℝ)=planeOld p (decodeCoordinates v) := by
  simp only [Rat.cast_div,Rat.cast_intCast,planeOld,affineArgument,planeA,planeB,
    planeC,planeE,decode_binding]
  push_cast
  field_simp [show (p.e : ℝ)≠0 by exact_mod_cast hp.ne',
    show (v 2 : ℝ)≠0 by exact_mod_cast hz.ne',
    show (denominator : ℝ)≠0 by norm_num [denominator]]
  ring

theorem planeOld_endpoints (box : RawBox) (g : Geometry box) (p : SourcePlane)
    (hp : 0 < p.e) :
    (oldLow box p : ℝ)=planeOld p (decodeCoordinates box.2) ∧
    (oldHigh box p : ℝ)=planeOld p (decodeCoordinates box.1) :=
  ⟨planeOld_endpoint box.2 p hp ((g.raw_positive 2).trans (g.width 2)),
    planeOld_endpoint box.1 p hp (g.raw_positive 2)⟩

theorem planeOld_range (box : RawBox) (g : Geometry box) (p : SourcePlane)
    (hp : 0 < p.e) (he : jensenEligible box p)
    {t : BoxPoint} (ht : t∈Icc (decodeCoordinates box.1) (decodeCoordinates box.2)) :
    planeOld p t∈Icc (oldLow box p : ℝ) (oldHigh box p : ℝ) := by
  have heR : (0 : ℝ)<p.e := by exact_mod_cast hp
  have hB : planeB p≤0 := div_nonpos_of_nonpos_of_nonneg
    (by exact_mod_cast sub_nonpos.mpr he.1) heR.le
  have hC : planeC p≤0 := div_nonpos_of_nonpos_of_nonneg
    (by exact_mod_cast sub_nonpos.mpr he.2.1) heR.le
  let n (u : BoxPoint) : ℝ := planeA p+planeB p*u 0+planeC p*u 1
  have hres : 0 < n (decodeCoordinates box.2) := by
    have hn : (0 : ℝ)<((p.a*denominator+(p.b-p.e)*box.2 0+
      (p.c-p.e)*box.2 1 : ℤ) : ℝ) := by exact_mod_cast he.2.2.1
    have hD : (0 : ℝ)<denominator := by norm_num [denominator]
    have hh := div_pos hn (mul_pos heR hD)
    convert hh using 1
    dsimp [n,planeA,planeB,planeC]
    simp only [decode_binding]
    push_cast
    field_simp [heR.ne',hD.ne']
    ring
  have hl : n (decodeCoordinates box.2)≤n t := by
    dsimp [n]
    linarith only [mul_le_mul_of_nonpos_left (ht.2 0) hB,
      mul_le_mul_of_nonpos_left (ht.2 1) hC]
  have hh : n t≤n (decodeCoordinates box.1) := by
    dsimp [n]
    linarith only [mul_le_mul_of_nonpos_left (ht.1 0) hB,
      mul_le_mul_of_nonpos_left (ht.1 1) hC]
  have hz : 0<t 2 := (g.positive 2).trans_le (ht.1 2)
  have hl' := div_le_div₀ (hres.le.trans hl) hl hz (ht.2 2)
  have hh' := div_le_div₀ ((hres.le.trans hl).trans hh) hh (g.positive 2) (ht.1 2)
  obtain ⟨hlo,hhi⟩ := planeOld_endpoints box g p hp
  rw [hlo,hhi]
  exact ⟨add_le_add_right hl' (planeE p),add_le_add_right hh' (planeE p)⟩

theorem ordinary_old_mean_mem_range (box : RawBox) (g : Geometry box) (p : SourcePlane)
    (hp : 0 < p.e) (he : jensenEligible box p) (hs : ¬aboveSymmetric box) :
    realOldMean box p∈Icc (oldLow box p : ℝ) (oldHigh box p : ℝ) := by
  letI := boxProbability_isProbability _ _ g.positive g.real_width
  have hr : ∀ᵐ t∂boxProbability (decodeCoordinates box.1) (decodeCoordinates box.2),
      planeOld p t∈Icc (oldLow box p : ℝ) (oldHigh box p : ℝ) :=
    (boxProbability_ae_mem _ _).mono (fun t ht => planeOld_range box g p hp he ht)
  have hm : Measurable (planeOld p) := by unfold planeOld affineArgument; fun_prop
  have hint : Integrable (planeOld p)
      (boxProbability (decodeCoordinates box.1) (decodeCoordinates box.2)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable
      (|(oldLow box p : ℝ)|+|(oldHigh box p : ℝ)|)
    filter_upwards [hr] with t ht
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith only [neg_abs_le (oldLow box p : ℝ),
      abs_nonneg (oldHigh box p : ℝ),ht.1],
      by linarith only [le_abs_self (oldHigh box p : ℝ),abs_nonneg (oldLow box p : ℝ),ht.2]⟩
  have hlo := integral_mono_ae (integrable_const (oldLow box p : ℝ)) hint
    (hr.mono (fun _ h => h.1))
  have hhi := integral_mono_ae hint (integrable_const (oldHigh box p : ℝ))
    (hr.mono (fun _ h => h.2))
  have hmean : (∫ t,planeOld p t∂boxProbability
      (decodeCoordinates box.1) (decodeCoordinates box.2))=realOldMean box p := by
    rw [ordinary_old_mean_eq box g p hp hs]
    exact boxProbability_affine_mean _ _ g.positive g.real_width _ _ _ _
  rw [hmean] at hlo hhi
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hlo hhi
  exact ⟨hlo,hhi⟩

theorem planeOld_tent (s : TentSum) (k : TentSide) : planeOld (tentRow s k)=tentOldArgument s k := by
  funext t
  cases k <;> simp only [planeOld,tentOldArgument,affineArgument,planeA,planeB,planeC,planeE,
    tentRow,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,literalTentX_cast,literalTentY_cast,
    literalTentZ_cast,planeConst,planeSlope,oldX,oldY,oldZ] <;> ring

theorem planeOld_base : planeOld baseRow=bOldArgument := by
  funext t
  simp only [planeOld,bOldArgument,affineArgument,planeA,planeB,planeC,planeE,baseRow,
    Int.cast_ofNat,Int.cast_zero,Int.cast_neg]
  ring

theorem ordinary_tent_mean_eq (box : RawBox) (g : Geometry box) (s : TentSum) (k : TentSide)
    (hs : ¬aboveSymmetric box) :
    realOldMean box (tentRow s k)=tentOldMean s k
      (decodeCoordinates box.1) (decodeCoordinates box.2) := by
  rw [ordinary_old_mean_eq box g (tentRow s k)
    (by cases k <;> norm_num [tentRow]) hs]
  cases k <;> simp only [oldAffineMean,tentOldMean,planeA,planeB,planeC,planeE,
    tentRow,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,literalTentX_cast,literalTentY_cast,
    literalTentZ_cast,planeConst,planeSlope,oldX,oldY,oldZ] <;> ring

theorem ordinary_base_mean_eq (box : RawBox) (g : Geometry box) (hs : ¬aboveSymmetric box) :
    realOldMean box baseRow=bOldMean (decodeCoordinates box.1) (decodeCoordinates box.2) := by
  rw [ordinary_old_mean_eq box g baseRow (by norm_num [baseRow]) hs]
  simp only [oldAffineMean,bOldMean,planeA,planeB,planeC,planeE,baseRow,
    Int.cast_ofNat,Int.cast_zero,Int.cast_neg]
  ring

theorem base_endpoints (box : RawBox) (g : Geometry box) :
    (oldLow box baseRow : ℝ)=bOldLow (decodeCoordinates box.2) ∧
    (oldHigh box baseRow : ℝ)=bOldHigh (decodeCoordinates box.1) := by
  simpa only [planeOld_base,bOldLow,bOldHigh] using
    planeOld_endpoints box g baseRow (by norm_num [baseRow])

theorem below_mu_of_not_above (box : RawBox) (g : Geometry box)
    (hm : ¬muInteger≤box.1 0) : decodeCoordinates box.2 0≤VariableEnvelope.mu := by
  have hh := g.muCut.resolve_right hm
  have hd := decode_le_decode (w := fun _ => muInteger) (j := (0 : Fin 3)) hh
  simpa [decode_binding,muInteger,denominator,VariableEnvelope.mu] using hd

theorem above_mu_real (box : RawBox) (hm : muInteger≤box.1 0) :
    VariableEnvelope.mu≤decodeCoordinates box.1 0 := by
  have hd := decode_le_decode (v := fun _ => muInteger) (i := (0 : Fin 3)) hm
  simpa [decode_binding,muInteger,denominator,VariableEnvelope.mu] using hd

/-- For an ordinary full cell, the actual selected old argument is a
minorant of the genuine cap/history kernel. -/
theorem selected_old_minorant_ordinary (box : RawBox) (g : Geometry box)
    (hi : inside box) (hs : ¬symmetricHalf box) (p : SourcePlane)
    (hp : affineCapLower box=some p) (he : jensenEligible box p)
    {t : BoxPoint} (ht : t∈Icc (decodeCoordinates box.1) (decodeCoordinates box.2)) :
    planeOld p t≤actualOldArgument t := by
  have hyx := decode_le_decode (hi.1.resolve_right hs)
  have hzy := decode_le_decode hi.2.1
  rcases affineCapLower_selected_cases box p hp with ⟨hm,rfl⟩ | ⟨hm,hrow,hroot⟩
  · have hmu := (above_mu_real box hm).trans (ht.1 0)
    have hv := v_le_actualExtendedThirdEnvelope (t 0) (t 1) (t 2)
    rw [VariableEnvelope.v_eq_C hmu] at hv
    have htheta : VariableEnvelope.C (t 0)≤thirdPrefixTheta := by
      dsimp [VariableEnvelope.C,VariableEnvelope.mu,thirdPrefixTheta] at hmu ⊢
      linarith only [hmu]
    have hcap : VariableEnvelope.C (t 0)≤actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) := by
      simpa only [actualExtendedThirdBufferedCap,thirdPrefixBufferedCap,mul_zero,sub_zero]
        using le_min htheta hv
    have hz := (g.positive 2).trans_le (ht.1 2)
    rw [planeOld_tent,tent_old_argument_identity .x .fall t hz.ne']
    unfold actualOldArgument
    apply div_le_div_of_nonneg_right _ hz.le
    have heq : tentPlane .x .fall t=VariableEnvelope.C (t 0) := by
      simp [tentPlane,planeConst,planeSlope,tentSum,sumX,sumY,sumZ,VariableEnvelope.C]
      <;> ring
    rw [heq]
    linarith only [hcap]
  · have hmu := below_mu_of_not_above box g hm
    rcases hrow with rfl | ⟨s,k,rfl,hbranch⟩
    · rw [planeOld_base]
      exact below_mu_B_old_minorant _ _ g.positive hyx hzy hmu ht
    · obtain ⟨ha,hr,hres⟩ := source_tent_geometry box s k hbranch hroot he
      rw [planeOld_tent]
      exact original_tent_old_minorant s k _ _ g.positive hyx hzy hmu ha hr ht

theorem source_symmetric_endpoint_functions (box : RawBox) (hs : symmetricHalf box) :
    decodeCoordinates box.1=OriginalThirdP4ASymmetricTentPrerequisites.symmetricLeft
      (decodeCoordinates box.1 0) (decodeCoordinates box.1 2) ∧
    decodeCoordinates box.2=OriginalThirdP4ASymmetricTentPrerequisites.symmetricRight
      (decodeCoordinates box.2 0) (decodeCoordinates box.2 2) := by
  obtain ⟨hl,hu⟩ := source_symmetric_coordinates box hs
  constructor <;> funext i <;> fin_cases i <;>
    simp [OriginalThirdP4ASymmetricTentPrerequisites.symmetricLeft,
      OriginalThirdP4ASymmetricTentPrerequisites.symmetricRight,←hl,←hu]

theorem source_symmetric_new_mean (box : RawBox) (g : Geometry box) (hs : symmetricHalf box) :
    realNewMean box=OriginalThirdSymmetricJensenSourceOnly.newMean
      (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
      (decodeCoordinates box.1 2) (decodeCoordinates box.2 2) := by
  rw [realNewMean_eq_physical box g]
  obtain ⟨hl,hu⟩ := source_symmetric_coordinates box hs
  simp only [boxEX,boxEY,boxEZInv,←hl,←hu,OriginalThirdSymmetricJensenSourceOnly.newMean,
    OriginalThirdSymmetricJensenSourceOnly.sumMean,OriginalThirdSymmetricJensenSourceOnly.invZMean]
  ring

theorem above_symmetric_selected (box : RawBox) (p : SourcePlane)
    (hp : affineCapLower box=some p) (hs : aboveSymmetric box) : p=tentRow .x .fall := by
  have hp' : some (tentRow .x .fall)=some p := by
    simpa only [affineCapLower,if_pos hs.1,tentRow,literalTentX,literalTentY,literalTentZ,
      mul_one,mul_zero] using hp
  exact (Option.some.inj hp').symm

theorem above_symmetric_mean_endpoints (box : RawBox) (g : Geometry box) (p : SourcePlane)
    (hp : affineCapLower box=some p) (hs : aboveSymmetric box) :
    realOldMean box p=OriginalThirdSymmetricJensenSourceOnly.oldMean
      (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
      (decodeCoordinates box.1 2) (decodeCoordinates box.2 2) ∧
    (oldLow box p : ℝ)=OriginalThirdSymmetricJensenSourceOnly.oldLow
      (decodeCoordinates box.2 0) (decodeCoordinates box.2 2) ∧
    (oldHigh box p : ℝ)=OriginalThirdSymmetricJensenSourceOnly.oldHigh
      (decodeCoordinates box.1 0) (decodeCoordinates box.1 2) := by
  have hrow := above_symmetric_selected box p hp hs
  obtain ⟨hl,hu⟩ := source_symmetric_coordinates box hs.2
  obtain ⟨hx,hy,hz,hm⟩ := raw_moments_eq_physical box g
  refine ⟨?_,?_,?_⟩
  · have hsum : boxEX (decodeCoordinates box.1) (decodeCoordinates box.2)+
        boxEY (decodeCoordinates box.1) (decodeCoordinates box.2)=
        OriginalThirdSymmetricJensenSourceOnly.sumMean
          (decodeCoordinates box.1 0) (decodeCoordinates box.2 0) := by
      simp only [boxEX,boxEY,←hl,←hu,OriginalThirdSymmetricJensenSourceOnly.sumMean]
      ring
    simp only [realOldMean,if_pos hs,hx,hy,hz,hm]
    calc
      _ = (57/64-boxEX (decodeCoordinates box.1) (decodeCoordinates box.2)-
          boxEY (decodeCoordinates box.1) (decodeCoordinates box.2)-
          (3/2)*OriginalThirdTriangleMomentsSourceOnly.maxMean
            (decodeCoordinates box.1 0) (decodeCoordinates box.2 0))*
          boxEZInv (decodeCoordinates box.1) (decodeCoordinates box.2)-1 := by
        field_simp [show (denominator : ℝ)≠0 by norm_num [denominator]]
        ring
      _ = _ := by
        simp only [OriginalThirdSymmetricJensenSourceOnly.oldMean,
          ←hsum,OriginalThirdSymmetricJensenSourceOnly.invZMean,boxEZInv]
        ring
  · rw [hrow,(source_tent_endpoints box g .x .fall).1]
    simp only [tentOldLow,tentOldArgument,affineArgument,planeConst,planeSlope,oldX,oldY,oldZ,
      sumX,sumY,sumZ,←hu,OriginalThirdSymmetricJensenSourceOnly.oldLow]
    ring
  · rw [hrow,(source_tent_endpoints box g .x .fall).2]
    simp only [tentOldHigh,tentOldArgument,affineArgument,planeConst,planeSlope,oldX,oldY,oldZ,
      sumX,sumY,sumZ,←hl,OriginalThirdSymmetricJensenSourceOnly.oldHigh]
    ring

theorem source_old_mean_mem_range (box : RawBox) (g : Geometry box) (hi : inside box)
    (p : SourcePlane) (hp : affineCapLower box=some p) (he : jensenEligible box p) :
    realOldMean box p∈Icc (oldLow box p : ℝ) (oldHigh box p : ℝ) := by
  by_cases hs : aboveSymmetric box
  · obtain ⟨hm,hl,hh⟩ := above_symmetric_mean_endpoints box g p hp hs
    rw [hm,hl,hh]
    exact OriginalThirdSymmetricClippedMeanSourceOnly.actual_oldMean_mem_range
      (source_symmetricFullBox box g hi hs.2) (above_mu_real box hs.1)
  · exact ordinary_old_mean_mem_range box g p (selected_coefficients box p hp).1 he hs

end
end ImbalancedChen.P2OriginalCompactQ80JensenGeometrySourceOnly
