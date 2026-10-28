import ImbalancedChen.P2N48AllHighBandWeightedMass
import ImbalancedChen.P2IndependentMercator320

/-! SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
All actual retained n48 row weighted moments feed the SAME Q80 payload
ports. The independently frozen scalar Mercator soundness is reused for
the actual rational bin ratios. Signed moment additions/subtractions use
the existing four-corner enclosure algebra, not positive-only products.

No row payload, decimal/Q80 enclosure, Bernstein cover, comparison or
stored sum is evaluated. The finite payload-containment and original
row/omega checks remain concrete unexecuted obligations. This file does
not bound the still explicit whole-negative-domain uncoveredCost.
-/
namespace ImbalancedChen.P2N48AllPatternDirectedMassPorts
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48TiedParentMassReduction P2N48AllHighBandTiePatterns
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P2N48OriginalQ80DirectedRowSoundness P2N48OriginalStrictLogMassAndOmegaPorts
open P2N48TiedMomentPrimitives P2N48AllHighBandWeightedMass
open Certificates.P2DirectedLogRounding
open Certificates.SavedParent394700ActualBuchstabSourceOnly (OmegaCoverCertificate)

/-- Every original n48 bin ratio is in the proved direct Mercator window.
This is arithmetic on the symbolic source indices, not a row-data replay. -/
theorem row_log_argument_range (r : SourceRow) (j : Fin 4) :
    1≤logArgument r j ∧ logArgument r j≤3/2 := by
  have hleft : 0<leftEnd r j := by
    unfold leftEnd
    split_ifs <;> simp only [lowLo,highLo] <;> omega
  have hwidth : 2*width r j≤leftEnd r j := by
    unfold width leftEnd
    split_ifs <;> simp only [lowLo,highLo] <;> omega
  have hright : leftEnd r j≤rightEnd r j := by unfold rightEnd; omega
  have hthree : 2*rightEnd r j≤3*leftEnd r j := by unfold rightEnd; omega
  have hL : (0 : ℚ)<(leftEnd r j : ℚ) := by exact_mod_cast hleft
  have heq : logArgument r j=(rightEnd r j : ℚ)/(leftEnd r j : ℚ) := by
    unfold logArgument upperQ lowerQ
    field_simp <;> ring
  rw [heq]
  constructor
  · apply (le_div_iff₀ hL).2
    simpa only [one_mul] using (show (leftEnd r j : ℚ)≤(rightEnd r j : ℚ) by exact_mod_cast hright)
  · apply (div_le_iff₀ hL).2
    have hh : 2*(rightEnd r j : ℚ)≤3*(leftEnd r j : ℚ) := by exact_mod_cast hthree
    linarith

def logEnclosure (r : SourceRow) (j : Fin 4) : Enclosure :=
  P2IndependentMercator320.mercator (logArgument r j)

theorem logEnclosure_contains (r : SourceRow) (j : Fin 4) :
    (logEnclosure r j).Contains (rowLog r j) := by
  have hr := row_log_argument_range r j
  have h := P2IndependentMercator320.mercator_contains hr.1 hr.2
  simpa only [logEnclosure,rowLog,logArgument,Rat.cast_div,lowerQ_cast,upperQ_cast] using h

/-- r=0,s=1: 1/a-(1+L)/b. The negative term reverses its endpoints. -/
def moment01Enclosure (a b : ℚ) (L : Enclosure) : Enclosure :=
  (Enclosure.point (1/a)).sub
    (((Enclosure.point 1).add L).mul (Enclosure.point (1/b)))

/-- r=1,s=0: (L-1)/a+1/b, including the signed L-1 factor. -/
def moment10Enclosure (a b : ℚ) (L : Enclosure) : Enclosure :=
  ((L.sub (Enclosure.point 1)).mul (Enclosure.point (1/a))).add (Enclosure.point (1/b))

/-- r=1,s=1: (L-2)/a+(L+2)/b. Neither bracket is assumed positive. -/
def moment11Enclosure (a b : ℚ) (L : Enclosure) : Enclosure :=
  ((L.sub (Enclosure.point 2)).mul (Enclosure.point (1/a))).add
    ((L.add (Enclosure.point 2)).mul (Enclosure.point (1/b)))

theorem moment01Enclosure_sound (a b : ℚ) {L : Enclosure}
    (hL : L.Contains (Real.log ((b : ℝ)/(a : ℝ)))) :
    (moment01Enclosure a b L).Contains (moment01 (a : ℝ) b) := by
  have h := Enclosure.sub_contains (Enclosure.point_contains (1/a))
    (Enclosure.mul_contains (Enclosure.add_contains (Enclosure.point_contains 1) hL)
      (Enclosure.point_contains (1/b)))
  convert h using 1 <;> simp only [moment01Enclosure,moment01,Rat.cast_div,Rat.cast_one] <;> ring

theorem moment10Enclosure_sound (a b : ℚ) {L : Enclosure}
    (hL : L.Contains (Real.log ((b : ℝ)/(a : ℝ)))) :
    (moment10Enclosure a b L).Contains (moment10 (a : ℝ) b) := by
  have h := Enclosure.add_contains
    (Enclosure.mul_contains (Enclosure.sub_contains hL (Enclosure.point_contains 1))
      (Enclosure.point_contains (1/a))) (Enclosure.point_contains (1/b))
  convert h using 1 <;>
    simp only [moment10Enclosure,moment10,Rat.cast_div,Rat.cast_one] <;> ring

theorem moment11Enclosure_sound (a b : ℚ) {L : Enclosure}
    (hL : L.Contains (Real.log ((b : ℝ)/(a : ℝ)))) :
    (moment11Enclosure a b L).Contains (moment11 (a : ℝ) b) := by
  have h := Enclosure.add_contains
    (Enclosure.mul_contains (Enclosure.sub_contains hL (Enclosure.point_contains 2))
      (Enclosure.point_contains (1/a)))
    (Enclosure.mul_contains (Enclosure.add_contains hL (Enclosure.point_contains 2))
      (Enclosure.point_contains (1/b)))
  convert h using 1 <;>
    simp only [moment11Enclosure,moment11,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] <;> ring

/-- All ORIGINAL tie patterns, using exactly the corresponding true moment. -/
def rawRowMassEnclosure (r : SourceRow) : Enclosure :=
  if r.iy=r.iz then
    if r.iz=r.iw then
      (logEnclosure r 0).mul (moment11Enclosure (lowerQ r 1) (upperQ r 1) (logEnclosure r 1))
    else ((logEnclosure r 0).mul
      (moment10Enclosure (lowerQ r 1) (upperQ r 1) (logEnclosure r 1))).mul (logEnclosure r 3)
  else if r.iz=r.iw then
    ((logEnclosure r 0).mul (logEnclosure r 1)).mul
      (moment01Enclosure (lowerQ r 2) (upperQ r 2) (logEnclosure r 2))
  else (((logEnclosure r 0).mul (logEnclosure r 1)).mul
    (Enclosure.point (1/lowerQ r 2-1/upperQ r 2))).mul (logEnclosure r 3)

def rowMassEnclosure (r : SourceRow) : Enclosure := (rawRowMassEnclosure r).round 80

theorem rawRowMassEnclosure_sound (r : SourceRow) :
    (rawRowMassEnclosure r).Contains (rowZFormula r) := by
  have h0 := logEnclosure_contains r 0
  have h1 := logEnclosure_contains r 1
  have h2 := logEnclosure_contains r 2
  have h3 := logEnclosure_contains r 3
  have hM01 := moment01Enclosure_sound (lowerQ r 2) (upperQ r 2)
    (by simpa only [rowLog,lowerQ_cast,upperQ_cast] using h2)
  have hM10 := moment10Enclosure_sound (lowerQ r 1) (upperQ r 1)
    (by simpa only [rowLog,lowerQ_cast,upperQ_cast] using h1)
  have hM11 := moment11Enclosure_sound (lowerQ r 1) (upperQ r 1)
    (by simpa only [rowLog,lowerQ_cast,upperQ_cast] using h1)
  by_cases h12 : r.iy=r.iz
  · by_cases h23 : r.iz=r.iw
    · simpa only [rawRowMassEnclosure,rowZFormula,if_pos h12,if_pos h23,
        lowerQ_cast,upperQ_cast] using Enclosure.mul_contains h0 hM11
    · simpa only [rawRowMassEnclosure,rowZFormula,if_pos h12,if_neg h23,
        lowerQ_cast,upperQ_cast] using Enclosure.mul_contains (Enclosure.mul_contains h0 hM10) h3
  · by_cases h23 : r.iz=r.iw
    · simpa only [rawRowMassEnclosure,rowZFormula,if_neg h12,if_pos h23,
        lowerQ_cast,upperQ_cast] using Enclosure.mul_contains (Enclosure.mul_contains h0 h1) hM01
    · have hpoint := Enclosure.point_contains (1/lowerQ r 2-1/upperQ r 2)
      have h := Enclosure.mul_contains
        (Enclosure.mul_contains (Enclosure.mul_contains h0 h1) hpoint) h3
      simpa only [rawRowMassEnclosure,rowZFormula,if_neg h12,if_neg h23,
        strictZ,rowLog,Rat.cast_sub,Rat.cast_div,Rat.cast_one,lowerQ_cast,upperQ_cast] using h

/-- ACTUAL full ordered-row Z, not a supplied mass enclosure. -/
theorem actual_retained_rowMassEnclosure_sound (r : SourceRow) (hr : r∈actualRetainedRows) :
    (rowMassEnclosure r).Contains (parentUnweightedMass (fullParent r)) := by
  rw [actual_retained_true_mass_formula r hr]
  exact Enclosure.round_contains (rawRowMassEnclosure_sound r) 80

/-- Finite rational containment into the same original directed payload.
This check is only written; no actual payload or row result is asserted. -/
def massPayloadCheck (r : SourceRow) (p : DirectedPayload) : Bool :=
  decide ((p.massLo : ℚ)/(q80 : ℚ)≤(rowMassEnclosure r).lower ∧
    (rowMassEnclosure r).upper≤(p.massHi : ℚ)/(q80 : ℚ))

theorem actual_all_pattern_mass_endpoints (r : SourceRow) (hr : r∈actualRetainedRows)
    (p : DirectedPayload) (hcheck : massPayloadCheck r p=true) :
    value p.massLo≤parentUnweightedMass (fullParent r) ∧
      parentUnweightedMass (fullParent r)≤value p.massHi := by
  have hrat : (p.massLo : ℚ)/(q80 : ℚ)≤(rowMassEnclosure r).lower ∧
      (rowMassEnclosure r).upper≤(p.massHi : ℚ)/(q80 : ℚ) := of_decide_eq_true hcheck
  have he := actual_retained_rowMassEnclosure_sound r hr
  have hlo : value p.massLo≤((rowMassEnclosure r).lower : ℝ) := by exact_mod_cast hrat.1
  have hhi : ((rowMassEnclosure r).upper : ℝ)≤value p.massHi := by exact_mod_cast hrat.2
  exact ⟨hlo.trans he.1,he.2.trans hhi⟩

/-- All tie patterns now supply the actual original directed ports. -/
theorem actual_all_rows_directed_ports (r : SourceRow) (hr : r∈actualRetainedRows)
    (p : DirectedPayload) (c : OmegaCoverCertificate)
    (hrow : rowPayloadCheck r p=true) (hMass : massPayloadCheck r p=true)
    (hOmega : omegaPayloadCheck r p c=true) :
    value (baselineLo p)≤anchorK*omegaCap*parentUnweightedMass (fullParent r) ∧
      anchorK*parentSwitchedMass (fullParent r)≤value (omegaCostHi p) := by
  have ht := (decoded_of_mem_rawSelectedRows r (actualRetainedRows_policy r hr).1).1
  have hZ := actual_all_pattern_mass_endpoints r hr p hMass
  obtain ⟨_,_,hLo,_,hOm,_⟩ := rowPayloadCheck_sound r p hrow
  exact ⟨directed_baseline_sound r p hLo hZ.1,
    directed_omega_cost_sound r p hOm hZ.2 (actual_omega_payload_bound r ht p c hOmega)⟩

/-- The same actual selected coefficient consumes all weighted row cases.
No hMass, hBaseline, hOmegaCost or real omega enclosure is a premise.
The full uncoveredCost and all genuine finite checks remain explicit. -/
theorem actual_selected_functional_upper_all_pattern_certificates
    (p : SourceRow→DirectedPayload) (cOmega cCap : SourceRow→OmegaCoverCertificate)
    (hrow : ∀ r∈actualRetainedRows,rowPayloadCheck r (p r)=true)
    (hMass : ∀ r∈actualRetainedRows,massPayloadCheck r (p r)=true)
    (hOmega : ∀ r∈actualRetainedRows,omegaPayloadCheck r (p r) (cOmega r)=true)
    (hCap : ∀ r∈actualRetainedRows,omegaCapCheck r (cCap r)=true) :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient≤
      (∑ r∈actualRetainedRows,savedParent r (parentUnweightedMass (fullParent r)))-
      (∑ r∈actualRetainedRows,rowGainLower r)+uncoveredCost actualRetainedRows := by
  apply actual_selected_functional_upper_of_original_Q80 p hrow
  · intro r hr
    exact actual_all_pattern_mass_endpoints r hr (p r) (hMass r hr)
  · intro r hr
    have ht := (decoded_of_mem_rawSelectedRows r (actualRetainedRows_policy r hr).1).1
    exact actual_omega_payload_bound r ht (p r) (cOmega r) (hOmega r hr)
  · intro r hr
    have ht := (decoded_of_mem_rawSelectedRows r (actualRetainedRows_policy r hr).1).1
    exact actual_omega_cap_bound r ht (cCap r) (hCap r hr)

end
end ImbalancedChen.P2N48AllPatternDirectedMassPorts
