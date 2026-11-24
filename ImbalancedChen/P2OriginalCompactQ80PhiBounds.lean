import ImbalancedChen.P2OriginalCompactQ80Leaf
import ImbalancedChen.VariableEnvelopeConsequences

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNCHECKED.

The literal original phi_range upper endpoint and both lowerDifference
candidates. All queries are the actual maximum-12 Q80 source queries.
The only cell assumptions are Geometry's original coordinate bounds,
strict widths and preserved mu cut. There is no cap, table, factor-gap,
leaf-integral or selected-charge premise. No finite guard is evaluated.

The true gated cap is retained, including its full branch at x=mu. The
source scalar branch agrees there because the full envelope equals cap.
Concavity is used only after the literal olo >= 2*z1 guard proves old>=2.
Integration and the symmetric half-domain rule belong to the companion
selection module; the true asymmetric cap is never called symmetric here.
-/
namespace ImbalancedChen.P2OriginalCompactQ80PhiBoundsSourceOnly

noncomputable section
open Set
open Certificates.P2HistoricQ80DefectLookup
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P2OriginalCompactBoundaryCapFloorSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdP4AOriginalClippedGapSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly

/-- Coordinate normalization, distinct from Q80 value normalization. -/
def rawValue (n : ℤ) : ℝ := (n : ℝ)/(denominator : ℝ)

theorem denominator_real_pos : (0 : ℝ) < (denominator : ℝ) := by
  norm_num [denominator]

theorem rawValue_mono {a b : ℤ} (h : a ≤ b) : rawValue a ≤ rawValue b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) denominator_real_pos.le

theorem rawValue_min (a b : ℤ) : rawValue (min a b) = min (rawValue a) (rawValue b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,min_eq_left (rawValue_mono h)]
  · rw [min_eq_right h,min_eq_right (rawValue_mono h)]

theorem rawValue_up (n d : ℤ) (hd : 0 < d) :
    rawValue n/(d : ℝ) ≤ rawValue (up n d) := by
  have h := div_le_div_of_nonneg_right
    (Certificates.P2HistoricLogPointInterpreter.real_le_ceilDiv n d hd)
    denominator_real_pos.le
  convert h using 1 <;> dsimp [rawValue,up,
    Certificates.P2HistoricLogPointInterpreter.ceilDiv] <;> ring

theorem rawValue_theta : rawValue thetaInteger = thirdPrefixTheta := by
  norm_num [rawValue,thetaInteger,denominator,thirdPrefixTheta]

theorem rawValue_mu : rawValue muInteger = VariableEnvelope.mu := by
  norm_num [rawValue,muInteger,denominator,VariableEnvelope.mu]

theorem decode_eq_rawValue (v : Fin 3 → ℤ) (i : Fin 3) :
    decodeCoordinates v i = rawValue (v i) := decode_binding v i

/-- Both original endpoint ceilings stay inside the minimum. -/
theorem vPointUpper_sound (n : ℤ) :
    VariableEnvelope.v (rawValue n) ≤ rawValue (vPointUpper n) := by
  rw [vPointUpper,rawValue_min,VariableEnvelope.v_eq_min]
  apply min_le_min
  · have h := rawValue_up (denominator+n) 2 (by norm_num)
    convert h using 1 <;> dsimp [VariableEnvelope.A,rawValue] <;>
      push_cast <;> field_simp [denominator_real_pos.ne'] <;> ring
  · have h := rawValue_up (57*denominator-96*n) 64 (by norm_num)
    convert h using 1 <;> dsimp [VariableEnvelope.C,rawValue] <;>
      push_cast <;> field_simp [denominator_real_pos.ne'] <;> ring

/-- The original peak test includes either endpoint equal to mu. -/
theorem vUpper_sound (lo hi : ℤ) {x : ℝ}
    (hl : rawValue lo ≤ x) (hh : x ≤ rawValue hi) :
    VariableEnvelope.v x ≤ rawValue (vUpper lo hi) := by
  by_cases hm : lo ≤ muInteger ∧ muInteger ≤ hi
  · rw [vUpper,if_pos hm]
    have hp := rawValue_up (153*denominator) 256 (by norm_num)
    have he : rawValue (153*denominator)/(256 : ℝ) = VariableEnvelope.cap := by
      dsimp [rawValue,VariableEnvelope.cap]
      push_cast
      field_simp [denominator_real_pos.ne']
    rw [he] at hp
    exact (VariableEnvelope.v_le_cap x).trans hp
  · rw [vUpper,if_neg hm]
    by_cases hu : hi ≤ muInteger
    · have hmu : rawValue hi ≤ VariableEnvelope.mu := by
        simpa only [rawValue_mu] using rawValue_mono hu
      have hv : VariableEnvelope.v x ≤ VariableEnvelope.v (rawValue hi) := by
        rw [VariableEnvelope.v_eq_A (hh.trans hmu),VariableEnvelope.v_eq_A hmu]
        dsimp [VariableEnvelope.A]
        linarith only [hh]
      exact (hv.trans (vPointUpper_sound hi)).trans
        (rawValue_mono (le_max_right _ _))
    · have hmu : VariableEnvelope.mu ≤ rawValue lo := by
        have hmlo : muInteger ≤ lo := by omega
        simpa only [rawValue_mu] using rawValue_mono hmlo
      have hv : VariableEnvelope.v x ≤ VariableEnvelope.v (rawValue lo) := by
        rw [VariableEnvelope.v_eq_C (hmu.trans hl),VariableEnvelope.v_eq_C hmu]
        dsimp [VariableEnvelope.C]
        linarith only [hl]
      exact (hv.trans (vPointUpper_sound lo)).trans
        (rawValue_mono (le_max_left _ _))

theorem sumRanges_eq_authorSums (box : RawBox) :
    sumRanges box = authorSums.map (fun s => (rawSum s box.1,rawSum s box.2)) := by
  simp [sumRanges,authorSums,rawSum,literalTentX,literalTentY,literalTentZ]

private theorem base_le_max_fold (xs : List ℤ) (a : ℤ) : a ≤ xs.foldr max a := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact ih.trans (le_max_right _ _)

private theorem mem_le_max_fold (xs : List ℤ) (a x : ℤ) (hx : x ∈ xs) :
    x ≤ xs.foldr max a := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with he | he
      · subst x
        exact le_max_left _ _
      · exact (ih he).trans (le_max_right _ _)

/-- The upper B operand uses z0 and one ceiling, exactly as the producer. -/
theorem B_upper_sound (lo : Fin 3 → ℤ) {t : Point}
    (ht : decodeCoordinates lo ≤ t) :
    VariableEnvelope.B (t 2) ≤ rawValue (up (153*denominator-96*lo 2) 256) := by
  have h := rawValue_up (153*denominator-96*lo 2) 256 (by norm_num)
  have he : rawValue (153*denominator-96*lo 2)/(256 : ℝ) =
      VariableEnvelope.B (decodeCoordinates lo 2) := by
    rw [decode_eq_rawValue]
    dsimp [rawValue,VariableEnvelope.B,VariableEnvelope.cap]
    push_cast
    field_simp [denominator_real_pos.ne'] <;> ring
  rw [he] at h
  exact (show VariableEnvelope.B (t 2) ≤ VariableEnvelope.B (decodeCoordinates lo 2) from by
    dsimp [VariableEnvelope.B]
    linarith only [ht 2]).trans h

def belowUpper (box : RawBox) : ℤ :=
  ((sumRanges box).map (fun p => vUpper p.1 p.2)).foldr max
    (up (153*denominator-96*box.1 2) 256)

theorem six_le_belowUpper (box : RawBox) {t : Point}
    (ht : t ∈ Icc (decodeCoordinates box.1) (decodeCoordinates box.2)) :
    VariableEnvelope.six (t 0) (t 1) (t 2) ≤ rawValue (belowUpper box) := by
  have hs (s : TentSum) : VariableEnvelope.v (tentSum s t) ≤ rawValue (belowUpper box) := by
    have hb (v : Fin 3 → ℤ) : rawValue (rawSum s v) = tentSum s (decodeCoordinates v) :=
      rawSum_real_binding v (decodeCoordinates v) (decode_binding v) s
    have hv := vUpper_sound (rawSum s box.1) (rawSum s box.2)
      (by rw [hb]; exact tentSum_mono s ht.1)
      (by rw [hb]; exact tentSum_mono s ht.2)
    apply hv.trans
    apply rawValue_mono
    apply mem_le_max_fold
    rw [sumRanges_eq_authorSums,List.map_map]
    apply List.mem_map.mpr
    refine ⟨s,?_,rfl⟩
    cases s <;> simp [authorSums]
  have hB : VariableEnvelope.B (t 2) ≤ rawValue (belowUpper box) :=
    (B_upper_sound box.1 ht.1).trans (rawValue_mono (base_le_max_fold _ _))
  have hx := hs .x
  have hxy := hs .xy
  have hxyz := hs .xyz
  have hxz := hs .xz
  have hyz := hs .yz
  simp only [tentSum,sumX,sumY,sumZ,one_mul,zero_mul,zero_add,add_zero] at hx hxy hxyz hxz hyz
  exact max_le hx (max_le hxy (max_le hxyz (max_le hB (max_le hxz hyz))))

/-- Above mu, the actual dispatch agrees with v even at the closed wall.
At equality this uses the proved full-envelope value, not an if rewrite
that incorrectly assigns equality to the analytic fallback branch. -/
theorem actualEnvelope_eq_v_of_mu_le {x y z : ℝ}
    (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) (hm : VariableEnvelope.mu ≤ x) :
    actualExtendedThirdEnvelope x y z = VariableEnvelope.v x := by
  by_cases hx : x ≤ VariableEnvelope.mu
  · have he : x = VariableEnvelope.mu := le_antisymm hx hm
    subst x
    rw [actualExtendedThirdEnvelope,if_pos le_rfl,
      VariableEnvelope.original_mu_left ⟨hz,hzy,hyx,le_rfl⟩,
      VariableEnvelope.v_eq_A le_rfl]
    norm_num [VariableEnvelope.cap,VariableEnvelope.A,VariableEnvelope.mu]
  · rw [actualExtendedThirdEnvelope,if_neg hx]

theorem phiRange_upper_le_theta (box : RawBox) : (phiRange box).hi ≤ thetaInteger := by
  unfold phiRange
  split <;> exact min_le_left _ _

/-- Exact original phi upper bound on the actual ordered intersection,
including boundary boxes and x0=mu. No desired phi bound is an input. -/
theorem cap_ceiling_on_actual_intersection (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) ≤
      rawValue (phiRange box).hi := by
  have hz : 0 ≤ t 2 := ht.1.1.1.1.le
  have hzy : t 2 ≤ t 1 := ht.1.1.1.2.2.1
  have hyx : t 1 ≤ t 0 := ht.1.1.1.2.2.2.1
  by_cases hm : muInteger ≤ box.1 0
  · have hmu : VariableEnvelope.mu ≤ t 0 := by
      have h := (rawValue_mono hm).trans (by simpa only [decode_eq_rawValue] using ht.2.1 0)
      simpa only [rawValue_mu] using h
    have hv := vUpper_sound (box.1 0) (box.2 0)
      (by simpa only [decode_eq_rawValue] using ht.2.1 0)
      (by simpa only [decode_eq_rawValue] using ht.2.2 0)
    simp only [phiRange,if_pos hm,rawValue_min,rawValue_theta,
      actualExtendedThirdBufferedCap,thirdPrefixBufferedCap,mul_zero,sub_zero]
    rw [actualEnvelope_eq_v_of_mu_le hz hzy hyx hmu]
    exact min_le_min le_rfl hv
  · have hhi : box.2 0 ≤ muInteger := g.muCut.resolve_right hm
    have hmu : t 0 ≤ VariableEnvelope.mu := by
      have h := (show t 0 ≤ rawValue (box.2 0) from by
        simpa only [decode_eq_rawValue] using ht.2.2 0).trans (rawValue_mono hhi)
      simpa only [rawValue_mu] using h
    have hv := six_le_belowUpper box ht.2
    simp only [phiRange,if_neg hm]
    change _ ≤ rawValue (min thetaInteger (belowUpper box))
    rw [rawValue_min,rawValue_theta]
    simp only [actualExtendedThirdBufferedCap,thirdPrefixBufferedCap,mul_zero,sub_zero]
    rw [actualExtendedThirdEnvelope_eq_six ⟨hz,hzy,hyx,hmu⟩]
    exact min_le_min le_rfl hv

/-- Both original endpoints enclose the literal cap, in coordinate units. -/
theorem phiRange_contains_actual_cap (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    rawValue (phiRange box).lo ≤ actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) ∧
      actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) ≤ rawValue (phiRange box).hi :=
  ⟨cap_floor_on_actual_intersection box g ht,cap_ceiling_on_actual_intersection box g ht⟩

end
end ImbalancedChen.P2OriginalCompactQ80PhiBoundsSourceOnly
