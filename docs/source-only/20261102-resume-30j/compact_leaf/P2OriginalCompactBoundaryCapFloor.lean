import ImbalancedChen.ActualThirdOriginalP4AOrdinaryRawFallbackAllOld
import ImbalancedChen.ActualThirdOriginalP4AOriginalClippedGapLeaf

/-!
SOURCEONLY / UNCOMPILED / ORIGINAL P2.4 OPEN.

The old cap-floor supplier required an OrdinaryGrid: an entirely ordered,
entirely inside, below-mu rectangle. Actual adaptive boundary rectangles do
not satisfy those hypotheses. Here the order is obtained from the ORIGINAL
compact-domain intersection, including its closed faces. Both source sides
of mu are treated, and the original v_lo floor is identified exactly with
the endpoint-minimum form used by the later independent producer.

No per-leaf integral, cap minorant, query enclosure or final endpoint is a
premise. The final analytic theorem consumes the existing proved clipped
gap integral. Its CheckedBlockTable input is the precise later P112/P160
reader, not the original P80 table; the next module fixes that reader.
-/

namespace ImbalancedChen.P2OriginalCompactBoundaryCapFloorSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
open OriginalThirdP4AOrdinaryRawFallbackAllOldSourceOnly
open OriginalThirdP4AOriginalClippedGapSourceOnly
open OriginalThirdClippedChordSourceOnly
open OriginalU2StoredNodeBlockCheckerSourceOnly OriginalU2StoredQueryLookupSourceOnly

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)
local notation "M₀" => (157286400000:ℤ)

/-- Literal certify_extended_prefix.py::v_lo, with two floor divisions. -/
def sourceVLower (l u : ℤ) : ℤ :=
  min ((D₀+l)/2) ((57*D₀-96*u)/64)

/-- The source and independent cap-floor formulas agree exactly; floors
remain inside the minimum and no approximate real comparison is used. -/
theorem sourceVLower_eq_endpoint_min (l u : ℤ) (hlu : l≤u) :
    sourceVLower l u=min (rawTentLower l) (rawTentLower u) := by
  have hA : (D₀+l)/2≤(D₀+u)/2 :=
    Int.ediv_le_ediv (by norm_num) (by omega)
  have hC : (57*D₀-96*u)/64≤(57*D₀-96*l)/64 :=
    Int.ediv_le_ediv (by norm_num) (by omega)
  unfold sourceVLower rawTentLower
  apply le_antisymm
  · exact le_min
      (le_min (min_le_left _ _) ((min_le_right _ _).trans hC))
      (le_min ((min_le_left _ _).trans hA) (min_le_right _ _))
  · exact le_min ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _))

theorem rawSum_mono (s : TentSum) {lo hi : Fin 3 → ℤ} (h : lo≤hi) :
    rawSum s lo≤rawSum s hi := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  cases s <;>
    simp only [rawSum,literalTentX,literalTentY,literalTentZ,
      one_mul,zero_mul,zero_add,add_zero] <;> omega

/-- The author's original branch order, including xyz before xz and yz. -/
def authorSums : List TentSum := [.x,.y,.xy,.xyz,.xz,.yz]

def authorBelowCapLower (lo hi : Fin 3 → ℤ) : ℤ :=
  min T₀ ((authorSums.map (fun s => sourceVLower (rawSum s lo) (rawSum s hi))).foldr
    max ((153*D₀-96*hi 2)/256))

/-- Exact original floor formula, not an equality of display values or hashes.
The reordered finite maximum is harmless; charge and leaf order are untouched. -/
theorem authorBelowCapLower_eq_source (lo hi : Fin 3 → ℤ) (h : lo≤hi) :
    authorBelowCapLower lo hi=sourceCapLower lo hi := by
  have he (s : TentSum) := sourceVLower_eq_endpoint_min
    (rawSum s lo) (rawSum s hi) (rawSum_mono s h)
  simp only [authorBelowCapLower,authorSums,sourceCapLower,sourceSums,
    List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,he]
  ac_rfl

private theorem scale_pos : (0:ℝ)<(D₀:ℝ) := by norm_num

theorem rawSum_real_binding (v : Fin 3 → ℤ) (p : BoxPoint)
    (hp : ∀ i, p i=(v i:ℝ)/(D₀:ℝ)) (s : TentSum) :
    (rawSum s v:ℝ)/(D₀:ℝ)=tentSum s p := by
  unfold rawSum tentSum
  rw [hp 0,hp 1,hp 2,←literalTentX_cast s,
    ←literalTentY_cast s,←literalTentZ_cast s]
  push_cast
  ring

/-- No full-box ordering or raw-cube condition is needed for an endpoint
floor to bound its own tent operand. -/
theorem boundary_tent_floor (lo hi : Fin 3 → ℤ) (a b : BoxPoint)
    (ha : ∀ i, a i=(lo i:ℝ)/(D₀:ℝ))
    (hb : ∀ i, b i=(hi i:ℝ)/(D₀:ℝ)) (s : TentSum)
    {t : BoxPoint} (ht : t∈Icc a b) :
    ((min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi)):ℤ):ℝ)/(D₀:ℝ)≤
      VariableEnvelope.v (tentSum s t) := by
  let q : ℤ := min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi))
  have hlow : (q:ℝ)/(D₀:ℝ)≤VariableEnvelope.v (tentSum s a) := by
    have hm : (q:ℝ)≤(rawTentLower (rawSum s lo):ℝ) := by
      exact_mod_cast (min_le_left (rawTentLower (rawSum s lo))
        (rawTentLower (rawSum s hi)))
    have hh := (div_le_div_of_nonneg_right hm scale_pos.le).trans
      (raw_tent_floor_le_v (rawSum s lo))
    rwa [rawSum_real_binding lo a ha s] at hh
  have hupp : (q:ℝ)/(D₀:ℝ)≤VariableEnvelope.v (tentSum s b) := by
    have hm : (q:ℝ)≤(rawTentLower (rawSum s hi):ℝ) := by
      exact_mod_cast (min_le_right (rawTentLower (rawSum s lo))
        (rawTentLower (rawSum s hi)))
    have hh := (div_le_div_of_nonneg_right hm scale_pos.le).trans
      (raw_tent_floor_le_v (rawSum s hi))
    rwa [rawSum_real_binding hi b hb s] at hh
  exact (le_min hlow hupp).trans
    (v_endpoint_min_le (tentSum_mono s ht.1) (tentSum_mono s ht.2))

theorem boundary_B_floor (hi : Fin 3 → ℤ) (b : BoxPoint)
    (hb : ∀ i, b i=(hi i:ℝ)/(D₀:ℝ))
    {t : BoxPoint} (ht : t≤b) :
    ((((153*D₀-96*hi 2)/256:ℤ):ℝ)/(D₀:ℝ))≤VariableEnvelope.B (t 2) := by
  have hh := div_le_div_of_nonneg_right
    (integer_floor_div_cast_le (153*D₀-96*hi 2) 256 (by norm_num)) scale_pos.le
  have he : (((153*D₀-96*hi 2:ℤ):ℝ)/(256:ℝ))/(D₀:ℝ)=
      VariableEnvelope.B (b 2) := by
    rw [hb 2]
    unfold VariableEnvelope.B VariableEnvelope.cap
    push_cast
    field_simp [scale_pos.ne']
    ring
  rw [he] at hh
  exact hh.trans (by unfold VariableEnvelope.B; linarith [ht 2])

/-- Actual order comes from compactRegion, even if the raw box crosses
x=y, y=z or the old-cube wall. This removes the old OrdinaryGrid premise. -/
theorem below_mu_boundary_cap_floor (lo hi : Fin 3 → ℤ) (a b : BoxPoint)
    (ha : ∀ i, a i=(lo i:ℝ)/(D₀:ℝ))
    (hb : ∀ i, b i=(hi i:ℝ)/(D₀:ℝ))
    (hmu : b 0≤VariableEnvelope.mu) {t : BoxPoint}
    (ht : t∈compactRegion ∩ Icc a b) :
    (sourceCapLower lo hi:ℝ)/(D₀:ℝ)≤
      actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) := by
  have ho : VariableEnvelope.Ordered (t 0) (t 1) (t 2) :=
    ⟨ht.1.1.1.1.le,ht.1.1.1.2.2.1,ht.1.1.1.2.2.2.1,(ht.2.2 0).trans hmu⟩
  have hbase : (((153*D₀-96*hi 2)/256:ℤ):ℝ)/(D₀:ℝ)≤
      VariableEnvelope.six (t 0) (t 1) (t 2) :=
    (boundary_B_floor hi b hb ht.2.2).trans (VariableEnvelope.B_le_six _ _ _)
  have hterms : ∀ q∈sourceSums.map (fun s =>
      min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi))),
      (q:ℝ)/(D₀:ℝ)≤VariableEnvelope.six (t 0) (t 1) (t 2) := by
    intro q hq
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hq
    exact (boundary_tent_floor lo hi a b ha hb s ht.2).trans (tent_v_le_six s ho)
  have hfold := normalized_foldr_max_le _ _ _ hbase hterms
  have hR : (sourceCapLower lo hi:ℝ)≤
      (((sourceSums.map (fun s =>
        min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi)))).foldr max
          ((153*D₀-96*hi 2)/256):ℤ):ℝ) := by
    exact_mod_cast (min_le_right T₀
      ((sourceSums.map (fun s => min (rawTentLower (rawSum s lo))
        (rawTentLower (rawSum s hi)))).foldr max ((153*D₀-96*hi 2)/256)))
  have hL : (sourceCapLower lo hi:ℝ)≤(T₀:ℝ) := by
    exact_mod_cast (show sourceCapLower lo hi≤T₀ from min_le_left _ _)
  have htheta : (T₀:ℝ)/(D₀:ℝ)=thirdPrefixTheta := by norm_num [thirdPrefixTheta]
  unfold actualExtendedThirdBufferedCap thirdPrefixBufferedCap
  simp only [mul_zero,sub_zero]
  rw [actualExtendedThirdEnvelope_eq_six ho]
  apply le_min
  · rw [←htheta]
    exact div_le_div_of_nonneg_right hL scale_pos.le
  · exact (div_le_div_of_nonneg_right hR scale_pos.le).trans hfold

/-- Literal mu-side dispatch of the original author, not a new policy.
The equality x0=mu takes the author's fallback v_lo branch. -/
def authorCapLower (lo hi : Fin 3 → ℤ) : ℤ :=
  if M₀≤lo 0 then min T₀ (sourceVLower (lo 0) (hi 0))
  else authorBelowCapLower lo hi

theorem authorCapLower_le_theta (lo hi : Fin 3 → ℤ) : authorCapLower lo hi≤T₀ := by
  unfold authorCapLower authorBelowCapLower
  split <;> exact min_le_left _ _

private theorem base_le_foldr_max (zs : List ℤ) (base : ℤ) :
    base≤zs.foldr max base := by
  induction zs with
  | nil => exact le_rfl
  | cons z zs ih => exact ih.trans (le_max_right _ _)

/-- The author's assertion ca>x1+y1 is automatic on the ORIGINAL compact
coordinate cube. It is not another leaf-specific numeric certificate.
The below-mu side uses the always-present B floor; the other side retains
both floor operands of v_lo. In particular, all positive-width descendants
of any original seed inherit this assertion from their endpoint bounds. -/
theorem authorCapLower_residual_of_original_cube (lo hi : Fin 3 → ℤ)
    (hlo : 8053063680≤lo 0) (hhi : ∀ i, hi i≤159383552000) :
    hi 0+hi 1<authorCapLower lo hi := by
  have hsum : hi 0+hi 1≤2*(159383552000:ℤ) := by
    have hx := hhi 0
    have hy := hhi 1
    omega
  have hT : 2*(159383552000:ℤ)<T₀ := by norm_num
  have hB : 2*(159383552000:ℤ)<(153*D₀-96*hi 2)/256 := by
    have hm : (153*D₀-96*(159383552000:ℤ))/256≤(153*D₀-96*hi 2)/256 :=
      Int.ediv_le_ediv (by norm_num) (by have hz := hhi 2; omega)
    exact (by norm_num : 2*(159383552000:ℤ)<
      (153*D₀-96*(159383552000:ℤ))/256).trans_le hm
  have hA : 2*(159383552000:ℤ)<(D₀+lo 0)/2 := by
    have hm : (D₀+(8053063680:ℤ))/2≤(D₀+lo 0)/2 :=
      Int.ediv_le_ediv (by norm_num) (by omega)
    exact (by norm_num : 2*(159383552000:ℤ)<(D₀+(8053063680:ℤ))/2).trans_le hm
  have hC : 2*(159383552000:ℤ)<(57*D₀-96*hi 0)/64 := by
    have hm : (57*D₀-96*(159383552000:ℤ))/64≤(57*D₀-96*hi 0)/64 :=
      Int.ediv_le_ediv (by norm_num) (by have hx := hhi 0; omega)
    exact (by norm_num : 2*(159383552000:ℤ)<
      (57*D₀-96*(159383552000:ℤ))/64).trans_le hm
  unfold authorCapLower
  split
  · exact lt_min (hsum.trans_lt hT)
      (lt_min (hsum.trans_lt hA) (hsum.trans_lt hC))
  · unfold authorBelowCapLower
    exact lt_min (hsum.trans_lt hT)
      ((hsum.trans_lt hB).trans_le (base_le_foldr_max _ _))

/-- The scalar v(x) remains a lower envelope at x=mu, where the analytic
definition still takes its full gated branch. Thus the author's closed
endpoint convention is sound without changing that analytic definition. -/
theorem v_x_le_actual_envelope {t : BoxPoint} (ht : t∈compactRegion) :
    VariableEnvelope.v (t 0)≤actualExtendedThirdEnvelope (t 0) (t 1) (t 2) := by
  by_cases hx : t 0≤VariableEnvelope.mu
  · have ho : VariableEnvelope.Ordered (t 0) (t 1) (t 2) :=
      ⟨ht.1.1.1.le,ht.1.1.2.2.1,ht.1.1.2.2.2.1,hx⟩
    rw [actualExtendedThirdEnvelope_eq_six ho]
    exact VariableEnvelope.v_le_six _ _ _
  · rw [actualExtendedThirdEnvelope,if_neg hx]

theorem author_boundary_cap_floor (lo hi : Fin 3 → ℤ) (a b : BoxPoint)
    (ha : ∀ i, a i=(lo i:ℝ)/(D₀:ℝ))
    (hb : ∀ i, b i=(hi i:ℝ)/(D₀:ℝ)) (hwidth : lo≤hi)
    (hcut : hi 0≤M₀ ∨ M₀≤lo 0) {t : BoxPoint}
    (ht : t∈compactRegion ∩ Icc a b) :
    (authorCapLower lo hi:ℝ)/(D₀:ℝ)≤
      actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) := by
  by_cases hm : M₀≤lo 0
  · rw [authorCapLower,if_pos hm,sourceVLower_eq_endpoint_min _ _ (hwidth 0)]
    have hf := boundary_tent_floor lo hi a b ha hb .x ht.2
    simp only [rawSum,literalTentX,literalTentY,literalTentZ,tentSum,sumX,sumY,sumZ,
      one_mul,zero_mul,zero_add,add_zero] at hf
    have hscalar := hf.trans (v_x_le_actual_envelope ht.1)
    have hfloor : ((min T₀ (min (rawTentLower (lo 0)) (rawTentLower (hi 0))):ℤ):ℝ)/(D₀:ℝ)≤
        ((min (rawTentLower (lo 0)) (rawTentLower (hi 0)):ℤ):ℝ)/(D₀:ℝ) := by
      apply div_le_div_of_nonneg_right _ scale_pos.le
      exact_mod_cast (min_le_right T₀ (min (rawTentLower (lo 0)) (rawTentLower (hi 0))))
    have htop : ((min T₀ (min (rawTentLower (lo 0)) (rawTentLower (hi 0))):ℤ):ℝ)/(D₀:ℝ)≤
        thirdPrefixTheta := by
      have htheta : (T₀:ℝ)/(D₀:ℝ)=thirdPrefixTheta := by norm_num [thirdPrefixTheta]
      rw [←htheta]
      apply div_le_div_of_nonneg_right _ scale_pos.le
      exact_mod_cast (min_le_left T₀ (min (rawTentLower (lo 0)) (rawTentLower (hi 0))))
    simpa only [actualExtendedThirdBufferedCap,thirdPrefixBufferedCap,mul_zero,sub_zero]
      using le_min htop (hfloor.trans hscalar)
  · have hh : hi 0≤M₀ := hcut.resolve_right hm
    have hmu : b 0≤VariableEnvelope.mu := by
      rw [hb 0]
      have hhR : (hi 0:ℝ)≤(M₀:ℝ) := by exact_mod_cast hh
      have he : (M₀:ℝ)/(D₀:ℝ)=VariableEnvelope.mu := by norm_num [VariableEnvelope.mu]
      rw [←he]
      exact div_le_div_of_nonneg_right hhR scale_pos.le
    rw [authorCapLower,if_neg hm,authorBelowCapLower_eq_source lo hi hwidth]
    exact below_mu_boundary_cap_floor lo hi a b ha hb hmu ht

/-- Boundary clipping paid from literal source floors and the SAME reader.
No full-box order, raw-cube, Jensen-range or target integral assumption. -/
theorem author_boundary_clipped_integral (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : BoxPoint)
    (ha : ∀ i, a i=(lo i:ℝ)/(D₀:ℝ))
    (hb : ∀ i, b i=(hi i:ℝ)/(D₀:ℝ))
    (hpositive : ∀ i, 0<a i) (hwidth : ∀ i, a i<b i)
    (hrawWidth : lo≤hi) (hcut : hi 0≤M₀ ∨ M₀≤lo 0)
    (hres : hi 0+hi 1<authorCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc a b,compactKernel t)≤
      4*boxMass a b*value (clippedHigh table lo hi (authorCapLower lo hi)) := by
  exact original_clipped_gap_integral table lo hi (authorCapLower lo hi) a b
    ha hb hpositive hwidth (authorCapLower_le_theta lo hi) hres
    (fun t ht => author_boundary_cap_floor lo hi a b ha hb hrawWidth hcut ht)

end
end ImbalancedChen.P2OriginalCompactBoundaryCapFloorSourceOnly
