import ImbalancedChen.P4AFallbackCanonicalBanks
import ImbalancedChen.CompactLocalThreshold
import ImbalancedChen.P4AOriginalFull87HistoryCore

/-! SOURCE_ONLY / UNCOMPILED.
Necessary compact-to-canonical-box conversion. The endpoint relation is
open only in the STRICT lower and original region rows; the cap's strict
upper tent margin is separately supplied by the positive rational buffer.
There is no caller hypothesis that a selected finite bank already covers.
-/
namespace ImbalancedChen.P4AFallbackCompactEndpointCover
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope
open P4AFallbackCanonicalBanks
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (secondMask thirdMask)
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)

def realCap {k : ℕ} (I : Finset (Fin k)) (l u : Point k) (b : ℝ) : ℝ :=
  min (A (∑ i∈I,l i)) (C (∑ i∈I,u i))-b

def qLevel {k : ℕ} (I : Finset (Fin k)) (m : ℕ) (j : Label k m) : ℚ :=
  qVLo (∑ i∈I,lo m j i) (∑ i∈I,hi m j i)-buffer m

theorem qLevel_cast {k : ℕ} (I : Finset (Fin k)) (m : ℕ) (j : Label k m) :
    (qLevel I m j : ℝ) = realCap I (realPoint (lo m j)) (realPoint (hi m j)) (width m) := by
  simp only [qLevel,Rat.cast_sub,cast_qVLo,Rat.cast_sum,buffer_cast,width,realCap,realPoint]

theorem qLevel_second (m : ℕ) (j : Label 2 m) : qLevel secondMask m j=level2 m j := by
  simp [qLevel,level2,P4AOriginalBufferedFallbackCaps.table2,secondMask,lo,hi]
theorem qLevel_third (m : ℕ) (j : Label 3 m) : qLevel thirdMask m j=level3 m j := by
  simp [qLevel,level3,P4AOriginalBufferedFallbackCaps.table3,thirdMask,lo,hi]

def lowerGood {k : ℕ} [NeZero k] (I : Finset (Fin k)) (l u : Point k) (b : ℝ) : Prop :=
  C (l 0)<realCap I l u b ∧ (1/2 : ℝ)<realCap I l u b ∧
    (∀ i,prefixSquareExpr u i<realCap I l u b) ∧
    (∀ i∉I,selectedSquareExpr I u i<realCap I l u b)

theorem realCap_diagonal {k : ℕ} (I : Finset (Fin k)) (t : Point k) :
    realCap I t t 0=v (∑ i∈I,t i) := by rw [realCap,sub_zero,←v_eq_min]

theorem continuous_realCap {k : ℕ} (I : Finset (Fin k)) :
    Continuous (fun p : (Point k × Point k) × ℝ => realCap I p.1.1 p.1.2 p.2) := by
  unfold realCap A C
  fun_prop

/-- An actual strict center supplies one radius for BOTH rational
corners and the small rational buffer, including all finite mask gates.
-/
theorem exists_endpoint_radius {k a : ℕ} [NeZero k]
    (I : Finset (Fin k)) (slack : Point k → Point k → Fin a → ℝ)
    (hc : ∀ i,Continuous (fun p : Point k × Point k => slack p.1 p.2 i))
    (t : Point k) (hs : ∀ i,0<slack t t i) (hl : lowerGood I t t 0) :
    ∃ d : ℝ,0<d ∧ ∀ l u : Point k,∀ b : ℝ,
      dist l t<d → dist u t<d → |b|<d →
      (∀ i,0<slack l u i) ∧ lowerGood I l u b := by
  let p0 : (Point k × Point k) × ℝ := ((t,t),0)
  have hcap := continuous_realCap I
  have hsl : ∀ᶠ p : (Point k × Point k) × ℝ in 𝓝 p0,∀ i,0<slack p.1.1 p.1.2 i := by
    apply eventually_all.mpr
    intro i
    exact continuousAt_const.eventually_lt ((hc i).comp continuous_fst).continuousAt (hs i)
  have hC : Continuous (fun p : (Point k × Point k) × ℝ => C (p.1.1 0)) := by
    unfold C
    fun_prop
  have hold : ∀ᶠ p : (Point k × Point k) × ℝ in 𝓝 p0,
      C (p.1.1 0)<realCap I p.1.1 p.1.2 p.2 :=
    hC.continuousAt.eventually_lt hcap.continuousAt hl.1
  have hhalf : ∀ᶠ p : (Point k × Point k) × ℝ in 𝓝 p0,
      (1/2 : ℝ)<realCap I p.1.1 p.1.2 p.2 :=
    continuousAt_const.eventually_lt hcap.continuousAt hl.2.1
  have hfull : ∀ᶠ p : (Point k × Point k) × ℝ in 𝓝 p0,
      ∀ i,prefixSquareExpr p.1.2 i<realCap I p.1.1 p.1.2 p.2 := by
    apply eventually_all.mpr
    intro i
    exact ((continuous_prefixSquareExpr i).comp (continuous_snd.comp continuous_fst)).continuousAt.eventually_lt
      hcap.continuousAt (hl.2.2.1 i)
  have hsel : ∀ᶠ p : (Point k × Point k) × ℝ in 𝓝 p0,
      ∀ i∉I,selectedSquareExpr I p.1.2 i<realCap I p.1.1 p.1.2 p.2 := by
    apply eventually_all.mpr
    intro i
    by_cases hi : i∈I
    · exact Eventually.of_forall (fun _ h => False.elim (h hi))
    · exact (((continuous_selectedSquareExpr I i).comp (continuous_snd.comp continuous_fst)).continuousAt.eventually_lt
        hcap.continuousAt (hl.2.2.2 i hi)).mono (fun _ h _ => h)
  obtain ⟨d,hd,hball⟩ := Metric.eventually_nhds_iff.mp
    (hsl.and (hold.and (hhalf.and (hfull.and hsel))))
  refine ⟨d,hd,?_⟩
  intro l u b hl' hu' hb
  apply hball
  simp only [p0,Prod.dist_eq,Real.dist_eq,sub_zero]
  exact max_lt (max_lt hl' hu') hb

theorem qLevel_upper {k : ℕ} (I : Finset (Fin k)) (m : ℕ) (j : Label k m) :
    qLevel I m j<selectedCapUpper I (299/500) (lo m j) (hi m j) := by
  have ht := (closedBox_nonempty m j).choose_spec
  have hsum : ((∑ i∈I,lo m j i : ℚ) : ℝ)≤((∑ i∈I,hi m j i : ℚ) : ℝ) := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => (ht.1 i).trans (ht.2 i))
  have hv := (qVLo_le_v (le_refl ((∑ i∈I,lo m j i : ℚ) : ℝ)) hsum).trans
    (v_le_cap ((∑ i∈I,lo m j i : ℚ) : ℝ))
  have htheta : qVLo (∑ i∈I,lo m j i) (∑ i∈I,hi m j i)<(299/500 : ℚ) := by
    apply (Rat.cast_lt (K := ℝ)).mp
    exact hv.trans_lt (by norm_num [cap])
  have hb := buffer_pos m
  unfold selectedCapUpper qLevel
  exact lt_min (by linarith) (by linarith)

theorem qLevel_capRows {k : ℕ} [NeZero k] (I : Finset (Fin k)) (m : ℕ) (j : Label k m)
    (h : lowerGood I (realPoint (lo m j)) (realPoint (hi m j)) (width m)) :
    capRows I (lo m j) (hi m j) (qLevel I m j) := by
  have hold : qC (lo m j 0)<qLevel I m j := by
    apply (Rat.cast_lt (K := ℝ)).mp
    rw [cast_qC,qLevel_cast]
    exact h.1
  have hhalf : (1/2 : ℚ)<qLevel I m j := by
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_ofNat,qLevel_cast] using h.2.1
  have hfull (i : Fin k) : prefixSquareExpr (hi m j) i<qLevel I m j := by
    apply (Rat.cast_lt (K := ℝ)).mp
    rw [cast_prefixSquareExpr,qLevel_cast]
    exact h.2.2.1 i
  have hsel (i : Fin k) (hi : i∉I) : selectedSquareExpr I (P4AFallbackCanonicalBanks.hi m j) i<qLevel I m j := by
    apply (Rat.cast_lt (K := ℝ)).mp
    rw [cast_selectedSquareExpr,qLevel_cast]
    exact h.2.2.2 i hi
  refine ⟨?_,qLevel_upper I m j⟩
  apply (Finset.max'_lt_iff _ _).mpr
  intro v hv
  simp only [selectedCapLowerSet,Finset.mem_insert,Finset.mem_union,Finset.mem_image] at hv
  rcases hv with rfl | rfl | ⟨i,_,rfl⟩ | ⟨i,hi,rfl⟩
  · exact hold
  · exact hhalf
  · exact hfull i
  · exact hsel i (Finset.mem_sdiff.mp hi).2

/-- Uniform canonical owners on a compact set, before every physical
cutoff or target. The final concrete second/third modules prove these
strict center rows from the actual manuscript trims.
-/
theorem exists_compact_endpoint_cover {k a : ℕ} [NeZero k]
    (I : Finset (Fin k)) (slack : Point k → Point k → Fin a → ℝ)
    (hc : ∀ i,Continuous (fun p : Point k × Point k => slack p.1 p.2 i))
    (K : Set (Point k)) (hK : IsCompact K)
    (hs : ∀ t∈K,∀ i,0<slack t t i) (hl : ∀ t∈K,lowerGood I t t 0) :
    ∃ m0 : ℕ,2≤m0 ∧ ∀ m : ℕ,m0≤m → ∀ t∈K,∀ j : Label k m,
      t∈logPrimeMeshCell 0 (19/96) m j →
      (∀ i,0<slack (realPoint (lo m j)) (realPoint (hi m j)) i) ∧
        capRows I (lo m j) (hi m j) (qLevel I m j) := by
  apply exists_uniform_threshold_on_compact_of_local_nhds K hK
    (fun m t => ∀ j : Label k m,t∈logPrimeMeshCell 0 (19/96) m j →
      (∀ i,0<slack (realPoint (lo m j)) (realPoint (hi m j)) i) ∧
        capRows I (lo m j) (hi m j) (qLevel I m j))
  intro t ht
  obtain ⟨d,hd,hedge⟩ := exists_endpoint_radius I slack hc t (hs t ht) (hl t ht)
  have hsmall : ∀ᶠ m : ℕ in atTop,
      logPrimeMeshStep 0 (19/96) m<d/4 ∧ width m<d :=
    ((tendsto_logPrimeMeshStep 0 (19/96)).eventually (gt_mem_nhds (by positivity))).and
      (width_tendsto.eventually (gt_mem_nhds hd))
  obtain ⟨m0,hm0⟩ := eventually_atTop.mp hsmall
  refine ⟨m0,Metric.eventually_nhds_iff.mpr ⟨d/4,by positivity,?_⟩⟩
  intro x hx m hm j hj
  obtain ⟨hlo,hhi⟩ := logPrimeMesh_endpoints_dist_le_step (by norm_num : (0 : ℝ)≤19/96) hj
  have hlx : dist (realPoint (lo m j)) t<d := by
    have he : realPoint (lo m j)=logPrimeMeshLo 0 (19/96) m j := by
      simpa only [lo,realPoint,Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using cast_qLogPrimeMeshLo 0 (19/96) m j
    rw [he]
    exact (dist_triangle _ x t).trans_lt (by linarith [(hm0 m hm).1])
  have hux : dist (realPoint (hi m j)) t<d := by
    have he : realPoint (hi m j)=logPrimeMeshHi 0 (19/96) m j := by
      simpa only [hi,realPoint,Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using cast_qLogPrimeMeshHi 0 (19/96) m j
    rw [he]
    exact (dist_triangle _ x t).trans_lt (by linarith [(hm0 m hm).1])
  have H := hedge _ _ (width m) hlx hux (by simpa only [abs_of_pos (width_pos m)] using (hm0 m hm).2)
  exact ⟨H.1,qLevel_capRows I m j H.2⟩

end
end ImbalancedChen.P4AFallbackCompactEndpointCover
