import ImbalancedChen.P2OriginalCompactQ80JensenMoments
import ImbalancedChen.ActualThirdOriginalSixTentRoundedConsumer

/-! SOURCE ONLY / UNCOMPILED.
The selected row is extracted from the literal source find/filter/fold.
The order is x,y,xy,xyz,xz,yz,B; first-active and strict midpoint ties are
unchanged. No old P160 selector is substituted for this Q80 selector. -/
namespace ImbalancedChen.P2OriginalCompactQ80JensenSelectionSourceOnly

noncomputable section
open Set
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly

abbrev SourcePlane := P2OriginalCompactQ80EncloserSourceOnly.Plane

def sourceSums : List TentSum := [.x,.y,.xy,.xyz,.xz,.yz]

def tentRow (s : TentSum) : TentSide → SourcePlane
  | .rise => ⟨1,literalTentX s,literalTentY s,literalTentZ s,2⟩
  | .fall => ⟨57,-96*literalTentX s,-96*literalTentY s,-96*literalTentZ s,64⟩

def baseRow : SourcePlane := ⟨153,0,0,-96,256⟩

def sourceDeltaNumerator (s : TentSum) (v : Fin 3 → ℤ) : ℤ :=
  -50*denominator+256*(literalTentX s*v 0+literalTentY s*v 1+literalTentZ s*v 2)

def branchTest (box : RawBox) (s : TentSum) : TentSide → Prop
  | .rise => sourceDeltaNumerator s box.2 ≤ 0
  | .fall => ¬sourceDeltaNumerator s box.2 ≤ 0 ∧ 0 ≤ sourceDeltaNumerator s box.1

theorem source_direction_order : planeDirections = sourceSums.map
    (fun s => (literalTentX s,literalTentY s,literalTentZ s)) := rfl

theorem planeDifference_self (p : SourcePlane) :
    planeDifference p p = ⟨0,0,0,0,1⟩ := by
  ext <;> simp [planeDifference]

theorem rise_fall_extreme (box : RawBox) (s : TentSum) :
    affineExtreme box (planeDifference (tentRow s .rise) (tentRow s .fall)) true =
      sourceDeltaNumerator s box.2 := by
  cases s <;> norm_num [affineExtreme,planeDifference,tentRow,literalTentX,
    literalTentY,literalTentZ,sourceDeltaNumerator] <;> ring

theorem fall_rise_extreme (box : RawBox) (s : TentSum) :
    affineExtreme box (planeDifference (tentRow s .fall) (tentRow s .rise)) true =
      -sourceDeltaNumerator s box.1 := by
  cases s <;> norm_num [affineExtreme,planeDifference,tentRow,literalTentX,
    literalTentY,literalTentZ,sourceDeltaNumerator] <;> ring

/-- Source first-active priority, including the equality test for the rising
plane. This is a symbolic identity; no cell's guard is evaluated. -/
theorem activeMinPlane_source_formula (box : RawBox) (s : TentSum) :
    activeMinPlane box (vPlanes (literalTentX s) (literalTentY s) (literalTentZ s)) =
      if sourceDeltaNumerator s box.2 ≤ 0 then some (tentRow s .rise)
      else if 0 ≤ sourceDeltaNumerator s box.1 then some (tentRow s .fall) else none := by
  change ([tentRow s .rise,tentRow s .fall].find? (fun p =>
    [tentRow s .rise,tentRow s .fall].all (fun q =>
      decide (affineExtreme box (planeDifference p q) true ≤ 0)))) = _
  simp only [List.find?_cons,List.find?_nil,List.all_cons,List.all_nil,
    planeDifference_self,rise_fall_extreme,fall_rise_extreme]
  have hself : affineExtreme box (⟨0,0,0,0,1⟩ : SourcePlane) true=0 := by
    simp [affineExtreme]
  rw [hself]
  by_cases hr : sourceDeltaNumerator s box.2 ≤ 0
  · simp [hr]
  · by_cases hf : 0 ≤ sourceDeltaNumerator s box.1
    · simp [hr,hf]
    · simp [hr,hf]

theorem activeMinPlane_tent_cases (box : RawBox) (s : TentSum) (p : SourcePlane)
    (hp : activeMinPlane box (vPlanes (literalTentX s) (literalTentY s)
      (literalTentZ s))=some p) :
    ∃ k, p=tentRow s k ∧ branchTest box s k := by
  rw [activeMinPlane_source_formula] at hp
  split_ifs at hp with hr hf
  · exact ⟨.rise,(Option.some.inj hp).symm,hr⟩
  · exact ⟨.fall,(Option.some.inj hp).symm,hr,hf⟩
  · cases hp

theorem affineChoices_source_formula (box : RawBox) :
    affineChoices box =
      ((sourceSums.filterMap (fun s => activeMinPlane box
        (vPlanes (literalTentX s) (literalTentY s) (literalTentZ s)))) ++ [baseRow]).filter
        (fun p => decide (affineExtreme box p true ≤ thetaInteger*p.e)) := rfl

theorem affineChoices_cases (box : RawBox) (p : SourcePlane) (hp : p∈affineChoices box) :
    (p=baseRow ∨ ∃ s k, p=tentRow s k ∧ branchTest box s k) ∧
      affineExtreme box p true ≤ thetaInteger*p.e := by
  rw [affineChoices_source_formula] at hp
  obtain ⟨hm,hroot⟩ := List.mem_filter.mp hp
  refine ⟨?_,of_decide_eq_true hroot⟩
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨s,hs,hp⟩ := List.mem_filterMap.mp hm
    obtain ⟨k,hrow,hbranch⟩ := activeMinPlane_tent_cases box s p hp
    exact Or.inr ⟨s,k,hrow,hbranch⟩
  · exact Or.inl (by simpa using hm)

private theorem midpoint_fold_mem (box : RawBox) (rest : List SourcePlane) (first : SourcePlane) :
    rest.foldl (fun best p =>
      if atMid box p*best.e > atMid box best*p.e then p else best) first ∈ first::rest := by
  induction rest generalizing first with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      split_ifs with h
      · have hm := ih p
        rcases List.mem_cons.mp hm with hm | hm
        · simp [hm]
        · simp [hm]
      · have hm := ih first
        rcases List.mem_cons.mp hm with hm | hm
        · simp [hm]
        · simp [hm]

/-- The exact chosen row survives extraction. A midpoint equality still
keeps the previous row because the source fold uses strict `>`. -/
theorem affineCapLower_selected_cases (box : RawBox) (p : SourcePlane)
    (hp : affineCapLower box=some p) :
    (muInteger ≤ box.1 0 ∧ p=tentRow .x .fall) ∨
      (¬muInteger ≤ box.1 0 ∧
        (p=baseRow ∨ ∃ s k, p=tentRow s k ∧ branchTest box s k) ∧
        affineExtreme box p true ≤ thetaInteger*p.e) := by
  by_cases hm : muInteger ≤ box.1 0
  · left
    refine ⟨hm,?_⟩
    simpa [affineCapLower,hm,tentRow,literalTentX,literalTentY,literalTentZ] using hp.symm
  · right
    refine ⟨hm,?_⟩
    simp only [affineCapLower,if_neg hm] at hp
    cases hc : affineChoices box with
    | nil => simp only [hc] at hp; cases hp
    | cons first rest =>
        rw [hc] at hp
        have he := Option.some.inj hp
        have hmem := midpoint_fold_mem box rest first
        rw [he,←hc] at hmem
        exact affineChoices_cases box p hmem

theorem selected_coefficients (box : RawBox) (p : SourcePlane)
    (hp : affineCapLower box=some p) : 0 < p.e ∧ p.b < p.e ∧ p.c < p.e := by
  rcases affineCapLower_selected_cases box p hp with ⟨hm,rfl⟩ | ⟨hm,hrow,hroot⟩
  · norm_num [tentRow,literalTentX,literalTentY,literalTentZ]
  · rcases hrow with rfl | ⟨s,k,rfl,hbranch⟩
    · norm_num [baseRow]
    · cases s <;> cases k <;>
        norm_num [tentRow,literalTentX,literalTentY,literalTentZ]

theorem selected_denominator_le (box : RawBox) (p : SourcePlane)
    (hp : affineCapLower box=some p) : p.e ≤ 256 := by
  rcases affineCapLower_selected_cases box p hp with ⟨hm,rfl⟩ | ⟨hm,hrow,hroot⟩
  · norm_num [tentRow]
  · rcases hrow with rfl | ⟨s,k,rfl,hbranch⟩
    · norm_num [baseRow]
    · cases k <;> norm_num [tentRow]

/-- The positive OLD residual and one lattice step in x force a span of at
least 1/(e*z1). This is much larger than one Q80 unit on the actual cube.
Consequently the chord division assertion follows from source geometry. -/
theorem source_chord_width_one_ulp (box : RawBox) (g : Geometry box) (p : SourcePlane)
    (hp : affineCapLower box=some p) (he : jensenEligible box p) :
    1/(Certificates.P2HistoricQ80DefectLookup.Q : ℚ) ≤ oldHigh box p-oldLow box p := by
  obtain ⟨he0,hb,hc⟩ := selected_coefficients box p hp
  let nl : ℤ := p.a*denominator+(p.b-p.e)*box.2 0+(p.c-p.e)*box.2 1
  let nh : ℤ := p.a*denominator+(p.b-p.e)*box.1 0+(p.c-p.e)*box.1 1
  have hn : 0 < nl := he.2.2.1
  have hx : 1 ≤ box.2 0-box.1 0 := by have hw := g.width 0; omega
  have hy : 0 ≤ box.2 1-box.1 1 := sub_nonneg.mpr (g.width 1).le
  have hb' : 1 ≤ p.e-p.b := by omega
  have hc' : 0 ≤ p.e-p.c := by omega
  have hx' := mul_le_mul hb' hx (by norm_num : (0 : ℤ)≤1) (by omega : 0≤p.e-p.b)
  have hy' := mul_nonneg hc' hy
  have hdiff : nl+1 ≤ nh := by dsimp [nl,nh]; nlinarith only [hx',hy']
  have hnh : 0 < nh := hn.trans_le (by omega)
  have hz0 := g.raw_positive 2
  have hz1 := hz0.trans (g.width 2)
  have hd0 : (0 : ℚ) < (p.e : ℚ)*(box.1 2 : ℚ) :=
    mul_pos (by exact_mod_cast he0) (by exact_mod_cast hz0)
  have hd1 : (0 : ℚ) < (p.e : ℚ)*(box.2 2 : ℚ) :=
    mul_pos (by exact_mod_cast he0) (by exact_mod_cast hz1)
  have hden : (p.e : ℚ)*(box.1 2 : ℚ) ≤ (p.e : ℚ)*(box.2 2 : ℚ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast (g.width 2).le)
      (by exact_mod_cast he0.le)
  have hmove := div_le_div_of_nonneg_left (by exact_mod_cast hnh.le : (0 : ℚ)≤nh) hd0 hden
  have hnum : (nl : ℚ)+1 ≤ (nh : ℚ) := by exact_mod_cast hdiff
  have hinc := (div_le_div_iff_of_pos_right hd1).2 hnum
  have helo : oldLow box p=(nl : ℚ)/((p.e : ℚ)*(box.2 2 : ℚ))+
      ((p.d : ℚ)-(p.e : ℚ))/(p.e : ℚ) := by
    unfold oldLow
    dsimp [nl]
    push_cast
    field_simp [show (p.e : ℚ)≠0 by exact_mod_cast he0.ne',
      show (box.2 2 : ℚ)≠0 by exact_mod_cast hz1.ne']
    ring
  have hehi : oldHigh box p=(nh : ℚ)/((p.e : ℚ)*(box.1 2 : ℚ))+
      ((p.d : ℚ)-(p.e : ℚ))/(p.e : ℚ) := by
    unfold oldHigh
    dsimp [nh]
    push_cast
    field_simp [show (p.e : ℚ)≠0 by exact_mod_cast he0.ne',
      show (box.1 2 : ℚ)≠0 by exact_mod_cast hz0.ne']
    ring
  have hspan : 1/((p.e : ℚ)*(box.2 2 : ℚ)) ≤ oldHigh box p-oldLow box p := by
    rw [helo,hehi]
    rw [add_div] at hinc
    linarith only [hinc,hmove]
  have hlarge : p.e*box.2 2 ≤ scale := by
    have h1 := mul_le_mul (selected_denominator_le box p hp) (g.upper 2)
      hz1.le (by norm_num : (0 : ℤ)≤256)
    exact h1.trans (by norm_num [rhoInteger,scale])
  have hQ : (p.e : ℚ)*(box.2 2 : ℚ) ≤
      (Certificates.P2HistoricQ80DefectLookup.Q : ℚ) := by
    change (p.e : ℚ)*(box.2 2 : ℚ) ≤ (2 : ℚ)^80
    change p.e*box.2 2 ≤ (2 : ℤ)^80 at hlarge
    exact_mod_cast hlarge
  exact (one_div_le_one_div_of_le hd1 hQ).trans hspan

theorem source_old_strict_span (box : RawBox) (g : Geometry box) (p : SourcePlane)
    (hp : affineCapLower box=some p) (he : jensenEligible box p) :
    oldLow box p < oldHigh box p := by
  have h := source_chord_width_one_ulp box g p hp he
  have hq := one_div_pos.mpr Certificates.P2HistoricQ80DefectLookup.Q_pos
  exact sub_pos.mp (hq.trans_le h)

theorem source_chord_denominator_guard (box : RawBox) (g : Geometry box) (p : SourcePlane)
    (hp : affineCapLower box=some p) (he : jensenEligible box p) :
    0 < (Certificates.P2HistoricQ80DefectLookup.I80.point (oldHigh box p-oldLow box p)).lo := by
  exact Certificates.P2HistoricI80DivisionSoundness.point_lo_pos_of_one_ulp_le _
    (source_chord_width_one_ulp box g p hp he)

theorem tent_root_test (box : RawBox) (s : TentSum) (k : TentSide) :
    affineExtreme box (tentRow s k) true =
      match k with
      | .rise => denominator+literalTentX s*box.2 0+
          literalTentY s*box.2 1+literalTentZ s*box.2 2
      | .fall => 57*denominator-96*(literalTentX s*box.1 0+
          literalTentY s*box.1 1+literalTentZ s*box.1 2) := by
  cases s <;> cases k <;>
    norm_num [affineExtreme,tentRow,literalTentX,literalTentY,literalTentZ] <;> ring

/-- Actual source integer guards imply the old analytic active/root/residual
conditions for the SAME label and side. The newer selector's order is unused. -/
theorem source_tent_geometry (box : RawBox) (s : TentSum) (k : TentSide)
    (hbranch : branchTest box s k)
    (hroot : affineExtreme box (tentRow s k) true ≤ thetaInteger*(tentRow s k).e)
    (hres : jensenEligible box (tentRow s k)) :
    sourceActive s k (decodeCoordinates box.1) (decodeCoordinates box.2) ∧
      planeUpper s k (decodeCoordinates box.1) (decodeCoordinates box.2)≤thirdPrefixTheta ∧
      0<oldNumerator s k (decodeCoordinates box.2) := by
  apply original_selected_tent_guard_bridge s k box.1 box.2 denominator thetaInteger
    (decodeCoordinates box.1) (decodeCoordinates box.2) rfl rfl
    (decode_binding box.1) (decode_binding box.2)
  · exact hbranch
  · rw [tent_root_test] at hroot
    cases k <;> simpa only [tentRow] using hroot
  · have hr := hres.2.2.1
    cases k <;> simpa only [tentRow] using hr

theorem source_tent_endpoints (box : RawBox) (g : Geometry box) (s : TentSum) (k : TentSide) :
    (oldLow box (tentRow s k) : ℝ)=tentOldLow s k (decodeCoordinates box.2) ∧
      (oldHigh box (tentRow s k) : ℝ)=tentOldHigh s k (decodeCoordinates box.1) := by
  have hD : (denominator : ℝ)≠0 := by norm_num [denominator]
  have hlo : (box.1 2 : ℝ)≠0 := by exact_mod_cast (g.raw_positive 2).ne'
  have hhi : (box.2 2 : ℝ)≠0 := by exact_mod_cast ((g.raw_positive 2).trans (g.width 2)).ne'
  have heL : oldLow box (tentRow s k)=literalTentEndpoint s k box.2 denominator := by
    cases k <;> rfl
  have heH : oldHigh box (tentRow s k)=literalTentEndpoint s k box.1 denominator := by
    cases k <;> rfl
  rw [heL,heH]
  exact ⟨literalTentEndpoint_cast s k box.2 denominator (decodeCoordinates box.2)
    hD hhi (decode_binding box.2),
    literalTentEndpoint_cast s k box.1 denominator (decodeCoordinates box.1)
    hD hlo (decode_binding box.1)⟩

end
end ImbalancedChen.P2OriginalCompactQ80JensenSelectionSourceOnly
