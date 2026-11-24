import ImbalancedChen.P4AFallbackCompactEndpointCover
import ImbalancedChen.P4AOriginalSecondResidualSupplier
import ImbalancedChen.P4AOriginalThirdFallbackPrimeTests

/-! SOURCE_ONLY / UNCOMPILED.
The compact inputs are the ORIGINAL second residual trim and the closed
support of the ORIGINAL third continuous trim tests. Their prior weighted
boundary/trim convergence suppliers are retained. No new box source or
gain predicate is supplied by a caller.
-/
namespace ImbalancedChen.P4AFallbackOriginalCompactTrims
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope
open P4AFallbackCanonicalBanks P4AFallbackCompactEndpointCover
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P4AOriginalFull87HistoryCore (width width_pos)

def qSlacks2 (l u : QPoint 2) : Fin 5 → ℚ :=
  ![l 0-25/128,19/96-u 0,l 1-(2*qC (l 0)-1),l 0-u 1,qC (u 0)-3*u 0]
def slacks2 (l u : Point 2) : Fin 5 → ℝ :=
  ![l 0-25/128,19/96-u 0,l 1-(2*C (l 0)-1),l 0-u 1,C (u 0)-3*u 0]

def qSlacks3 (l u : QPoint 3) : Fin 11 → ℚ :=
  ![l 0-25/128,19/96-u 0,l 2,l 1-u 2,l 1+l 2-(2*qC (l 0)-1),
    l 0-u 1-u 2,18*l 2-5*(u 1+u 2),l 2-5/96,3/16-u 1,
    qC (u 0)-3*u 0,qC (u 0)-u 0-u 1-3*u 2]
def slacks3 (l u : Point 3) : Fin 11 → ℝ :=
  ![l 0-25/128,19/96-u 0,l 2,l 1-u 2,l 1+l 2-(2*C (l 0)-1),
    l 0-u 1-u 2,18*l 2-5*(u 1+u 2),l 2-5/96,3/16-u 1,
    C (u 0)-3*u 0,C (u 0)-u 0-u 1-3*u 2]

theorem corners2_iff (l u : QPoint 2) : corners2 l u ↔ ∀ i,0<qSlacks2 l u i := by
  constructor
  · rintro ⟨h0,h1,h2,h3,h4⟩ i
    fin_cases i <;> simp [qSlacks2] <;> linarith
  · intro h
    have h0 := h 0;have h1 := h 1;have h2 := h 2;have h3 := h 3;have h4 := h 4
    norm_num [qSlacks2] at h0 h1 h2 h3 h4
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
theorem corners3_iff (l u : QPoint 3) : corners3 l u ↔ ∀ i,0<qSlacks3 l u i := by
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ i
    fin_cases i <;> simp [qSlacks3] <;> linarith
  · intro h
    have h0 := h 0;have h1 := h 1;have h2 := h 2;have h3 := h 3;have h4 := h 4
    have h5 := h 5;have h6 := h 6;have h7 := h 7;have h8 := h 8;have h9 := h 9;have h10 := h 10
    norm_num [qSlacks3] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,
      by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem slacks2_cast (l u : QPoint 2) (i : Fin 5) :
    slacks2 (realPoint l) (realPoint u) i=(qSlacks2 l u i : ℝ) := by
  fin_cases i <;> simp [slacks2,qSlacks2,realPoint,qC,C] <;> ring
theorem slacks3_cast (l u : QPoint 3) (i : Fin 11) :
    slacks3 (realPoint l) (realPoint u) i=(qSlacks3 l u i : ℝ) := by
  fin_cases i <;> simp [slacks3,qSlacks3,realPoint,qC,C] <;> ring

theorem continuous_slacks2 (i : Fin 5) :
    Continuous (fun p : Point 2 × Point 2 => slacks2 p.1 p.2 i) := by
  fin_cases i <;> simp [slacks2,C] <;> fun_prop
theorem continuous_slacks3 (i : Fin 11) :
    Continuous (fun p : Point 3 × Point 3 => slacks3 p.1 p.2 i) := by
  fin_cases i <;> simp [slacks3,C] <;> fun_prop

theorem second_slacks_pos (t : Point 2) (ht : SecondRegion (t 0) (t 1)) :
    ∀ i,0<slacks2 t t i := by
  have hv := v_eq_C ht.1.le
  have hc := above_mu_old_cap_gt_cube ht.1 ht.2.1
  rcases ht with ⟨hx,hr,hb,ho⟩
  rw [hv] at hc hb
  dsimp only [mu,rho,C] at hx hr hb hc
  intro i
  fin_cases i <;> simp [slacks2,C] <;> linarith

theorem second_lower_good (t : Point 2) (ht : SecondRegion (t 0) (t 1)) :
    lowerGood secondMask t t 0 := by
  have hs := second_initial_physical_gates ht
  have hv := v_eq_C ht.1.le
  have hhalf : (1/2 : ℝ)<v (t 0) := by
    rw [hv]
    dsimp only [C]
    have htop := ht.2.1
    dsimp only [rho] at htop
    linarith
  unfold lowerGood
  rw [realCap_diagonal]
  have hsum : (∑ i∈secondMask,t i)=t 1 := by simp [secondMask]
  rw [hsum]
  refine ⟨by simpa only [←hv] using hs.2.2.2,hhalf.trans hs.2.2.2,?_,?_⟩
  · intro i
    fin_cases i <;> simp [prefixSquareExpr,Fin.sum_univ_two,Finset.sum_filter] <;> linarith [hs.1,hs.2.1,hs.2.2.2]
  · intro i hi
    fin_cases i <;> simp [secondMask,selectedSquareExpr,Fin.sum_univ_two,Finset.sum_filter] at hi ⊢ <;>
      linarith [hs.2.2.1,hs.2.2.2]

theorem third_lower_good (t : Point 3) (ht : ThirdRegion (t 0) (t 1) (t 2)) :
    lowerGood thirdMask t t 0 := by
  have hs := third_initial_physical_gates ht
  have hv := v_eq_C ht.1.le
  have hhalf : (1/2 : ℝ)<v (t 0) := by
    rw [hv]
    dsimp only [C]
    have htop := ht.2.1
    dsimp only [rho] at htop
    linarith
  unfold lowerGood
  rw [realCap_diagonal]
  have hsum : (∑ i∈thirdMask,t i)=t 1+t 2 := by simp [thirdMask]
  rw [hsum]
  refine ⟨by simpa only [←hv] using hs.2.2.2.2.2,hhalf.trans hs.2.2.2.2.2,?_,?_⟩
  · intro i
    fin_cases i <;> simp [prefixSquareExpr,Fin.sum_univ_three,Finset.sum_filter] <;>
      linarith [hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.2.2]
  · intro i hi
    fin_cases i <;> simp [thirdMask,selectedSquareExpr,Fin.sum_univ_three,Finset.sum_filter] at hi ⊢ <;>
      linarith [hs.2.2.2.2.1,hs.2.2.2.2.2]

def pairPoint (p : ℝ × ℝ) : Point 2 := ![p.1,p.2]
def secondCore (delta : ℝ) : Set (Point 2) :=
  pairPoint '' P4AOriginalSecondResidualSupplier.trimmedRegion delta

theorem continuous_pairPoint : Continuous pairPoint := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [pairPoint] <;> fun_prop

theorem secondCore_compact (delta : ℝ) (hd : 0<delta) : IsCompact (secondCore delta) :=
  (P4AOriginalSecondResidualSupplier.isCompact_trimmedRegion hd).image continuous_pairPoint

theorem secondCore_region (delta : ℝ) (hd : 0<delta) {t : Point 2} (ht : t∈secondCore delta) :
    SecondRegion (t 0) (t 1) := by
  obtain ⟨p,hp,rfl⟩ := ht
  have hh := P4AOriginalSecondResidualSupplier.trimmedRegion_subset_physicalDomain hd hp
  rcases hh with ⟨hx,hr,hy,ho⟩
  have hx' : mu<p.1 := by simpa only [mu,Certificates.AboveMuSecondCoarse.mu] using hx
  change SecondRegion p.1 p.2
  refine ⟨hx',hr,?_,ho⟩
  rw [v_eq_C hx'.le]
  dsimp only [C]
  linarith

/-- EXACT prior third trim support, using its original affine region
walls and original five history-clearance rows. -/
def thirdPatch (r : ℕ) (c : P4AOriginalThirdFallbackArchive.Cell) : Set (Point 3) :=
  Icc (fun _ => P4AOriginalThirdFallbackPrimeTests.cut) (fun _ => rho) ∩
    {t | ∀ g : P4AOriginalThirdFallbackPrimeTests.Gate,
      width r≤P4AOriginalThirdFallbackPrimeTests.gate c g t}
def thirdCore (r : ℕ) : Set (Point 3) := ⋃ c : P4AOriginalThirdFallbackArchive.Cell,thirdPatch r c

theorem thirdPatch_compact (r : ℕ) (c : P4AOriginalThirdFallbackArchive.Cell) : IsCompact (thirdPatch r c) := by
  have hc : IsClosed {t : Point 3 | ∀ g : P4AOriginalThirdFallbackPrimeTests.Gate,
      width r≤P4AOriginalThirdFallbackPrimeTests.gate c g t} := by
    have he : {t : Point 3 | ∀ g : P4AOriginalThirdFallbackPrimeTests.Gate,
        width r≤P4AOriginalThirdFallbackPrimeTests.gate c g t} =
        ⋂ g : P4AOriginalThirdFallbackPrimeTests.Gate,
          {t | width r≤P4AOriginalThirdFallbackPrimeTests.gate c g t} := by ext t;simp
    rw [he]
    exact isClosed_iInter (fun g => isClosed_le continuous_const (P4AOriginalThirdFallbackPrimeTests.continuous_gate c g))
  exact isCompact_Icc.inter_right hc

theorem thirdCore_compact (r : ℕ) : IsCompact (thirdCore r) :=
  isCompact_iUnion (fun c => thirdPatch_compact r c)

theorem thirdPatch_region (r : ℕ) (c : P4AOriginalThirdFallbackArchive.Cell)
    {t : Point 3} (ht : t∈thirdPatch r c) : t∈P4AOriginalThirdFallbackJacobian.region c := by
  apply (P4AOriginalThirdFallbackRegions.region_iff_walls c t).mpr
  intro i j
  exact (width_pos r).trans_le (ht.2 (.inl (i,j)))

theorem third_combined_support (r : ℕ) (t : Point 3)
    (ht : P4AOriginalThirdFallbackPrimeTests.combined r t≠0) : t∈thirdCore r := by
  obtain ⟨c,hc⟩ : ∃ c : P4AOriginalThirdFallbackArchive.Cell,
      P4AOriginalThirdFallbackPrimeTests.test r c t≠0 := by
    by_contra! h
    exact ht (by simp [P4AOriginalThirdFallbackPrimeTests.combined,h])
  have hp := P4AOriginalThirdFallbackPrimeTests.region_of_ne hc
  have hg := P4AOriginalThirdFallbackRegions.region_guard hp
  have hb := mem_logPrimeBox.mp (P4AOriginalThirdFallbackPrimeTests.guard_cube hg)
  apply mem_iUnion.mpr
  refine ⟨c,⟨⟨fun i => (hb i).1,fun i => (hb i).2.le⟩,?_⟩⟩
  intro g
  exact (P4AOriginalThirdFallbackPrimeTests.gates_of_ne hc g).le

theorem third_slacks_pos (t : Point 3) (ht : ThirdRegion (t 0) (t 1) (t 2))
    (hw : 5*(t 1+t 2)<18*t 2) : ∀ i,0<slacks3 t t i := by
  have hv := v_eq_C ht.1.le
  have hfirst := above_mu_old_cap_gt_cube ht.1 ht.2.1
  have hthird := (third_initial_physical_gates ht).2.2.2.1
  rcases ht with ⟨hx,hr,hz,hzy,hb,hs,hwlo,hwhi,hcut,hy⟩
  rw [hv] at hfirst hthird hb
  have hs0 : 0<t 1+t 2 := by linarith
  have hwlo' := (le_div_iff₀ hs0).mp hwlo
  have hcut' : (5/96 : ℝ)<t 2 := by
    dsimp only [rho,C] at hr hb
    linarith
  dsimp only [mu,rho,C] at hx hr hb hfirst hthird
  intro i
  fin_cases i <;> simp [slacks3,C] <;> linarith

theorem region_strict_ratio (c : P4AOriginalThirdFallbackArchive.Cell) (t : Point 3)
    (ht : t∈P4AOriginalThirdFallbackJacobian.region c) : 5*(t 1+t 2)<18*t 2 := by
  obtain ⟨s,hs,rfl⟩ := ht
  have hu := P4AOriginalThirdFallbackJacobian.strict_unit c hs
  have hS := P4AOriginalThirdFallbackSlope.positive_s (b := c.1)
    ⟨hu.1.1.le,hu.1.2.le⟩ ⟨hu.2.1.1.le,hu.2.1.2.le⟩
  have hw := mul_lt_mul_of_pos_left hu.2.2.1 hS
  change 5*(P4AOriginalThirdFallbackSlope.S c.1 (s 0) (s 1)-
    P4AOriginalThirdFallbackSlope.Z c.1 (s 0) (s 1) (s 2)+
    P4AOriginalThirdFallbackSlope.Z c.1 (s 0) (s 1) (s 2)) <
    18*P4AOriginalThirdFallbackSlope.Z c.1 (s 0) (s 1) (s 2)
  unfold P4AOriginalThirdFallbackSlope.Z
  nlinarith

theorem thirdCore_region (r : ℕ) {t : Point 3} (ht : t∈thirdCore r) :
    ThirdRegion (t 0) (t 1) (t 2) := by
  obtain ⟨c,hc⟩ := mem_iUnion.mp ht
  exact P4AOriginalThirdFallbackRegions.region_guard (thirdPatch_region r c hc)

theorem thirdCore_slacks (r : ℕ) {t : Point 3} (ht : t∈thirdCore r) :
    ∀ i,0<slacks3 t t i := by
  obtain ⟨c,hc⟩ := mem_iUnion.mp ht
  have hp := thirdPatch_region r c hc
  exact third_slacks_pos t (P4AOriginalThirdFallbackRegions.region_guard hp) (region_strict_ratio c t hp)

theorem good2_of_endpoint (m : ℕ) (j : Label 2 m)
    (hs : ∀ i,0<slacks2 (realPoint (lo m j)) (realPoint (hi m j)) i)
    (hc : capRows secondMask (lo m j) (hi m j) (qLevel secondMask m j)) : good2 m j := by
  refine ⟨(corners2_iff _ _).mpr ?_,?_⟩
  · intro i
    have h := hs i
    rw [slacks2_cast] at h
    exact_mod_cast h
  · simpa only [qLevel_second] using hc

theorem good3_of_endpoint (m : ℕ) (j : Label 3 m)
    (hs : ∀ i,0<slacks3 (realPoint (lo m j)) (realPoint (hi m j)) i)
    (hc : capRows thirdMask (lo m j) (hi m j) (qLevel thirdMask m j)) : good3 m j := by
  refine ⟨(corners3_iff _ _).mpr ?_,?_⟩
  · intro i
    have h := hs i
    rw [slacks3_cast] at h
    exact_mod_cast h
  · simpa only [qLevel_third] using hc

/-- The entire ORIGINAL second residual trim, before rough cutoffs. -/
theorem exists_second_core_owners (delta : ℝ) (hd : 0<delta) :
    ∃ m0 : ℕ,2≤m0 ∧ ∀ m : ℕ,m0≤m → ∀ t∈secondCore delta,
      ∃! j : Label 2 m,t∈logPrimeMeshCell 0 (19/96) m j ∧
        (bank m).second j=some (level2 m j) := by
  obtain ⟨m0,hm0,hM⟩ := exists_compact_endpoint_cover secondMask slacks2 continuous_slacks2
    (secondCore delta) (secondCore_compact delta hd)
    (fun t ht => second_slacks_pos t (secondCore_region delta hd ht))
    (fun t ht => second_lower_good t (secondCore_region delta hd ht))
  refine ⟨m0,hm0,?_⟩
  intro m hm t ht
  obtain ⟨j,hj⟩ := exists_logPrimeMeshCell 0 (19/96) m
    (P4AOriginalBufferedFallbackCaps.secondRegion_in_box (secondCore_region delta hd ht))
  have H := hM m hm t ht j hj
  refine ⟨j,⟨hj,(second_some_iff m j _).mpr ⟨good2_of_endpoint m j H.1 H.2,rfl⟩⟩,?_⟩
  intro k hk
  exact logPrimeMeshCell_unique (by norm_num : (0 : ℝ)≤19/96) hk.1 hj

/-- The prior third continuous test has compact support in this actual
family; every point of that support has its unique retained owner. -/
theorem exists_third_core_owners (r : ℕ) :
    ∃ m0 : ℕ,2≤m0 ∧ ∀ m : ℕ,m0≤m → ∀ t∈thirdCore r,
      ∃! j : Label 3 m,t∈logPrimeMeshCell 0 (19/96) m j ∧
        (bank m).third j=some (level3 m j) := by
  obtain ⟨m0,hm0,hM⟩ := exists_compact_endpoint_cover thirdMask slacks3 continuous_slacks3
    (thirdCore r) (thirdCore_compact r) (fun _ ht => thirdCore_slacks r ht)
    (fun t ht => third_lower_good t (thirdCore_region r ht))
  refine ⟨m0,hm0,?_⟩
  intro m hm t ht
  obtain ⟨j,hj⟩ := exists_logPrimeMeshCell 0 (19/96) m
    (P4AOriginalBufferedFallbackCaps.thirdRegion_in_box (thirdCore_region r ht))
  have H := hM m hm t ht j hj
  refine ⟨j,⟨hj,(third_some_iff m j _).mpr ⟨good3_of_endpoint m j H.1 H.2,rfl⟩⟩,?_⟩
  intro k hk
  exact logPrimeMeshCell_unique (by norm_num : (0 : ℝ)≤19/96) hk.1 hj

theorem exists_third_combined_owners (r : ℕ) :
    ∃ m0 : ℕ,2≤m0 ∧ ∀ m : ℕ,m0≤m → ∀ t : Point 3,
      P4AOriginalThirdFallbackPrimeTests.combined r t≠0 →
      ∃ j : Label 3 m,t∈logPrimeMeshCell 0 (19/96) m j ∧
        (bank m).third j=some (level3 m j) := by
  obtain ⟨m0,hm0,hM⟩ := exists_third_core_owners r
  exact ⟨m0,hm0,fun m hm t ht => (hM m hm t (third_combined_support r t ht)).exists⟩

end
end ImbalancedChen.P4AFallbackOriginalCompactTrims
