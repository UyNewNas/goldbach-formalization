import ImbalancedChen.Part5OriginalH430OrdinaryPairCounts
import ImbalancedChen.P2SeedFeedbackOriginalNumerical

/-! Actual seven-feedback seed, four positive pair windows. The non-strict
extra support line cuts only the original good polygon and is charged by
the source affine-wall majorant before passing to the limit. -/
namespace ImbalancedChen.Part5OriginalH430SeedPairFeedbackMass
noncomputable section
open Set MeasureTheory Finset
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalAffineProfilePassage
open P2OriginalClosedCellProfileAtoms P2OriginalOldProfilePrimeLimits
open P2OriginalCompactThetaMass P2OriginalPhysicalOldProfileMass
open P2EnhancedSeedSingletonPrimitive (parameters parameters_geometry S)
open P2EnhancedSeedActualFeedbackAssembly (pairCut supportedPair pairCoefficient)
open scoped Classical BigOperators

private abbrev Cut := (Fin 4) ⊕ Unit

private def form (j : Fin 4) : Cut → Coord 2 →L[ℝ] ℝ :=
  Sum.elim (pairForms j) (fun _ => -(pairNumeratorForm parameters j+S • pairDenominatorForm j))

private def bound (j : Fin 4) : Cut → ℝ :=
  Sum.elim (pairBounds parameters j) (fun _ =>
    -(pairNumeratorConstant parameters j-S*pairDenominatorConstant j))

private theorem nonzero (j : Fin 4) (a : Cut) : form j a ≠ 0 := by
  rcases a with a | ⟨⟩
  · exact pairForms_ne j a
  · exact neg_ne_zero.mpr ((pair_profile_form parameters_geometry j).1 S)

/-- The actual original open good domains with the additional closed seed
support test, including the two moving-cutoff lanes. -/
private theorem clipped_sandwich (j : Fin 4) :
    AffineSandwich (enumForms (form j)) (enumBounds (bound j)) (supportedPair j) := by
  unfold AffineSandwich
  rw [←finiteGates_enum,←finiteClosedGates_enum]
  have hform := pair_profile_form parameters_geometry j
  have half {x : Coord 2} (h : x∈W2PairDomain parameters j) : x∈pairHalf parameters j :=
    (pairHalf_partition parameters j x).mpr (Or.inl h)
  constructor
  · intro x hx
    have hmain : x∈W2PairDomain parameters j := by
      rw [pair_as_affine]
      exact fun a => hx (.inl a)
    have h := quotient_upper_lt (pairNumeratorForm parameters j) (pairDenominatorForm j)
      (pairNumeratorConstant parameters j) (pairDenominatorConstant j) S (hform.2.2 x (half hmain))
    refine ⟨hmain,?_⟩
    change pairProfile parameters j x ≤ S
    rw [hform.2.1 x (half hmain)]
    exact (h.mp (hx (.inr ()))).le
  · intro x hx a
    rcases a with a | ⟨⟩
    · have hx' := hx.1
      rw [pair_as_affine] at hx'
      exact (hx' a).le
    · have h := quotient_upper_le (pairNumeratorForm parameters j) (pairDenominatorForm j)
        (pairNumeratorConstant parameters j) (pairDenominatorConstant j) S (hform.2.2 x (half hx.1))
      apply h.mpr
      rw [←hform.2.1 x (half hx.1)]
      exact hx.2

def halfSupport (j : Fin 4) : Set (Coord 2) := pairHalf parameters j ∩ pairCut j

private theorem clipped_half_sandwich (j : Fin 4) :
    AffineSandwich (enumForms (form j)) (enumBounds (bound j)) (halfSupport j) := by
  have hfull := clipped_sandwich j
  have hhalf := pairHalf_sandwich parameters j
  have hform := pair_profile_form parameters_geometry j
  constructor
  · intro x hx
    have h := hfull.1 hx
    exact ⟨(pairHalf_partition parameters j x).mpr (Or.inl h.1),h.2⟩
  · rw [←finiteClosedGates_enum]
    intro x hx a
    rcases a with a | ⟨⟩
    · exact hhalf.2 hx.1 a
    · apply (quotient_upper_le (pairNumeratorForm parameters j) (pairDenominatorForm j)
        (pairNumeratorConstant parameters j) (pairDenominatorConstant j) S (hform.2.2 x hx.1)).mpr
      rw [←hform.2.1 x hx.1]
      exact hx.2

def pairMass (N : ℕ) (L : ℝ) (d : ℕ) (j : Fin 4) : ℝ :=
  truePairTest N L d (halfSupport j) residualPair

theorem prime_pair_feedback {Lmin Lmax ε : ℝ} (hm : 0<Lmin) (hM : Lmin≤Lmax)
    (he : 0<ε) (j : Fin 4) :
    ∃ T : ℕ, ∀ N : ℕ,T≤N → ∀ L∈Icc Lmin Lmax,∀ d : ℕ,
      |pairMass N L d j-pairCoefficient j|<ε := by
  have hb (x : Coord 2) : |residualPair x|≤10 := by
    rw [abs_of_nonneg (residualPair_bounds x).1]; exact (residualPair_bounds x).2
  have hc : halfSupport j ⊆ primeAffineGateRegion (enumForms (controlForms 2))
      (enumBounds controlBounds) := by
    rw [←finiteGates_enum]
    intro x hx
    apply control_contains_box
    have h := (pairHalf_geometry parameters_geometry j hx.1).1
    exact fun i => ⟨h.1 i,h.2 i⟩
  obtain ⟨Tp,hp⟩ := compact_uniform_sandwich hm hM (by norm_num : (0:ℝ)≤10) (half_pos he)
    (enumForms (form j)) (enumBounds (bound j))
    (fun i => nonzero j ((Fintype.equivFin Cut).symm i))
    (enumForms (controlForms 2)) (enumBounds controlBounds)
    (fun i => control_nonzero ((Fintype.equivFin _).symm i))
    (by rw [←finiteGates_enum]; exact control_in_cube 2)
    (clipped_half_sandwich j) hc residualPair residualPair_continuous hb
  obtain ⟨Ta,ha⟩ := compact_multiplier_error (k:=2) hm hM (by norm_num : (0:ℝ)≤60) (half_pos he)
  have hmset : MeasurableSet (supportedPair j) := (measurableSet_W2PairDomain _ _).inter
    (measurableSet_le (measurable_pairProfile parameters j) measurable_const)
  have hk : (∫ x in supportedPair j,residualPair x * ∏ i,1/x i)=pairCoefficient j := by
    apply setIntegral_congr_fun hmset
    exact fun x hx => pair_kernel parameters_geometry j hx.1
  refine ⟨max Tp Ta,?_⟩
  intro N hN L hL d
  have h := hp N ((le_max_left _ _).trans hN) L hL
  obtain ⟨hA,hE⟩ := ha N ((le_max_right _ _).trans hN) L hL
  have hne := fun i => nonzero j ((Fintype.equivFin Cut).symm i)
  have heq := (sandwich_integral (enumForms (form j)) (enumBounds (bound j)) hne
    (clipped_half_sandwich j) residualPair).trans
    (sandwich_integral (enumForms (form j)) (enumBounds (bound j)) hne
      (clipped_sandwich j) residualPair).symm
  rw [heq,hk] at h
  have hlocal := truePairTest_error d (halfSupport j) residualPair (by norm_num : (0:ℝ)≤10) hb hA
  norm_num at hlocal
  have htri := abs_sub_le (pairMass N L d j) (scaledPrimeSum N L (halfSupport j) residualPair)
    (pairCoefficient j)
  unfold pairMass at htri ⊢
  linarith only [htri,hlocal,h,hE]

end
end ImbalancedChen.Part5OriginalH430SeedPairFeedbackMass
