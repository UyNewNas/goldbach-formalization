import ImbalancedChen.P1Pair12OriginalLicenceChronology
import ImbalancedChen.OriginalFourthFiniteAtomEndpointRealization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The exact supported-frontier remainder is disintegrated on a finite common
refinement of the actual ORIGINAL and existing checked-bank ancestor covers.
The original licence is kept as supplied; no replacement licence/policy is
introduced. The product of two fixed covers is a common refinement even
when their actual physical caps differ. Signs and the complete same-rho
arithmetic test are preserved in every label contribution.

Both endpoint covers are derived from the SAME actual original rank-four
source state, by the existing true finite-max/chronological support proofs.
Their analytic caps each spend between e/2 and e above that coefficient's
OWN original fourth exponent. These statements concern the outer four-slot
prefix. Later fifth/tail selected-complement licensing is NOT inferred from
an outer-prefix cover and the supported remainder is NOT declared zero.
-/

namespace ImbalancedChen.P1OriginalSupportedRemainderJointCover

noncomputable section
open Classical
open Filter Topology Set
open scoped BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open P1Pair12ActualWireSourceSupport
open P1Pair12RetainedSignedSource
open P1Pair12OriginalLicenceChronology
open OriginalFourthOwnedEndpointBuffer20261026b
open OriginalFourthCanonicalIntegerEndpoints20261026b
open OriginalFourthFiniteAtomEndpointRealization20261026b

abbrev JointLabel (records : List FourthWireRow) (m ko kc : ℕ) :=
  CoverLabel records m ko × CoverLabel records m kc

def jointRegion (records : List FourthWireRow) (m ko kc : ℕ) (omega : ℝ)
    (l : JointLabel records m ko kc) : Set Point :=
  coverRegion records m ko omega l.1 ∩ coverRegion records m kc omega l.2

/-- A true finite product refinement: the unique original and checked
labels are chosen from half-open mesh and strict/weak raw-wall ownership. -/
theorem joint_cover_unique (records : List FourthWireRow) (m ko kc : ℕ)
    (omega : ℝ) {t : Point}
    (ht : t ∈ logPrimeBox (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))) :
    ∃! l : JointLabel records m ko kc, t ∈ jointRegion records m ko kc omega l := by
  obtain ⟨lo, hlo, huO⟩ := finite_cover_unique records m ko omega ht
  obtain ⟨lc, hlc, huC⟩ := finite_cover_unique records m kc omega ht
  refine ⟨(lo, lc), ⟨hlo, hlc⟩, ?_⟩
  intro l hl
  exact Prod.ext (huO l.1 hl.1) (huC l.2 hl.2)

/-- The rank-four SOURCE is the original firstStop/rawQ3 frontier. It is
also the actual producer frontier for every original fourth licence. -/
def commonFrontier (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) : List (FirstExitDepthState ℕ) :=
  firstExitDepthFrontier 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (fun _ : ℕ => 1) [] true 1 (roughPrimeUniverse N cap w z)

def frontierPoint (N : ℕ) (s : FirstExitDepthState ℕ) : Point :=
  primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 s.selectedPrefix)

theorem commonFrontier_is_actual_original
    (records : List FourthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (licensedOriginal : ProducerRow → Prop) (N cap : ℕ) (w z : ℝ)
    (s : FirstExitDepthState ℕ) (hs : s ∈ commonFrontier e chi m omega N cap w z) :
    s ∈ firstExitDepthFrontier 4
      (producerPolicy4 (e : ℝ) chi m omega (N : ℝ) (fourthFamily records) licensedOriginal)
      (fun _ : ℕ => 1) [] true 1 (roughPrimeUniverse N cap w z) := by
  simpa only [producerPolicy4, policy4, fourthCappedUpperPolicy_frontier_four,
    HistoricalThirdCoarse.policy, commonFrontier] using hs

/-- This box membership is obtained from the actual prime carrier. No
ambient-box or unrelated continuous point is a source assumption. -/
theorem commonFrontier_point_in_box
    (records : List FourthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (licensedOriginal : ProducerRow → Prop) (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (hz : z ≤ (N : ℝ) ^ (19 / 96 : ℝ))
    (s : FirstExitDepthState ℕ) (hs : s ∈ commonFrontier e chi m omega N cap w z) :
    frontierPoint N s ∈
      logPrimeBox (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
  exact actual_ancestor_in_cover_box records (e : ℝ) chi m omega licensedOriginal
    N cap hN w z hz (fun _ => 1) 4 le_rfl s
    (commonFrontier_is_actual_original records e chi m omega licensedOriginal N cap w z s hs)

def supportedFrontier (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) : List (FirstExitDepthState ℕ) :=
  (commonFrontier e chi m omega N cap w z).filter (fun s =>
    decide (P1ThirdFallbackSupport.supported (e : ℝ) chi m omega (N : ℝ)
      (rosserAncestor 3 s.selectedPrefix)))

def signedRemainder (records : List FourthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  signedTest (policy5 e chi m omega (N : ℝ) (fourthFamily records) licensedOriginal J5 rows5)
      (fun _ => 1) (attachedLeafTest N cap mark w L G)
      s.selectedPrefix s.positive s.mass s.remaining -
    signedTest (wirePolicy5 e chi m omega records J5 rows5 N)
      (fun _ => 1) (attachedLeafTest N cap mark w L G)
      s.selectedPrefix s.positive s.mass s.remaining

def physicalDifference (records : List FourthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  let Ro := policy5 e chi m omega (N : ℝ) (fourthFamily records) licensedOriginal J5 rows5
  let Rc := wirePolicy5 e chi m omega records J5 rows5 N
  (∑ q ∈ actualSmallRoughModuli (Ro false) N cap w z,
    actualSmallRoughRho (Ro false) N cap w z L q * G (mark * q)) -
  (∑ q ∈ actualSmallRoughModuli (Rc false) N cap w z,
    actualSmallRoughRho (Rc false) N cap w z L q * G (mark * q))

theorem physicalDifference_eq_supported_source
    (records : List FourthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physicalDifference records e chi m omega licensedOriginal J5 rows5 N cap mark w z L G =
      ((supportedFrontier e chi m omega N cap w z).map
        (signedRemainder records e chi m omega licensedOriginal J5 rows5 N cap mark w z L G)).sum := by
  exact actual_original_checked_physical_remainder e chi m omega records licensedOriginal
    J5 rows5 N cap mark w z L G

private theorem sum_map_univ {α β : Type*} [Fintype β] (states : List α) (F : α → β → ℝ) :
    (states.map (fun s => ∑ l : β, F s l)).sum =
      ∑ l : β, (states.map (fun s => F s l)).sum := by
  induction states with
  | nil => simp
  | cons s states ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [ih]

/-- The exact actual same-rho remainder is a sum of fixed finite common
labels. Every label retains its signed continuation test, and no source
term or raw-row face is removed by the disintegration. -/
theorem actual_remainder_eq_joint_label_sum
    (records : List FourthWireRow) (e : ℚ) (chi : ℝ) (m ko kc : ℕ) (omega : ℝ)
    (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap mark : ℕ) (hN : 1 < N) (w z L : ℝ)
    (hz : z ≤ (N : ℝ) ^ (19 / 96 : ℝ)) (G : ℕ → ℝ) :
    physicalDifference records e chi m omega licensedOriginal J5 rows5 N cap mark w z L G =
      ∑ l : JointLabel records m ko kc,
        ((supportedFrontier e chi m omega N cap w z).map (fun s =>
          if frontierPoint N s ∈ jointRegion records m ko kc omega l then
            signedRemainder records e chi m omega licensedOriginal J5 rows5 N cap mark w z L G s
          else 0)).sum := by
  rw [physicalDifference_eq_supported_source]
  have hpartition (s : FirstExitDepthState ℕ)
      (hs : s ∈ supportedFrontier e chi m omega N cap w z) :
      (∑ l : JointLabel records m ko kc,
        if frontierPoint N s ∈ jointRegion records m ko kc omega l then
          signedRemainder records e chi m omega licensedOriginal J5 rows5 N cap mark w z L G s
        else 0) =
      signedRemainder records e chi m omega licensedOriginal J5 rows5 N cap mark w z L G s := by
    have hsall : s ∈ commonFrontier e chi m omega N cap w z := (List.mem_filter.mp hs).1
    have hb := commonFrontier_point_in_box records e chi m omega licensedOriginal
      N cap hN w z hz s hsall
    obtain ⟨l, hl, hunique⟩ := joint_cover_unique records m ko kc omega hb
    rw [Finset.sum_eq_single_of_mem l (Finset.mem_univ l)]
    · exact if_pos hl
    · intro other _ho hne
      apply if_neg
      intro hother
      exact hne (hunique other hother)
  calc
    _ = ((supportedFrontier e chi m omega N cap w z).map (fun s =>
        ∑ l : JointLabel records m ko kc,
          if frontierPoint N s ∈ jointRegion records m ko kc omega l then
            signedRemainder records e chi m omega licensedOriginal J5 rows5 N cap mark w z L G s
          else 0)).sum := by
      congr 1
      apply List.map_congr_left
      intro s hs
      exact (hpartition s hs).symm
    _ = _ := sum_map_univ _ _

/-- The common finite labels and BOTH endpoint meshes are fixed before N.
They cover the actual same original rank-four source for both coefficients,
with their original licences and their OWN physical fourth caps unchanged.
This is an outer-prefix support result; it does not invent later-tail or
selected-complement support from that prefix alone. -/
theorem exists_actual_joint_buffered_remainder_cover
    (records : List FourthWireRow) (e : ℚ) (he : 0 < e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (licensedOriginal : ProducerRow → Prop) (rho : ℝ) (hrho : 0 < rho) :
    ∃ deltaO deltaC : ℝ, 0 < deltaO ∧ deltaO ≤ (e : ℝ) / 24 ∧
      0 < deltaC ∧ deltaC ≤ (e : ℝ) / 24 ∧ ∃ ko no kc nc : ℕ,
      ∀ᶠ N : ℕ in atTop, ∀ (cap : ℕ) (w z : ℝ),
        (N : ℝ) ^ rho ≤ w → z ≤ (N : ℝ) ^ (19 / 96 : ℝ) →
        ∀ s ∈ commonFrontier e chi m omega N cap w z,
          ∃ l : JointLabel records m ko kc,
            frontierPoint N s ∈ jointRegion records m ko kc omega l ∧
            (∀ other : JointLabel records m ko kc,
              frontierPoint N s ∈ jointRegion records m ko kc omega other → other = l) ∧
            (∀ p ∈ s.selectedPrefix.reverse, p ≤ integerUpper no N p) ∧
            actualDwellSupport
              ((N : ℝ) ^ coverCap records (e : ℝ) chi m ko licensedOriginal deltaO l.1)
              (s.selectedPrefix.reverse.map (integerUpper no N)) ∧
            ownedExponent records (e : ℝ) chi m omega (N : ℝ) licensedOriginal s.selectedPrefix +
                (e : ℝ) / 2 ≤ coverCap records (e : ℝ) chi m ko licensedOriginal deltaO l.1 ∧
            coverCap records (e : ℝ) chi m ko licensedOriginal deltaO l.1 ≤
              ownedExponent records (e : ℝ) chi m omega (N : ℝ) licensedOriginal s.selectedPrefix + e ∧
            (∀ p ∈ s.selectedPrefix.reverse, p ≤ integerUpper nc N p) ∧
            actualDwellSupport
              ((N : ℝ) ^ coverCap records (e : ℝ) chi m kc
                (fun r => sourceGeometryFlag r = true) deltaC l.2)
              (s.selectedPrefix.reverse.map (integerUpper nc N)) ∧
            ownedExponent records (e : ℝ) chi m omega (N : ℝ)
                (fun r => sourceGeometryFlag r = true) s.selectedPrefix + (e : ℝ) / 2 ≤
              coverCap records (e : ℝ) chi m kc (fun r => sourceGeometryFlag r = true) deltaC l.2 ∧
            coverCap records (e : ℝ) chi m kc (fun r => sourceGeometryFlag r = true) deltaC l.2 ≤
              ownedExponent records (e : ℝ) chi m omega (N : ℝ)
                (fun r => sourceGeometryFlag r = true) s.selectedPrefix + e := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  obtain ⟨deltaO, hdO, hsO, ko, no, hO⟩ :=
    exists_finite_actual_atom_endpoint_realization records (e : ℝ) chi m omega
      licensedOriginal heR rho hrho
  obtain ⟨deltaC, hdC, hsC, kc, nc, hC⟩ :=
    exists_finite_actual_atom_endpoint_realization records (e : ℝ) chi m omega
      (fun r => sourceGeometryFlag r = true) heR rho hrho
  refine ⟨deltaO, deltaC, hdO, hsO, hdC, hsC, ko, no, kc, nc, ?_⟩
  filter_upwards [hO, hC, eventually_ge_atTop (2 : ℕ)] with N hON hCN hN
  intro cap w z hrough hz s hs
  have hstateO := commonFrontier_is_actual_original records e chi m omega
    licensedOriginal N cap w z s hs
  have hstateC := commonFrontier_is_actual_original records e chi m omega
    (fun r => sourceGeometryFlag r = true) N cap w z s hs
  obtain ⟨lo, hlo, hendO, hfullO, hlowO, hhighO⟩ :=
    hON cap w z hrough hz (fun _ => 1) 4 le_rfl s hstateO
  obtain ⟨lc, hlc, hendC, hfullC, hlowC, hhighC⟩ :=
    hCN cap w z hrough hz (fun _ => 1) 4 le_rfl s hstateC
  have hb := commonFrontier_point_in_box records e chi m omega licensedOriginal
    N cap (by omega) w z hz s hs
  obtain ⟨l, hl, hunique⟩ := joint_cover_unique records m ko kc omega hb
  have hlabels : (lo, lc) = l := hunique (lo, lc) ⟨hlo, hlc⟩
  subst l
  exact ⟨(lo, lc), ⟨hlo, hlc⟩, hunique,
    hendO, hfullO, hlowO, hhighO, hendC, hfullC, hlowC, hhighC⟩

end
end ImbalancedChen.P1OriginalSupportedRemainderJointCover
