import ImbalancedChen.P1ActualSixthWinnerUniformEndpoints
import ImbalancedChen.P1CommonSixthCompactActualCaller

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The independently defined original compact tuple is turned into a real
COMMON sixth frontier, with the same original prime history and arbitrary
tuple weight. The fixed endpoint supplier is then applied to THAT source.
Both source-specific below-mu parent identity and compact-third evidence
are consumed; no frontier/support/guard/winner conclusion is a premise.

The arithmetic target grows only after compact choice D, coarse winner
labels, auxiliary width and ONE natural endpoint mesh have been fixed.
The actual original comparison cell and the actual attained winner may be
different. Their gains are not duplicated, and their masks are not mixed.
-/

namespace ImbalancedChen.P1OriginalCompactSixthEndpointCaller

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P2CompactThirdHistorySelection
open P2OriginalSixthCompactArithmeticFibre P2OriginalSixthCommonScheduleAndFullQ
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalCommonRefinedSeedHull
open P1CommonSixthCompactActualCaller P1ActualSixthWinnerUniformEndpoints
open Certificates.P2OriginalSixthElevenLogSemantics

/-- Construct the stopped source from its actual causal selected word.
This supplies the original remaining carrier, sign and mass by recursion;
it does not infer a frontier from a modulus support assertion. -/
private theorem frontier_of_valid_selection
    (P : Bool → List ℕ → Bool) (weight : ℕ → ℝ)
    {chosen remaining : List ℕ} (hsub : chosen <+ remaining)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (hvalid : FirstExitValidSelection P pre positive chosen) :
    ∃ s ∈ firstExitDepthFrontier (pre.length + chosen.length) P weight pre positive mass remaining,
      s.selectedPrefix = chosen.reverse ++ pre := by
  induction hsub generalizing pre positive mass with
  | slnil =>
      refine ⟨⟨pre, positive, mass, []⟩, ?_, by simp⟩
      simp [firstExitDepthFrontier]
  | cons q hsub ih =>
      by_cases hc : chosen = []
      · subst chosen
        refine ⟨⟨pre, positive, mass, q :: _⟩, ?_, by simp⟩
        simp [firstExitDepthFrontier]
      · have hlen : 0 < chosen.length := List.length_pos.mpr hc
        have hstop : ¬pre.length + chosen.length ≤ pre.length := by omega
        obtain ⟨s, hs, hselected⟩ := ih pre positive mass hvalid
        refine ⟨s, ?_, hselected⟩
        rw [firstExitDepthFrontier, if_neg hstop]
        exact List.mem_append_left _ hs
  | cons_cons q hsub ih =>
      obtain ⟨s, hs, hselected⟩ := ih (q :: pre) (!positive) (mass * weight q) hvalid.2
      have hstop : ¬pre.length + (q :: chosen).length ≤ pre.length := by simp; omega
      have htarget : (q :: pre).length + chosen.length = pre.length + (q :: chosen).length := by
        simp only [List.length_cons]
        omega
      refine ⟨s, ?_, ?_⟩
      · rw [firstExitDepthFrontier, if_neg hstop, if_pos hvalid.1]
        apply List.mem_append_right
        simpa only [htarget] using hs
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hselected

private theorem original_selection_to_common_sixth
    (d : OriginalData) (N : ℝ) (hN : 1 ≤ N) (chosen pre : List ℕ) (positive : Bool)
    (h : FirstExitValidSelection
      (P1OriginalVariableFifthContinuation.policy5 d.e d.chi d.m d.omega N
        d.rows4 d.licensed4 d.J5 d.rows5) pre positive chosen) :
    FirstExitValidSelection (policy6 d N) pre positive chosen := by
  induction chosen generalizing pre positive with
  | nil => trivial
  | cons p ps ih =>
      exact ⟨fifth_approval_preserved_by_sixth d N hN (!positive) (p :: pre)
          (original_policy5_approval_preserved d N hN (!positive) (p :: pre) h.1),
        ih (p :: pre) (!positive) h.2⟩

/-- Actual original compact source, not an arbitrary six-prime word. Its
real old retained path constructs a COMMON stopped source with exactly
that history and the unchanged original target-deleted carrier. -/
theorem compact_tuple_has_actual_common_sixth_frontier
    {n : ℕ} (D : CompactThirdChoice (commonCore n))
    (N cap : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 D.mesh))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow D.mesh))
    (c : Cell) (p : Fin 6 → ℕ) (hp : p ∈ compactTuples c n N) (weight : ℕ → ℝ) :
    let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
    ∃ s ∈ firstExitDepthFrontier 6 (policy6 d (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ))),
      s.selectedPrefix = tupleHistory6 p := by
  dsimp only
  let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
  let carrier := roughPrimeUniverse N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ))
  obtain ⟨oldLeaf, hleaf, hselected⟩ := compact_tuple_has_actual_retained_fibre c n
    (restrictChoice D c) N cap hN omega homega hcap rows4 licensedOriginal J5 rows5 p hp weight
  obtain ⟨chosen, hsub, hvalid, hpath⟩ := exists_validSelection_of_mem_firstExitRetainedLeaves
    (P1OriginalVariableFifthContinuation.policy5 d.e d.chi d.m d.omega (N : ℝ)
      d.rows4 d.licensed4 d.J5 d.rows5) weight [] carrier true 1 oldLeaf hleaf
  have hchosen : chosen.length = 6 := by
    have hlen := congrArg List.length hpath
    rw [hselected] at hlen
    simpa only [List.length_cons, List.length_nil, List.length_append, List.length_reverse,
      Nat.add_zero] using hlen.symm
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  obtain ⟨s, hs, hsPath⟩ := frontier_of_valid_selection (policy6 d (N : ℝ)) weight hsub []
    true 1 (original_selection_to_common_sixth d (N : ℝ) hNr chosen [] true hvalid)
  refine ⟨s, ?_, hsPath.trans (hpath.symm.trans hselected)⟩
  simpa only [List.length_nil, Nat.zero_add, hchosen] using hs

/-- The original compact caller now receives the fixed finite winner
cover and SAME natural endpoint map. No support, third/H5/upper guard,
frontier or actual-winner premise is requested from an arithmetic caller.
The old comparison cell c is kept separate from the attained label l.1. -/
theorem exists_original_compact_sixth_endpoint_caller
    {n : ℕ} (D : CompactThirdChoice (commonCore n))
    (omega rho : ℝ) (homega : omega ≤ D.roughFloor) (hrho : 0 < rho) (hrhoOmega : rho ≤ omega)
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 D.mesh))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow D.mesh))
    (b : ℝ) (hb : 0 < b) (hbsmall : b ≤ 1 / 1000) :
    let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ b / 36 ∧ ∃ m k : ℕ,
      ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ,
        (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
        ∀ (c : Cell) (p : Fin 6 → ℕ), p ∈ compactTuples c n N →
          actualParent5 d (N : ℝ) (tupleHistory6 p) ≤ oldCap c (actualPrimeTupleLog N p) ∧
          actualParent5 d (N : ℝ) (tupleHistory6 p) =
            oldFifth d (N : ℝ) (rosserAncestor 5 (tupleHistory6 p)) ∧
          ∀ weight : ℕ → ℝ, ∃ s ∈ firstExitDepthFrontier 6 (policy6 d (N : ℝ)) weight [] true 1
            (roughPrimeUniverse N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ))),
            s.selectedPrefix = tupleHistory6 p ∧
            ∃ l ∈ winnerLabels m, WinnerEndpointSupport d b delta m k N s l := by
  dsimp only
  let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
  obtain ⟨delta, hd, hsmall, m, k, hends⟩ := exists_uniform_actual_sixth_winner_endpoints
    d b hb hbsmall rho hrho
  refine ⟨delta, hd, hsmall, m, k, ?_⟩
  filter_upwards [hends, eventually_ge_atTop (2 : ℕ)] with N hendpoint hN
  intro cap hcap c p hp
  have hNnat : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hcaller := compact_original_tuple_common_sixth_admitted D N cap hNnat omega homega
    hcap rows4 licensedOriginal J5 rows5 c p hp
  have hphys : PhysicalCell c (primeHistoryLogCoordinates (N : ℝ) 6 (tupleHistory6 p)) := by
    rw [tupleHistory6_log]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hparent := P5OriginalElevenBelowMuAncestor.actual_parent_eq_original_on_eleven d (N : ℝ)
    (tupleHistory6 p) (by simp [tupleHistory6]) c hphys
  refine ⟨hcaller.1, hparent, ?_⟩
  intro weight
  obtain ⟨s, hs, hselected⟩ := compact_tuple_has_actual_common_sixth_frontier D N cap hNnat
    omega homega hcap rows4 licensedOriginal J5 rows5 c p hp weight
  have hrough : (N : ℝ) ^ rho ≤ (N : ℝ) ^ omega :=
    Real.rpow_le_rpow_of_exponent_le hNr.le hrhoOmega
  rcases hendpoint cap 6 (by decide) ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ)) hrough
      le_rfl weight s hs with hseed | ⟨l, hl, hsupport⟩
  · have hself : rosserAncestor 6 s.selectedPrefix = tupleHistory6 p := by
      rw [hselected]
      exact rosserAncestor_self_of_length 6 _ (by simp [tupleHistory6])
    rw [hself] at hseed
    exact (lt_irrefl _ (hcaller.2.2.1.trans_eq hseed)).elim
  · exact ⟨s, hs, hselected, l, hl, hsupport⟩

end
end ImbalancedChen.P1OriginalCompactSixthEndpointCaller
