import ImbalancedChen.P1ActualCommonSixthWinnerSelectedTail
import ImbalancedChen.P5OriginalElevenBelowMuAncestor
import ImbalancedChen.P5ActualCommonRefinedRange
import ImbalancedChen.OriginalFourthCanonicalIntegerEndpoints
import ImbalancedChen.OriginalSelectedEndpointQuotientInflation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite original winner/corner labels and ONE canonical natural endpoint
map are fixed BEFORE N. Every actually improving policy6 source constructs
its attained winner, own mask/Q6, fixed auxiliary cover and simultaneous
full/selected/complement/ENTIRE-tail endpoint support. The old/common parent
identity is consumed only on that actual eleven-cell source, from the
independently frozen below-mu separation proof.

Native selected critical bounds remain at the unchanged physical Q6.
No assertion moves those strict bounds to the larger auxiliary cover
without a separate uniform winner-specific slack argument. Seed source
terms are retained, and no PP, density, K or gain conclusion is assumed.
-/

namespace ImbalancedChen.P1ActualSixthWinnerUniformEndpoints

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSeedHull
open P1ActualCommonSixthWinnerSelectedTail
open Certificates.P2OriginalSixthElevenLogSemantics
open OriginalFourthCanonicalIntegerEndpoints20261026b
open OriginalSelectedEndpointQuotientInflation20261026b

abbrev WinnerLabel (m : ℕ) := Cell × (Fin 6 → Fin (m + 1))

def winnerLabels (m : ℕ) : Finset (WinnerLabel m) := allCells.toFinset ×ˢ Finset.univ

def winnerCover (b delta : ℝ) (m : ℕ) (l : WinnerLabel m) : ℝ :=
  newCap l.1 (logPrimeMeshLo 0 (19 / 96 : ℝ) m l.2) + 9 * delta + b / 2

private theorem selected_remainder_length6 (c : Cell) (p : Fin 6 → ℕ) :
    ((selectedSlots6 c).map p).length + (remainderPrimes6 c p).length = 6 := by
  cases c <;> simp [selectedSlots6, remainderPrimes6, remainderSlots6, Cell.selectedMask]

theorem endpoint_selected_times_remainder6 (c : Cell) (p : Fin 6 → ℕ)
    (tail : List ℕ) (U : ℕ → ℕ) :
    selectedProduct6 c (fun i => U (p i)) * ((remainderPrimes6 c p ++ tail).map U).prod =
      ((List.ofFn p ++ tail).map U).prod := by
  have hmap : (remainderPrimes6 c p).map U = remainderPrimes6 c (fun i => U (p i)) := by
    simp only [remainderPrimes6, List.map_map, Function.comp_def]
  rw [List.map_append, List.prod_append, ← mul_assoc, hmap,
    selected_times_remaining6, List.map_append, List.prod_append, List.map_ofFn]

/-- The actual original sixth cap has total coordinate modulus at most9:
clipped S5+4r-eta has modulus9, and ascending33-eta has modulus1. -/
theorem newCap_coordinate_oscillation (c : Cell) (t u : Physical) (delta : ℝ)
    (hd : 0 ≤ delta) (hc : ∀ i, |t i - u i| ≤ delta) :
    |newCap c t - newCap c u| ≤ 9 * delta := by
  have h0 := abs_le.mp (hc 0)
  have h1 := abs_le.mp (hc 1)
  have h2 := abs_le.mp (hc 2)
  have h3 := abs_le.mp (hc 3)
  have h4 := abs_le.mp (hc 4)
  have h5 := abs_le.mp (hc 5)
  unfold newCap
  split_ifs <;> dsimp [ascending33, clippedCap, S5]
  all_goals
    apply abs_le.mpr
    constructor <;> linarith

theorem winnerCover_bracket (c : Cell) (t : Physical) (b delta : ℝ) (m : ℕ)
    (j : Fin 6 → Fin (m + 1)) (hd : 0 ≤ delta) (hsmall : delta ≤ b / 36)
    (hc : ∀ i, |t i - logPrimeMeshLo 0 (19 / 96 : ℝ) m j i| ≤ delta) :
    newCap c t + b / 2 ≤ winnerCover b delta m (c, j) ∧
      winnerCover b delta m (c, j) ≤ newCap c t + b := by
  have ho := abs_le.mp (newCap_coordinate_oscillation c t _ delta hd hc)
  unfold winnerCover
  constructor <;> nlinarith

private theorem corner_close (m : ℕ) (delta : ℝ)
    (hm : logPrimeMeshStep 0 (19 / 96 : ℝ) m ≤ delta)
    {j : Fin 6 → Fin (m + 1)} {t : Physical}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96 : ℝ) m j) :
    ∀ i, |t i - logPrimeMeshLo 0 (19 / 96 : ℝ) m j i| ≤ delta := by
  intro i
  have hi := mem_logPrimeMeshCell.mp ht i
  rw [logPrimeMeshHi_eq_lo_add_step] at hi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- One labelled support statement keeps physical lambda6 and native B
separate from the auxiliary analytic cover and endpoint Bupper. -/
def WinnerEndpointSupport (d : OriginalData) (b delta : ℝ) (m n N : ℕ)
    (s : FirstExitDepthState ℕ) (l : WinnerLabel m) : Prop :=
  let a := rosserAncestor 6 s.selectedPrefix
  let p := primeHistoryTuple 6 a
  let t := primeHistoryLogCoordinates (N : ℝ) 6 a
  let lam := lambda6 d (N : ℝ) a
  let C := winnerCover b delta m l
  let B := selectedProduct6 l.1 p
  let Bupper := selectedProduct6 l.1 (fun i => integerUpper n N (p i))
  let T := remainderPrimes6 l.1 p ++ s.selectedPrefix.reverse.drop 6
  eligibleSixth d (N : ℝ) l.1 a ∧ lam = newCap l.1 t ∧
    t ∈ logPrimeMeshCell 0 (19 / 96 : ℝ) m l.2 ∧
    actualParent5 d (N : ℝ) a = oldFifth d (N : ℝ) (rosserAncestor 5 a) ∧
    actualParent5 d (N : ℝ) a ≤ oldCap l.1 t ∧
    lam + b / 2 ≤ C ∧ C ≤ lam + b ∧ C < 3 / 5 ∧
    (∀ q ∈ s.selectedPrefix.reverse, q ≤ integerUpper n N q) ∧
    actualDwellSupport ((N : ℝ) ^ C) (s.selectedPrefix.reverse.map (integerUpper n N)) ∧
    B ≤ Bupper ∧ 0 < Bupper ∧
    actualDwellSupport ((N : ℝ) ^ C / (Bupper : ℝ)) (T.map (integerUpper n N)) ∧
    Bupper * (T.map (integerUpper n N)).prod =
      (s.selectedPrefix.reverse.map (integerUpper n N)).prod ∧
    (N : ℝ) ^ (2 * lam - 1) < (B : ℝ) ∧
    (B : ℝ) < (N : ℝ) ^ ((2 / 3 : ℝ) * (57 / 64 - lam))

/-- The cap labels, natural endpoint mesh and rank budget all precede N.
This covers every actually improving sixth-stage source, including rank6
all-skip source and every retained tail length. The seed alternative is
kept explicitly. No actual winner, support, rank ceiling or guard is a
premise; the independent actual finite maximum supplies its winner. -/
theorem exists_uniform_actual_sixth_winner_endpoints
    (d : OriginalData) (b : ℝ) (hb : 0 < b) (hbsmall : b ≤ 1 / 1000)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ b / 36 ∧ ∃ m n : ℕ,
      ∀ᶠ N : ℕ in atTop, ∀ (cap rank : ℕ) (hrank : 6 ≤ rank) (w z : ℝ),
        (N : ℝ) ^ rho ≤ w → z ≤ (N : ℝ) ^ (19 / 96 : ℝ) →
        ∀ (weight : ℕ → ℝ) (s : FirstExitDepthState ℕ),
          s ∈ firstExitDepthFrontier rank (policy6 d (N : ℝ)) weight [] true 1
            (roughPrimeUniverse N cap w z) →
          lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) =
              actualParent5 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ∨
            ∃ l ∈ winnerLabels m, WinnerEndpointSupport d b delta m n N s l := by
  let R := actualRoughVectorRankBound rho
  let tau : ℝ := b / (4 * ((R : ℝ) + 1))
  let delta : ℝ := b / 72
  have hR : 0 < (R : ℝ) + 1 := by positivity
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hsmall : delta ≤ b / 36 := by dsimp [delta]; linarith
  have hwidth : tau * ((R : ℝ) + 1) ≤ b / 2 := by
    have heq : tau * ((R : ℝ) + 1) = b / 4 := by
      dsimp [tau]
      field_simp [hR.ne']
      <;> ring
    rw [heq]
    linarith
  obtain ⟨m, hm⟩ := ((tendsto_logPrimeMeshStep 0 (19 / 96 : ℝ)).eventually
    (gt_mem_nhds hd)).exists
  obtain ⟨n, _hn, hendpoint⟩ := exists_uniform_canonical_endpoints tau htau
  refine ⟨delta, hd, hsmall, m, n, ?_⟩
  filter_upwards [hendpoint, eventually_ge_atTop (2 : ℕ)] with N hU hN
  intro cap rank hrank w z hrough hz weight s hs
  have hNnat : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNnat
  rcases actual_sixth_frontier_seed_or_winner_licence d N cap rank hNnat hrank w z weight s hs with
    hseed | ⟨c, helig, hwin, hB, hfull, hquot, hfact, hlo, hhi⟩
  · exact Or.inl hseed
  · right
    let a := rosserAncestor 6 s.selectedPrefix
    let p := primeHistoryTuple 6 a
    let t := primeHistoryLogCoordinates (N : ℝ) 6 a
    let lam := lambda6 d (N : ℝ) a
    let S := (selectedSlots6 c).map p
    let T := remainderPrimes6 c p ++ s.selectedPrefix.reverse.drop 6
    let U := integerUpper n N
    have hlen := firstExitDepthFrontier_selected_length rank _ weight []
      (roughPrimeUniverse N cap w z) true 1 (by simp) s hs
    have ha : a.length = 6 := by simp only [a, rosserAncestor_length, hlen]; omega
    have hfront : List.ofFn p = s.selectedPrefix.reverse.take 6 := by
      rw [primeHistoryTuple_ofFn ha]
      simp only [a, rosserAncestor, List.reverse_drop]
      congr 1
      omega
    have hsplit : List.ofFn p ++ s.selectedPrefix.reverse.drop 6 = s.selectedPrefix.reverse := by
      rw [hfront]
      exact List.take_append_drop 6 s.selectedPrefix.reverse
    have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist rank (policy6 d (N : ℝ))
      weight (roughPrimeUniverse N cap w z) s hs
    have hpMem (i : Fin 6) : p i ∈ s.selectedPrefix.reverse := by
      apply (List.take_sublist 6 s.selectedPrefix.reverse).subset
      rw [← hfront]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    have htbox : t ∈ logPrimeBox (fun _ : Fin 6 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
      apply mem_logPrimeBox.mpr
      intro i
      have hp := hsub.subset (hpMem i)
      exact primeCoordinate_mem hNnat (mem_roughPrimeUniverse_prime hp).pos
        ((mem_roughPrimeUniverse_upper hp).trans_le hz)
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 (19 / 96 : ℝ) m htbox
    let C := winnerCover b delta m (c, j)
    have hC : lam + b / 2 ≤ C ∧ C ≤ lam + b := by
      rw [show lam = newCap c t from hwin]
      exact winnerCover_bracket c t b delta m j hd.le hsmall (corner_close m delta hm.le hj)
    have hcap : lam < (153 / 256 : ℝ) := by
      rw [show lam = newCap c t from hwin]
      exact P5Z.ActualCommonRefinedRange.eleven_newCap_lt_envelope helig.2.1
    have hCsmall : C < (3 / 5 : ℝ) := by linarith [hC.2]
    have hep (q : ℕ) (hq : q ∈ s.selectedPrefix.reverse) :
        q ≤ U q ∧ (U q : ℝ) ≤ (N : ℝ) ^ tau * (q : ℝ) := by
      have hmem := hsub.subset hq
      exact hU q (mem_roughPrimeUniverse_prime hmem).pos
        ((mem_roughPrimeUniverse_upper hmem).trans_le hz)
    have hne : s.selectedPrefix.reverse ≠ [] := by
      intro heq
      have hh := congrArg List.length heq
      simp only [List.length_reverse, List.length_nil, hlen] at hh
      omega
    have hRank : s.selectedPrefix.reverse.length ≤ R := by
      apply actualRoughPrimeVector_length_le hNr hrho (by linarith : lam ≤ (5 / 8 : ℝ))
        s.selectedPrefix.reverse hne
        (fun q hq => (mem_roughPrimeUniverse_prime (hsub.subset hq)).pos)
        (fun q hq => hrough.trans (mem_roughPrimeUniverse_lower (hsub.subset hq)))
      exact hfull
    have hbudget : lam + tau * ((R : ℝ) + 1) ≤ C := by linarith [hC.1]
    have hfullU : actualDwellSupport ((N : ℝ) ^ C) (s.selectedPrefix.reverse.map U) := by
      apply actualDwellSupport_upper_inflation hNr htau.le id U s.selectedPrefix.reverse hRank
        (fun q hq => (hep q hq).2)
      · simpa using hfull
      · exact hbudget
    have hSTmem : ∀ q ∈ S ++ T, q ∈ s.selectedPrefix.reverse := by
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hq
        exact hpMem i
      · rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hq
          exact hpMem i
        · exact List.mem_of_mem_drop hq
    have hlengthST : S.length + T.length = s.selectedPrefix.reverse.length := by
      have h6 := selected_remainder_length6 c p
      simp only [S, T, List.length_append, List.length_drop, List.length_reverse]
      omega
    have hquotU := selected_endpoint_quotient_support hNr htau.le S T U
      (fun q hq => (mem_roughPrimeUniverse_prime
        (hsub.subset (hSTmem q (List.mem_append_left _ hq)))).pos)
      (fun q hq => (hep q (hSTmem q (List.mem_append_left _ hq))).1)
      (fun q hq => (hep q (hSTmem q hq)).2)
      (by rw [hlengthST]; exact hRank) hquot hbudget
    have hSU : (S.map U).prod = selectedProduct6 c (fun i => U (p i)) := by
      simp only [S, selectedProduct6, List.map_map, Function.comp_def]
    change selectedProduct6 c p ≤ (S.map U).prod ∧ 0 < (S.map U).prod ∧ _ at hquotU
    rw [hSU] at hquotU
    have hparent := P5OriginalElevenBelowMuAncestor.actual_parent_eq_original_on_eleven
      d (N : ℝ) a ha c helig.2.1
    refine ⟨(c, j), Finset.mem_product.mpr
      ⟨List.mem_toFinset.mpr (allCells_complete c), Finset.mem_univ j⟩, ?_⟩
    dsimp only [WinnerEndpointSupport]
    refine ⟨helig, hwin, hj, hparent, helig.2.2.2, hC.1, hC.2, hCsmall,
      (fun q hq => (hep q hq).1), hfullU, hquotU.1, hquotU.2.1, hquotU.2.2, ?_, hlo, hhi⟩
    have hprod := endpoint_selected_times_remainder6 c p (s.selectedPrefix.reverse.drop 6) U
    rw [hsplit] at hprod
    exact hprod

end
end ImbalancedChen.P1ActualSixthWinnerUniformEndpoints
