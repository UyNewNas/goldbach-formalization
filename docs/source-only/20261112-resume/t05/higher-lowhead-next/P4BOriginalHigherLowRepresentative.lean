import ImbalancedChen.P4BOriginalHigherLowRootRows

namespace ImbalancedChen.P4BOriginalHigherLowRepresentative
noncomputable section
open Classical Set
open P4BOriginalCollisionWords (Params)
open P4BOriginalMediumLowTriple (representative representative_raw)
open P4BOriginalCollisionTensor (ownerHead)
open P4AOriginalFiniteFallbackPhysicalSelected (head)
open P4AOriginalFiniteFallbackSelectedMask (front)
open P4AOriginalOrderedThirdTable
open P4BOriginalHigherLowRootRows (Row)
open P4AFinitePPLastOddSupport (exponent tested)
open P4AFallbackCanonicalBanks (bank)
open P1FiniteAffineDecisionProgram P4AOriginalFourthFifthAffinePrograms
open P4AOriginalFull87HistoryCore (width width_pos)

abbrev d (P : Params) := P4AOriginalNewFifthUnion.data P.e P.q P.a
abbrev g (P : Params) (J : List ℕ) := representative P J
abbrev primeWord (P : Params) (J : List ℕ) := (g P J).primeFactorsList.reverse
abbrev t (P : Params) (J : List ℕ) := actualPrimeTupleLog P.N (ownerHead P J)
abbrev lastLevel (P : Params) (J : List ℕ) :=
  exponent (bank P.m) (width P.r) P.n (d P) P.N (g P J)

def cell (P : Params) (J : List ℕ) : HistoricalThirdCoarse.Cell (d P).m :=
  if h : ∃j∈retained (P.e:ℝ) (d P).m,t P J∈logPrimeMeshCell 0 (19/96) (d P).m j then
    h.choose else fun _ => 0

def level (P : Params) (J : List ℕ) := capValue (P.e:ℝ) (d P).m (cell P J)
def row (P : Params) (J : List ℕ) := P4BOriginalHigherLowRootRows.read (P.e:ℝ) (cell P J)
/-- A test on the fixed raw representative before any HB length or owner
is read. It can also succeed after a higher physical cap was adopted. -/
def atThird (P : Params) (J : List ℕ) :=
  actualDwellSupport ((P.N:ℝ)^level P J) (primeWord P J)

theorem front_eq (xs : List ℕ) (h : 3≤xs.length) : front (head xs) (xs.drop 3)=xs := by
  rcases xs with _|⟨a,xs⟩ <;> try simp at h
  rcases xs with _|⟨b,xs⟩ <;> try simp at h
  rcases xs with _|⟨c,xs⟩ <;> try simp at h
  rfl

theorem length_word (P : Params) (hN : 1<P.N) {J : List ℕ} (hJ : J∈P.words) :
    (primeWord P J).length=J.length := by
  simpa only [Params.wordOf,P4AOriginalFiniteFallbackPhysicalSelected.word,List.length_map] using
    congrArg List.length (representative_raw P hN hJ).2

theorem owner_data (P : Params) (hN : 1<P.N) (he : 0≤P.e) (ho : 0≤P.omega)
    {J : List ℕ} (hJ : J∈P.words) :
    cell P J∈retained (P.e:ℝ) (d P).m ∧ t P J∈logPrimeMeshCell 0 (19/96) (d P).m (cell P J) ∧
      t P J∈portion (d P).m (cell P J) := by
  have hr := (representative_raw P hN hJ).1
  have h3' : 3≤(primeWord P J).length := by
    rw [length_word P hN hJ]
    exact (Finset.mem_filter.mp hJ).2
  have h3 : 3≤(g P J).primeFactorsList.length := by
    simpa only [primeWord,List.length_reverse] using h3'
  have coords : t P J=actualPrimeTupleLog P.N (P2CanonicalWallFullResidualPayment.canonicalPrefix 3 (g P J)) :=
    P4AFull87ActualAffineDeletion.canonical_coords P.N 3 (g P J) h3
  obtain ⟨j,hret,hmem,_⟩ := P4AFinitePPLowActualRoot.owner (bank P.m) (by exact_mod_cast he)
    hN ho hr h3
  have h : ∃i∈retained (P.e:ℝ) (d P).m,t P J∈logPrimeMeshCell 0 (19/96) (d P).m i :=
    ⟨j,hret,coords.symm ▸ hmem⟩
  have H : cell P J=h.choose := by simp only [cell,dif_pos h]
  rw [H]
  refine ⟨h.choose_spec.1,h.choose_spec.2,owned_portion h.choose_spec.2 ?_⟩
  have shape := (front_eq (primeWord P J) (by simpa only [primeWord,List.length_reverse] using h3)).symm
  obtain ⟨hp,hs,_⟩ := P4AOriginalFiniteFallbackSelectedSupport.data_of_word hr (ownerHead P J) _ shape
  have hs' := (actualPrimeTupleLog_strictAnti_iff hN _ hp).mpr hs
  have hpos : 0≤t P J 2 := div_nonneg (Real.log_nonneg (by exact_mod_cast hp 2))
    (Real.log_nonneg (by exact_mod_cast hN.le))
  exact ⟨hpos,(hs' (by decide : (1:Fin 3)<2)).le,(hs' (by decide : (0:Fin 3)<1)).le⟩

theorem covered_of_last_le (P : Params) (hN : 1<P.N) (ho : 0≤P.omega) {J : List ℕ} (hJ : J∈P.words)
    (h : lastLevel P J≤level P J) : atThird P J := by
  have hl := length_word P hN hJ
  have hn : (g P J).primeFactorsList≠[] := by
    intro ha
    have hh := (Finset.mem_filter.mp hJ).2
    simp only [primeWord,ha,List.reverse_nil,List.length_nil] at hl; omega
  have H := (P4AFinitePPLastOddSupport.full (bank P.m) _ (width_pos P.r) P.n (d P) hN ho
    (representative_raw P hN hJ).1 hn).2
  exact fun i hi => (H i hi).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) h)

theorem uncovered_raises (P : Params) (hN : 1<P.N) (ho : 0≤P.omega) {J : List ℕ}
    (hJ : J∈P.words) (h : ¬atThird P J) : level P J<lastLevel P J :=
  lt_of_not_ge (fun hle => h (covered_of_last_le P hN ho hJ hle))

private theorem tested_four (l : List ℕ) (h : l.length=4) : (tested l).length=3 := by
  rcases l with _|⟨p,l⟩ <;> try simp at h
  rcases l with _|⟨q,l⟩ <;> try simp at h
  rcases l with _|⟨r,l⟩ <;> try simp at h
  rcases l with _|⟨s,l⟩ <;> try simp at h
  cases l with
  | nil => rfl
  | cons u l => simp at h

/-- On four actual rough slots the last retained odd test is exactly the
third. Both above-mu fallback reads miss by the literal first-coordinate test. -/
theorem four (P : Params) (hN : 1<P.N) (he : 0≤P.e) (ho : 0≤P.omega)
    {J : List ℕ} (hJ : J∈P.words) (h4 : J.length=4) (hl : t P J 0≤VariableEnvelope.mu) :
    lastLevel P J=level P J := by
  obtain ⟨hj,ht,_⟩ := owner_data P hN he ho hJ
  have hlen : (g P J).primeFactorsList.length=4 := by
    simpa only [primeWord,List.length_reverse] using (length_word P hN hJ).trans h4
  have hstage : P4AOrderedThirdRectangleRate.position (tested (g P J).primeFactorsList).length=.third := by
    rw [tested_four _ hlen]; rfl
  have hcoords : P4AFull87ActualAffineDeletion.coords P.N 3 (primeWord P J)=t P J := rfl
  have no : ¬Passed (t P J) (P4AFull87NativeThirdProgram.common (X 1)) :=
    fun h => (not_lt_of_ge hl) ((P4AOrderedThirdStaticRootPrograms.common_exact _ _).mp h).1
  unfold lastLevel exponent
  rw [hstage]
  simp only [P4AOriginalFiniteFallbackPrograms.code,P4AOriginalFiniteFallbackPrograms.switch_eval,
    P4AOrderedThirdRectangleRate.code,P4AOrderedThirdRankReads.thirdP,hcoords,if_neg (not_lt_of_ge hl),
    Program.eval,eval_allGates,if_neg no,max_self,P4AOrderedThirdStaticRootPrograms.seed_at]
  exact atPoint_on_cell hj ht

end
end ImbalancedChen.P4BOriginalHigherLowRepresentative
