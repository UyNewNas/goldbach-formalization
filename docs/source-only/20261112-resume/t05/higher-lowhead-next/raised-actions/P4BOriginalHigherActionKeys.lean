import ImbalancedChen.P4BOriginalHigherActionWinner
import ImbalancedChen.P4AFinitePPSelectedPrefixSquares
import ImbalancedChen.P4AOriginalFiniteFallbackNaturalEndpoints

namespace ImbalancedChen.P4BOriginalHigherActionKeys
noncomputable section
open scoped BigOperators
open Classical VariableEnvelope
open P4BOriginalCollisionWords (Params)
open P4BOriginalHigherLowRepresentative (g d t level lastLevel primeWord atThird owner_data)
open P4BOriginalHigherActionReads (raw point)
open P4BOriginalHigherActionWinner (SourceAction)
open P4BOriginalHigherActionMargins (reserve reserve_bounds)
open P2CanonicalWallFullResidualPayment (canonicalPrefix)
open P4AUpperTaggedFrozenAdmissionCatalogue (canonicalPrefix_ofFn canonicalPrefix_pos)
open P4AFinitePPSelectedPrefixSquares (selected partition exponent_product)
open P4AOriginalFiniteFallbackNaturalEndpoints (tag upper)
open P4BUpperSelectedBoxCapacity (endpoint)
open P4AHeldTaggedCompilerSupport (J0)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4BOriginalMediumLowTriple (representative_raw)

abbrev genuine (P : Params) (J : List ℕ) (b : SourceAction P) :=
  b.arity≤(raw P J).length ∧ (b.admitted J ∧ b.traced J) ∧ lastLevel P J=b.value J

def needsAction (P : Params) (J : List ℕ) : Prop :=
  4≤J.length ∧ t P J 0≤mu ∧ ¬atThird P J ∧ ∃ b,genuine P J b

theorem needsAction_iff (P : Params) {J : List ℕ} (hN : 1<P.N) (he : 0<P.e) (hes : (P.e:ℝ)≤1/2048)
    (step : logPrimeMeshStep 0 (19/96) (d P).m≤(P.e:ℝ)/20) (ho : 0≤P.omega) (hJ : J∈P.words) :
    needsAction P J ↔ 4≤J.length ∧ t P J 0≤mu ∧ ¬atThird P J := by
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1⟩,fun ⟨a,b,c⟩ => ⟨a,b,c,
    P4BOriginalHigherActionWinner.original P hN he hes step ho hJ a b c⟩⟩

def chosen (P : Params) (J : List ℕ) (h : needsAction P J) := h.2.2.2.choose
theorem chosen_genuine (P : Params) (J : List ℕ) (h : needsAction P J) : genuine P J (chosen P J h) :=
  h.2.2.2.choose_spec

variable (P : Params) (J : List ℕ) (b : SourceAction P)
abbrev pr := canonicalPrefix b.arity (g P J)
abbrev tail := (primeWord P J).drop b.arity
def sel := selected b.mask (pr P J b)
def rest := selected b.maskᶜ (pr P J b)++tail P J b
abbrev labels (xs : List ℕ) := xs.map (tag P.N P.T)
abbrev s := ∑i∈b.mask,actualPrimeTupleLog P.N (pr P J b) i
abbrev gap := reserve P.e P.r P.n
abbrev localE := gap P/4
def coverLevel := v (s P J b)-gap P

theorem word_eq (hk : b.arity≤(raw P J).length) :
    List.ofFn (pr P J b)++tail P J b=primeWord P J := by
  rw [canonicalPrefix_ofFn hk]; exact List.take_append_drop _ _

theorem perm (hk : b.arity≤(raw P J).length) :
    (sel P J b++rest P J b).Perm (primeWord P J) := by
  have hh : (sel P J b++rest P J b).Perm (List.ofFn (pr P J b)++tail P J b) := by
    simpa only [sel,rest,List.append_assoc] using (partition b.mask (pr P J b)).append_right (tail P J b)
  exact word_eq P J b hk ▸ hh

theorem labelled (hN : 1<P.N) (hJ : J∈P.words) (hk : b.arity≤(raw P J).length) :
    (labels P (sel P J b)++labels P (rest P J b)).Perm J := by
  have hw := (representative_raw P hN hJ).2
  change labels P (primeWord P J)=J at hw
  have H : (labels P (sel P J b)++labels P (rest P J b)).Perm (labels P (primeWord P J)) := by
    simpa only [labels,List.map_append] using (perm P J b hk).map (tag P.N P.T)
  exact hw ▸ H

/-- Full and selected-complement prefix squares for the *same* auxiliary
cover, at the upper integer key of every fine label in the occupied word. -/
theorem endpoints (hN : 1<P.N) (he : 0<P.e) (hes : (P.e:ℝ)≤1/2048)
    (step : logPrimeMeshStep 0 (19/96) (d P).m≤(P.e:ℝ)/20) (ho : 0<P.omega) (hJ : J∈P.words)
    (hlo : t P J 0≤mu) (raised : ¬atThird P J) (hb : genuine P J b)
    {z : ℝ} (ht : P.T*((J0 P.omega:ℝ)+1)≤z) :
    let H := actualPrimeFineLabelIntegerUpper P.N P.T
    let e := localE P
    let M := coverLevel P J b
    let S := labels P (sel P J b)
    let T := labels P (rest P J b)
    0<e ∧ e≤1/2048 ∧ 1/2≤M ∧ M≤cap-2*e ∧ 0≤s P J b ∧ s P J b≤1 ∧ M+e/2≤v (s P J b) ∧
    (P.N:ℝ)^s P J b≤endpoint H S ∧ endpoint H S≤(P.N:ℝ)^(s P J b+z) ∧
    actualDwellSupport ((P.N:ℝ)^(M+z)) (J.map H) ∧
    actualDwellSupport (((P.N:ℝ)^(M+z))/endpoint H S) (T.map H) ∧ ∀j∈J,0<H j := by
  have hr := (representative_raw P hN hJ).1
  have hw := (representative_raw P hN hJ).2
  change labels P (primeWord P J)=J at hw
  have hU := P4AUpperTaggedParityCompiler.rawSupport_subset_universe _ _ _ _ _ hr
  have hp := canonicalPrefix_pos hU hb.1
  have hx : actualPrimeTupleLog P.N (pr P J b)=point P J b.arity := P4AFull87SamePieceCapVariation.coord_ancestor hb.1 P.N
  have hlevel := P4BOriginalHigherLowRootRows.half_le (by exact_mod_cast he) hes step
    (owner_data P hN he.le ho.le hJ).2.2 hlo
  have hhot := P4BOriginalHigherLowRepresentative.uncovered_raises P hN ho.le hJ raised
  have val : 0<b.value J := by rw [←hb.2.2]; linarith only [hlevel,hhot]
  obtain ⟨hcap,hsq⟩ := P4BOriginalHigherActionWinner.native_margin P he b hb.2.1.1 val
  rw [←hx] at hcap hsq
  let M := coverLevel P J b
  let e := localE P
  have gap0 := (reserve_bounds he P.r P.n).1
  have gapE := (reserve_bounds he P.r P.n).2.2.1
  have hM : lastLevel P J≤M := by change lastLevel P J≤v _-gap P; rw [hb.2.2]; linarith only [hcap]
  have hhalf : (1/2:ℝ)≤M := hlevel.trans (hhot.le.trans hM)
  have hi : M≤cap-2*e := by dsimp only [M,coverLevel,e,localE]; linarith only [v_le_cap (s P J b),gap0]
  have he0 : 0<e := by change 0<reserve _ _ _/4; linarith only [gap0]
  have hes' : e≤1/2048 := by change reserve _ _ _/4≤_; linarith only [hes,gapE]
  have sm : 0≤s P J b := Finset.sum_nonneg (fun i _ => div_nonneg
    (Real.log_nonneg (by exact_mod_cast hp i : (1:ℝ)≤pr P J b i)) (Real.log_nonneg (by exact_mod_cast hN.le : (1:ℝ)≤P.N)))
  have s1 : s P J b≤1 := by
    have upper' : v (s P J b)≤C (s P J b) := (min_le_right _ _).trans (min_le_right _ _)
    change 1/2≤v (s P J b)-reserve _ _ _ at hhalf
    dsimp only [C] at upper'; linarith only [upper',hhalf,gap0]
  have gate : M+e/2≤v (s P J b) := by dsimp only [M,coverLevel,e,localE]; linarith only [gap0]
  have hne : raw P J≠[] := by
    have h3 := P4BOriginalHigherActionReads.arity P hN hJ (Finset.mem_filter.mp hJ).2
    intro h; rw [h] at h3; simp at h3
  have hf := (P4AFinitePPLastOddSupport.full _ _ (width_pos P.r) P.n (d P) hN ho.le hr hne).2
  have full : actualDwellSupport ((P.N:ℝ)^M) (primeWord P J) := fun i hi' => (hf i hi').trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) hM)
  have restD : actualDwellSupport (((P.N:ℝ)^M)/((sel P J b).prod:ℝ)) (rest P J b) :=
    P4AFinitePPSelectedPrefixSquares.complete hN b.mask (pr P J b) hp (tail P J b) M
      (by rw [word_eq P J b hb.1]; exact full)
      (fun j hj => by change _≤v _-gap P; linarith only [hsq j hj])
  obtain ⟨e1,e2,f1,f2,pos⟩ := P4AOriginalFiniteFallbackNaturalEndpoints.general_endpoint_support
    P.m P.n P.N P.N (g P J) (width P.r) P.omega (P4AOriginalFull87RawChronology.cutoff P.N) P.T z (d P)
    (width_pos P.r) he.le hN ho P.T_pos ht hr (sel P J b) (rest P J b) (primeWord P J) rfl
    (perm P J b hb.1) M (s P J b) (exponent_product hN b.mask (pr P J b) hp) full restD
  let H := actualPrimeFineLabelIntegerUpper P.N P.T
  have ep (l : List ℕ) : endpoint (upper P.N P.T) l=endpoint H (labels P l) := by
    simp [endpoint,H,labels,upper,List.map_map,Function.comp_def]
  have eq (l : List ℕ) : l.map (upper P.N P.T)=(labels P l).map H := by rw [labels,List.map_map]; rfl
  rw [ep] at e1 e2 f2
  rw [eq,hw] at f1
  rw [eq] at f2
  refine ⟨he0,hes',hhalf,hi,sm,s1,gate,e1,e2,f1,f2,?_⟩
  intro j hj; rw [←hw] at hj
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
  exact pos p hp

end
end ImbalancedChen.P4BOriginalHigherActionKeys
