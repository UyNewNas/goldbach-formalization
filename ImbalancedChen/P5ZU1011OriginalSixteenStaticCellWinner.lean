import ImbalancedChen.P5ZU1011OriginalSixteenBoxCertificates
import ImbalancedChen.P5ZU1011OriginalSwitchedOscillation
import ImbalancedChen.P5ZU1011OriginalSixteenSnappedTable

/-!
STATIC whole-cell compiler for the original16 bank. A score is read ONLY
at the rational lower corner of a closed box. The candidate bank contains
only concrete wholeBoxEligibleTest=true policies and the switched fallback.
The existing least-winner API is reused without another argmin definition.

Both the selected policy tag and its H248 table atom are fixed by the box,
before N or any arithmetic tuple exists. The selected ordinary expression
then varies only through its clipped actual residual. Every selected
ordinary policy is proved eligible at EVERY point of the whole closed box.
No native H248 density licence, count estimate, AP estimate or mean is
asserted. SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenStaticCellWinner

open Set
open Classical
open U11Integral U11Canonical U11H248 U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenOscillation U1011OriginalSwitchedOscillation
open U1011H248Partition
open scoped BigOperators

noncomputable section

def corner (B : Box) : LogFour := fun i=>(B.lo i:ℝ)

def cornerAtom (B : Box) (p : Policy) : AtomState :=
  chosenState (typedResidual p (corner B)/corner B 3)

def certified (B : Box) (j : ℕ) (_v : LogFour) : Prop :=
  if hj : j<16 then wholeBoxEligibleTest ⟨j,hj⟩ B=true else False

def ordinary (B : Box) (j : ℕ) (v : LogFour) : ℝ :=
  if hj : j<16 then frozenOrdinary (417/5000:ℝ) (cornerAtom B ⟨j,hj⟩) ⟨j,hj⟩ v else 0

def candidateKernel (B : Box) : ℕ→LogFour→ℝ :=
  guarded (certified B) extendedSwitched (ordinary B)

/-- This least winner is selected ONCE at the rational corner. It has no
N, prime tuple, logarithmic evaluation point, or moving-mask argument. -/
def chosenTag (B : Box) : ℕ :=
  Classical.choose (exists_winner Set.univ bank (candidateKernel B) (corner B) (Set.mem_univ _))

theorem chosenTag_spec (B : Box) : chosenTag B∈tags bank ∧
    corner B∈winner Set.univ bank (candidateKernel B) (chosenTag B) :=
  Classical.choose_spec (exists_winner Set.univ bank (candidateKernel B) (corner B) (Set.mem_univ _))

def staticKernel (B : Box) (v : LogFour) : ℝ := candidateKernel B (chosenTag B) v

/-- The actual corner scalar is retained, including every marked H248
knot and the full max-two clamp. It is frozen for the entire cell. -/
theorem cornerAtom_lookup (B : Box) (p : Policy) :
    Part5UpperTables.H248 (max 2 (typedResidual p (corner B)/corner B 3))=
      stateValue (cornerAtom B p) :=
  H248_eq_stateValue (chosenState_mem _)

/-- The score is precisely the original clipped H248 ordinary expression
at the corner; it is not a score recomputed for each arithmetic tuple. -/
theorem ordinary_corner (B : Box) (p : Policy) :
    ordinary B p.val (corner B)=
      4*(1-Part5UpperTables.H248 (max 2 (typedResidual p (corner B)/corner B 3)))/
        max (417/5000:ℝ) (typedResidual p (corner B)) := by
  simp only [ordinary,dif_pos p.isLt,frozenOrdinary]
  rw [cornerAtom_lookup]

/-- Exact existing finite-minimum identity at the static corner. -/
theorem staticKernel_corner_eq_minimum (B : Box) :
    staticKernel B (corner B)=envelope bank (candidateKernel B) (corner B) :=
  (chosenTag_spec B).2.2.1

theorem staticKernel_corner_le_candidate (B : Box) (c : ℕ) (hc : c∈tags bank) :
    staticKernel B (corner B)≤candidateKernel B c (corner B) := by
  rw [staticKernel_corner_eq_minimum]
  exact envelope_le bank (candidateKernel B) (corner B) c hc

theorem chosenTag_least_tie (B : Box) (c : ℕ) (hc : c∈tags bank) (hlt : c<chosenTag B) :
    candidateKernel B c (corner B)≠envelope bank (candidateKernel B) (corner B) :=
  (chosenTag_spec B).2.2.2 c hc hlt

/-- An ordinary winner can never be an ineligible fallback tie: tag0
would be a smaller minimizer. This is the existing least-winner theorem. -/
theorem chosen_successor_data (B : Box) (j : ℕ) (hchosen : chosenTag B=j.succ) :
    ∃ hj : j<16,wholeBoxEligibleTest ⟨j,hj⟩ B=true := by
  have hw := (chosenTag_spec B).2
  rw [hchosen] at hw
  have hc:=ordinary_winner_eligible Set.univ bank (certified B) extendedSwitched
    (ordinary B) j (corner B) hw
  by_cases hj : j<16
  · exact ⟨hj,by simpa only [certified,dif_pos hj] using hc⟩
  · simp only [certified,dif_neg hj] at hc

theorem chosen_ordinary_certificate (B : Box) (p : Policy)
    (hchosen : chosenTag B=p.val.succ) : wholeBoxEligibleTest p B=true := by
  obtain ⟨hj,ht⟩:=chosen_successor_data B p.val hchosen
  exact ht

/-- STATIC selected ordinary policy is actually eligible everywhere in
its whole closed cell, before N and all arithmetic tuple choices. -/
theorem chosen_ordinary_admissible (B : Box) (p : Policy)
    (hchosen : chosenTag B=p.val.succ) :
    ∀ v∈B.region,TypedEligible p v :=
  wholeBoxEligibleTest_sound p B (chosen_ordinary_certificate B p hchosen)

theorem staticKernel_eq_frozenOrdinary (B : Box) (p : Policy)
    (hchosen : chosenTag B=p.val.succ) (v : LogFour) :
    staticKernel B v=frozenOrdinary (417/5000:ℝ) (cornerAtom B p) p v := by
  have htest:=chosen_ordinary_certificate B p hchosen
  simp only [staticKernel,candidateKernel,hchosen,guarded,Nat.succ_ne_zero,if_false,Nat.pred_succ,
    certified,dif_pos p.isLt,htest,if_true,ordinary]

theorem staticKernel_eq_fallback (B : Box) (hchosen : chosenTag B=0) (v : LogFour) :
    staticKernel B v=extendedSwitched v := by
  simp only [staticKernel,candidateKernel,hchosen,guarded,if_pos rfl]

/-- A genuine modulus for the static selected kernel. Its atom and policy
are fixed, so table jumps or tuple-dependent policy choices cannot occur. -/
theorem staticKernel_abs_sub_le (B : Box) (v w : LogFour)
    (hv : v∈compactBox) (hw : w∈compactBox) :
    |staticKernel B v-staticKernel B w|≤10000*l1Delta v w := by
  have hd:=l1Delta_nonneg v w
  cases hchosen : chosenTag B with
  | zero =>
    rw [staticKernel_eq_fallback B hchosen v,staticKernel_eq_fallback B hchosen w]
    exact extendedSwitched_abs_sub_le hv hw
  | succ j =>
    obtain ⟨hj,ht⟩:=chosen_successor_data B j hchosen
    let p : Policy:=⟨j,hj⟩
    have htag : chosenTag B=p.val.succ:=hchosen
    rw [staticKernel_eq_frozenOrdinary B p htag v,staticKernel_eq_frozenOrdinary B p htag w]
    exact (original_frozenOrdinary_abs_sub_le (cornerAtom B p) p v w).trans (by nlinarith)

/-- The lower corner belongs to the entire closed rational box when the
box is valid. This is a structural fact, not an analytic eligibility input. -/
theorem corner_mem_region (B : Box) (hvalid : B.Valid) : corner B∈B.region := by
  constructor
  · intro i
    exact le_rfl
  · intro i
    exact_mod_cast hvalid i

end

end ImbalancedChen.P5Z.U1011OriginalSixteenStaticCellWinner
