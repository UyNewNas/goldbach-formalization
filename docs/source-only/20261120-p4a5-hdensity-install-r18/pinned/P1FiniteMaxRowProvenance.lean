import ImbalancedChen.P1AffineTaggedDecision
import ImbalancedChen.P4AOriginalFourthFifthAffinePrograms
import ImbalancedChen.P1FiniteAffineQuantizerTable

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

An original finite maximum receives a deterministic ROW witness without
changing its tests, cap or policy. The witness must attain the RAW maximum.
Only a strict protected-cap improvement is tagged; inheritance and equality
return none. Original eligibility is never rerun at a rounded current.
The finite row subtype is not an arithmetic occurrence-list quotient.
-/
namespace ImbalancedChen.P1FiniteMaxRowProvenance
noncomputable section
open scoped Classical
open P1FiniteAffineDecisionProgram P1AffineTaggedDecision
open P4AOriginalFourthFifthAffinePrograms P1FiniteAffineQuantizerTable
open P1GuardFrozenFiniteCapAlgebra P1OriginalVariableFourthContinuation
open P1AffineCertifiedMesh P1AffineCertifiedLookup

abbrev Row {ι : Type*} (rows : Finset ι) := {r : ι // r ∈ rows}

def enumeration {ι : Type*} (rows : Finset ι) : List (Row rows) :=
  (Finset.univ : Finset (Row rows)).toList

theorem mem_enumeration {ι : Type*} (rows : Finset ι) (r : Row rows) :
    r ∈ enumeration rows := by simp [enumeration]

section Bank
variable {k : ℕ} {ι : Type*}
  (rows : Finset ι) (tests : ι → List (Gate k))
  (candidate : ι → Program k) (seed : Program k)

def raw : Program k := maxRows tests candidate seed rows.toList

theorem raw_eval (t : Fin k → ℝ) :
    (raw rows tests candidate seed).eval t =
      finiteMax rows (fun r => Passed t (tests r))
        (fun r => (candidate r).eval t) (seed.eval t) := by
  simpa only [raw, eval_maxRows, Finset.toList_toFinset, Passed]
    using eval_maxRows tests candidate seed rows.toList t

/-- The additional two NONSTRICT tests check exact raw attainment.
A tie is allowed; firstWitness only picks one legitimate provenance tag. -/
def witnessTests (r : Row rows) : List (Gate k) :=
  tests r.val ++ [LE (candidate r.val) (raw rows tests candidate seed),
    LE (raw rows tests candidate seed) (candidate r.val)]

theorem passed_witness (t : Fin k → ℝ) (r : Row rows) :
    Passed t (witnessTests rows tests candidate seed r) ↔
      Passed t (tests r.val) ∧
      (raw rows tests candidate seed).eval t = (candidate r.val).eval t := by
  simp only [witnessTests, passed_append, passed_cons, passed_nil,
    holds_LE, and_true]
  constructor
  · rintro ⟨hr,hlo,hhi⟩
    exact ⟨hr,le_antisymm hhi hlo⟩
  · rintro ⟨hr,h⟩
    exact ⟨hr,h.ge,h.le⟩

/-- Even the predecessor is mapped with the SAME protected quantizer.
Concrete fourth/fifth bridges identify it with their actual predecessor. -/
def decision (n : ℕ) (b : ℚ) : Trace k (Option (Row rows)) :=
  .branch
    (LT (protectedProgram n b seed)
      (protectedProgram n b (raw rows tests candidate seed)))
    (firstWitness (witnessTests rows tests candidate seed) (enumeration rows))
    (.leaf none)

/-- A returned tag names the actual raw-attaining row and its OWN
rounded endpoint. No gate licence or signed-gain premise is smuggled in. -/
theorem decision_some_sound (n : ℕ) (b : ℚ) (t : Fin k → ℝ)
    (r : Row rows)
    (hr : (decision rows tests candidate seed n b).eval t = some r) :
    protect n b (seed.eval t) <
        protect n b ((raw rows tests candidate seed).eval t) ∧
      Passed t (tests r.val) ∧
      (raw rows tests candidate seed).eval t = (candidate r.val).eval t ∧
      protect n b ((raw rows tests candidate seed).eval t) =
        (rounded n ((candidate r.val).eval t) : ℝ) := by
  rw [decision, Trace.eval, holds_LT, protectedProgram_exact,
    protectedProgram_exact] at hr
  split_ifs at hr with hwin
  · have hw := (firstWitness_sound (witnessTests rows tests candidate seed)
      (enumeration rows) t r hr).2
    obtain ⟨ht,hraw⟩ := (passed_witness rows tests candidate seed t r).mp hw
    have hb := (seed_le_protect n (b : ℝ) (seed.eval t)).trans_lt hwin
    rw [hraw] at hb
    have hrounded : (b : ℝ) < (rounded n ((candidate r.val).eval t) : ℝ) := by
      simpa only [protect, lt_max_iff, lt_self_iff_false, false_or] using hb
    exact ⟨hwin,ht,hraw,by rw [hraw,protect,max_eq_right hrounded.le]⟩
  · simp only [Trace.eval] at hr
    cases hr

/-- Strict finite improvement rules out raw inheritance. The original
finite maximum itself supplies a valid row; no caller witness is needed. -/
theorem decision_exists_of_strict (n : ℕ) (b : ℚ) (t : Fin k → ℝ)
    (hwin : protect n b (seed.eval t) <
      protect n b ((raw rows tests candidate seed).eval t)) :
    ∃ r : Row rows, (decision rows tests candidate seed n b).eval t = some r := by
  have hattain := finiteMax_attained rows (fun r => Passed t (tests r))
    (fun r => (candidate r).eval t) (seed.eval t)
  rw [← raw_eval rows tests candidate seed t] at hattain
  rcases hattain with h | ⟨r,hr,ht,hraw⟩
  · rw [h] at hwin
    exact (lt_irrefl _ hwin).elim
  · let row : Row rows := ⟨r,hr⟩
    have hw : Passed t (witnessTests rows tests candidate seed row) :=
      (passed_witness rows tests candidate seed t row).mpr ⟨ht,hraw⟩
    obtain ⟨chosen,hchosen⟩ := firstWitness_exists
      (witnessTests rows tests candidate seed) (enumeration rows) t
      ⟨row,mem_enumeration rows row,hw⟩
    refine ⟨chosen,?_⟩
    rw [decision, Trace.eval, holds_LT, protectedProgram_exact,
      protectedProgram_exact, if_pos hwin]
    exact hchosen

theorem decision_none_iff (n : ℕ) (b : ℚ) (t : Fin k → ℝ) :
    (decision rows tests candidate seed n b).eval t = none ↔
      ¬protect n b (seed.eval t) <
        protect n b ((raw rows tests candidate seed).eval t) := by
  constructor
  · intro h hwin
    obtain ⟨r,hr⟩ := decision_exists_of_strict rows tests candidate seed n b t hwin
    rw [h] at hr
    cases hr
  · intro h
    rw [decision, Trace.eval, holds_LT, protectedProgram_exact,
      protectedProgram_exact, if_neg h]
    rfl

/-- No tag on the equality branch, even if an eligible row attains the
same raw value. The original finite maximum itself is not changed. -/
theorem decision_none_of_equal (n : ℕ) (b : ℚ) (t : Fin k → ℝ)
    (h : protect n b (seed.eval t) =
      protect n b ((raw rows tests candidate seed).eval t)) :
    (decision rows tests candidate seed n b).eval t = none := by
  apply (decision_none_iff rows tests candidate seed n b t).mpr
  rw [h]
  exact lt_irrefl _

end Bank

/-- The existing certified lookup fixes the ROW, hence its mask, on the
entire closed box. This lemma also covers the none/inheritance label. -/
theorem covered_fixed_row {k : ℕ} {ι : Type*} [Fintype ι]
    (trace : Trace k ι) (m : ℕ) (t : Fin k → ℝ)
    (ht : t ∈ covered trace.code m) :
    ∃ j ∈ approved trace.code m, t ∈ cell m j ∧
      ∀ u : Fin k → ℝ, (∀ i, lo m j i ≤ u i) → (∀ i, u i ≤ hi m j i) →
        trace.eval u = trace.lookup m t := by
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ht
  obtain ⟨hcert,htj⟩ := Set.mem_iUnion.mp hj
  have hc := (mem_approved _ _ _).mp hcert
  have hb := mem_logPrimeMeshCell.mp htj
  have htag := trace.tag_on_closed_box _ _ _ hc t
    (fun i => (hb i).1) (fun i => (hb i).2.le)
  refine ⟨j,hcert,htj,?_⟩
  intro u hl hu
  rw [Trace.lookup_exact,htag]
  exact trace.tag_on_closed_box _ _ _ hc u hl hu


/-- A single OWN-RANK mesh label certifies BOTH scalar and provenance.
The intersection is not a pair of unrelated boxes, nor a midpoint test. -/
def CapTagBox {k : ℕ} {ι : Type*} [Fintype ι]
    (n m : ℕ) (b : ℚ) (p : Program k) (trace : Trace k ι)
    (t : Fin k → ℝ) : Prop :=
  ∃ j ∈ approved (protectedProgram n b p) m,
    j ∈ approved trace.code m ∧ t ∈ cell m j ∧
    ∃ a ∈ outputAlphabet n b, ∀ u : Fin k → ℝ,
      (∀ i, lo m j i ≤ u i) → (∀ i, u i ≤ hi m j i) →
        scalarLookup n b p m u = (a : ℝ) ∧ trace.eval u = trace.lookup m t

theorem capTagBox_of_covered {k : ℕ} {ι : Type*} [Fintype ι]
    (n m : ℕ) (b : ℚ) (p : Program k) (trace : Trace k ι)
    (t : Fin k → ℝ)
    (hp : t ∈ covered (protectedProgram n b p) m)
    (ht : t ∈ covered trace.code m) : CapTagBox n m b p trace t := by
  obtain ⟨htcube,hjt⟩ := (mem_covered_iff trace.code m t).mp ht
  have hjp := ((mem_covered_iff (protectedProgram n b p) m t).mp hp).2
  have hcell := gridLabel_mem m t htcube
  obtain ⟨a,ha,hscalar⟩ := scalarTable_closed_box n b p m (gridLabel m t) hjp
  have hc := (mem_approved _ _ _).mp hjt
  have hb := mem_logPrimeMeshCell.mp hcell
  have htag := trace.tag_on_closed_box _ _ _ hc t
    (fun i => (hb i).1) (fun i => (hb i).2.le)
  refine ⟨gridLabel m t,hjp,hjt,hcell,a,ha,?_⟩
  intro u hl hu
  refine ⟨hscalar u hl hu,?_⟩
  rw [Trace.lookup_exact,htag]
  exact trace.tag_on_closed_box _ _ _ hc u hl hu

end
end ImbalancedChen.P1FiniteMaxRowProvenance
