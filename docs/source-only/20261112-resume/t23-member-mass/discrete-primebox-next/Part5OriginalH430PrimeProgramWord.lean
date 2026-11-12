import ImbalancedChen.Part5OriginalH430SharpPrimeBox
import ImbalancedChen.Part5OriginalH430EmittedWordBox

namespace ImbalancedChen.Part5OriginalH430PrimeProgramWord
noncomputable section
open Set Filter MeasureTheory Topology
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430NativeQueryPaths Part5OriginalH430IntegerItineraries
open Part5OriginalH430OwnedThetaWord Part5OriginalH430OwnedPrimeBoxWeight
open Part5OriginalH430FixedProgramL1 Part5OriginalH430FixedPrimeScreen Part5OriginalH430SharpPrimeBox
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenRootMass
open Part5OriginalH430PhysicalMassPerturbation

variable {mesh d r : ℕ}

def ints (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) :
    IntegerCoordinates d := fun i j =>
  if h : j.val < arity (shapes code i) then p (e.symm (.inr ⟨i,⟨j.val,h⟩⟩)) else 1

def originalWord (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) :=
  integerWord d [p (e.symm (.inl ()))] code (ints code e p)

private theorem word_fold {A : Type*} [CommMonoid A] (g : ℕ → A) (old : List ℕ)
    (code : Program mesh d) (q : IntegerCoordinates d) :
    ((integerWord d old code q).map g).prod = (old.map g).prod *
      ∏ i : Fin d, ((appendedWord (code i).1 (q i)).map g).prod := by
  induction d generalizing old with
  | zero => simp [integerWord]
  | succ d ih =>
    rw [integerWord,ih,List.map_append,List.prod_append,Fin.prod_univ_succ]
    exact mul_assoc .. 

private theorem batch {A : Type*} [CommMonoid A] (g : ℕ → A) (s : StepShape) (w : Fin (arity s) → ℕ) :
    ((appendedWord s (fun j => if h : j.val < arity s then w ⟨j.val,h⟩ else 1)).map g).prod =
      ∏ i : Fin (arity s), g (w i) := by
  cases s <;> simp [arity,appendedWord,Fin.prod_univ_two,mul_comm]

/-- Exact permutation-free product identity. The integer constructor
itself still appends the physical W2 pair in order [larger,smaller]. -/
theorem word_product {A : Type*} [CommMonoid A] (g : ℕ → A) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) :
    ((originalWord code e p).map g).prod = ∏ i, g (p i) := by
  rw [originalWord,word_fold]
  have h (i : Fin d) : ((appendedWord (code i).1 (ints code e p i)).map g).prod =
      ∏ j : Fin (arity (shapes code i)), g (p (e.symm (.inr ⟨i,j⟩))) :=
    batch g (code i).1 _
  calc
    _ = ∏ v : NativeSlot (shapes code), g (p (e.symm v)) := by
      rw [Fintype.prod_sum_type,Fintype.prod_sigma]
      simp only [h,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,Fintype.prod_unique]
    _ = _ := e.symm.prod_comp (fun i => g (p i))

theorem letters_in_range (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code))
    (p : Fin r → ℕ) {q : ℕ} (hq : q ∈ originalWord code e p) : ∃ i, p i = q := by
  by_contra! hn
  let g := fun u : ℕ => if u = q then (0:ℕ) else 1
  have hl : 0 ∈ (originalWord code e p).map g := List.mem_map.mpr ⟨q,hq,by simp [g]⟩
  have h := word_product g code e p
  rw [List.prod_eq_zero hl] at h
  simpa [g,hn] using h

theorem word_length (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) :
    (originalWord code e p).length = r := by
  have two (w : List ℕ) : (w.map (fun _ => (2:ℕ))).prod = 2^w.length := by
    induction w with
    | nil => simp
    | cons _ _ ih => simp [ih,pow_succ,mul_comm]
  have h := word_product (fun _ => (2:ℕ)) code e p
  rw [two] at h
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  exact (pow_right_strictMono₀ (by decide : 1 < (2:ℕ))).injective h

def base (k : Root) (v : Option ℕ) (t : ℝ) : TypedNode :=
  match v with | none => sourceRoot k 0 t | some n => frozenRoot n k (finiteTau n) t
def node (k : Root) (code : Program mesh d) (v : Option ℕ) (x : NativeSlot (shapes code) → ℝ) :=
  (realize d (base k v (nativeRootCoordinate x)) code (nativeCoordinates (shapes code) x)).physical

theorem literal_word (N : ℕ) (k : Root) (code : Program mesh d) (v : Option ℕ)
    (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) :
    word (node k code v (view e (actualPrimeTupleLog N p))) =
      (originalWord code e p).map (physicalPrime N) := by
  have hcoord : nativeCoordinates (shapes code) (view e (actualPrimeTupleLog N p)) =
      physicalCoordinates N (ints code e p) := by
    funext i j
    unfold nativeCoordinates physicalCoordinates ints
    split_ifs <;> simp [view,actualPrimeTupleLog,physicalPrime]
  unfold node
  rw [hcoord]
  apply realize_word
  cases v <;> rfl

def actualQ (N : ℕ) (k : Root) (v : Option ℕ) (t : ℝ) := (N:ℝ)^(base k v t).physical.total

theorem literal_level {N : ℕ} (hN : 1 < N) (k : Root) (code : Program mesh d) (v : Option ℕ)
    (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) (hp : ∀ i, 0 < p i) :
    let x := view e (actualPrimeTupleLog N p)
    residual (node k code v x) =
      physicalLevel N (actualQ N k v (nativeRootCoordinate x)) (originalWord code e p) := by
  apply residual_eq_physicalLevel hN (realize_total ..) (literal_word N k code v e p)
  intro q hq
  obtain ⟨i,rfl⟩ := letters_in_range code e p hq
  exact hp i

theorem log_product {N : ℕ} (k : Root) (code : Program mesh d) (v : Option ℕ)
    (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) :
    (word (node k code v (view e (actualPrimeTupleLog N p)))).prod = ∏ i, actualPrimeTupleLog N p i := by
  calc
    _ = ((originalWord code e p).map (physicalPrime N)).prod := congrArg List.prod (literal_word N k code v e p)
    _ = ∏ i, physicalPrime N (p i) := word_product _ code e p
    _ = _ := rfl

theorem word_ratio {N : ℕ} {a : ℝ} (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ)
    (hp : p ∈ actualPrimeBoxTuples N (fun _ => a) (fun _ => 1)) (hA : 4 ≤ (N:ℝ)^a) :
    0 ≤ wordFactor 1 (originalWord code e p) ∧
    wordFactor 1 (originalWord code e p) ≤ (2:ℝ)^r * atomWeight p := by
  let w := originalWord code e p
  have hg (q) (hq : q ∈ w) : (4:ℝ) ≤ q := by
    obtain ⟨i,rfl⟩ := letters_in_range code e p hq
    exact hA.trans ((mem_actualPrimeBoxTuples_iff.mp hp i).2.2.1)
  have hw := word_to_harmonic (A := 4) le_rfl w hg 1
  have hb := primeBox_ratio (A := 4) le_rfl w hg
  have hlen := word_length code e p
  change w.length = r at hlen
  rw [hlen] at hw
  norm_num at hw
  have hprod : (0:ℝ) < w.prod := by
    apply Nat.cast_pos.mpr (prod_pos _)
    intro q hq
    have h := hg q hq
    exact_mod_cast (show (0:ℝ)<q by linarith)
  have hr : 1/(w.prod:ℝ) ≤ primeBoxWord w := (div_le_iff₀ hprod).mpr hb.1
  have hweight : primeBoxWord w = atomWeight p := word_product _ code e p
  rw [← hweight]
  refine ⟨nonneg_of_mul_nonneg_left (zero_le_one.trans hw.1) hprod,?_⟩
  calc
    wordFactor 1 w ≤ 2^r/(w.prod:ℝ) := (le_div_iff₀ hprod).mpr hw.2
    _ = 2^r*(1/(w.prod:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)

end
end ImbalancedChen.Part5OriginalH430PrimeProgramWord
