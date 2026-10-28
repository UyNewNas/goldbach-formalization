import ImbalancedChen.P2CanonicalPairTentWarmHistory

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original L5 triangle and original L6 piecewise/product domain supply the
contracted marked-pair root squares and the first rough head square.
The once-buffer root is computed from the SAME original physical level.
This does not identify the tent subbank with the full adopted W policy.
-/
namespace ImbalancedChen.P2OriginalPairBufferedRootProvenance
noncomputable section
open scoped Classical
open P2LowerCapPlanIntegerRetention P2OriginalPairRootRoughProducer
open P2OriginalSelectedPairNativeData
open P2OriginalSelectedIntegerPrefixSquares
open P2EnhancedLowerPhysicalNode

/-- Literal original prime-coordinate order: smaller u, larger t. -/
def pairPoint (N : ℕ) (p : ℕ × ℕ) : Fin 2 → ℝ :=
  ![coordinate N p.1,coordinate N p.2]

def originalPairDomain (sixth : Bool) (eta : ℝ) : Set (Fin 2 → ℝ) :=
  if sixth then currentChenUpsilon6LogDomain eta
  else Part5OriginalUpsilon5CausalDictionary.triangle

/-- The actual root keeps the original double-buffer cap and chronological
    pair order; a rational source-ranking floor is absent from this identity. -/
theorem original_root_identity (sixth : Bool) (buffer : ℚ) (N : ℕ) (p : ℕ × ℕ) :
    (pairRoot N p (rootSeed sixth buffer N p)).word =
      [coordinate N p.2,coordinate N p.1] ∧
    (pairRoot N p (rootSeed sixth buffer N p)).cap =
      rootLevel sixth N p - 2*(buffer : ℝ) ∧
    rootSeed sixth buffer N p + (buffer : ℝ) =
      rootLevel sixth N p - (buffer : ℝ) := by
  refine ⟨rfl,rfl,?_⟩
  unfold rootSeed
  ring

/-- Uniform actual L5 root margin. No root square is an input. -/
theorem fifth_buffered_root_squares {x : Fin 2 → ℝ}
    (hx : x ∈ Part5OriginalUpsilon5CausalDictionary.triangle)
    (buffer : ℚ) (hb : buffer ≤ 1/1000) :
    let seed := Part5OriginalUpsilon5CausalDictionary.level (x 0) (x 1) - 2*(buffer : ℝ)
    2*x 1 < seed ∧ x 1+2*x 0 < seed ∧
      x 1+x 0+2*(417/5000 : ℝ) < seed := by
  obtain ⟨hu,hut,ht⟩ := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp hx
  have hl := (Part5OriginalUpsilon5CausalDictionary.level_bounds hu hut.le ht.le).1
  have huhi := hut.trans ht
  have hbR : (buffer : ℝ) ≤ 1/1000 := by exact_mod_cast hb
  dsimp [Part5OriginalUpsilon5CausalDictionary.a,
    Part5OriginalUpsilon5CausalDictionary.h] at hu ht huhi hl ⊢
  constructor
  · linarith
  constructor <;> linarith

/-- Original L6 cutoff/product restriction, not the full external rectangle.
    The product margin pays the two buffers in the first rough head square. -/
theorem sixth_buffered_root_squares {eta : ℝ} (heta : 0 ≤ eta)
    {x : Fin 2 → ℝ} (hx : x ∈ currentChenUpsilon6LogDomain eta)
    (buffer : ℚ) (hb : buffer ≤ 1/1000) (hcrop : 2*(buffer : ℝ) ≤ eta) :
    let seed := P5U6CausalLevelGeometry.physicalLevel (x 0) (x 1) - 2*(buffer : ℝ)
    2*x 1 < seed ∧ x 1+2*x 0 < seed ∧
      x 1+x 0+2*(417/5000 : ℝ) < seed := by
  obtain ⟨hu,huh,hht,htd⟩ :=
    mem_currentChenUpsilon6LogRectangle.mp hx.1
  have hl := (P5U6CausalLevelGeometry.physicalLevel_bounds hu huh.le hht htd.le).1
  have hp : x 0+x 1 ≤ (833/2500 : ℝ)-eta := hx.2
  have hbR : (buffer : ℝ) ≤ 1/1000 := by exact_mod_cast hb
  dsimp [P5U6CausalLevelGeometry.a,P5U6CausalLevelGeometry.h,
    P5U6CausalLevelGeometry.d] at hu huh hht htd hl ⊢
  constructor
  · linarith
  constructor <;> linarith

/-- Both original families feed the SAME stored pair root. Only genuine
    original domain/crop and numerical buffer allocation are premises. -/
theorem original_buffered_root_squares (sixth : Bool) (buffer : ℚ)
    (hb : buffer ≤ 1/1000) {eta : ℝ} (heta : 0 ≤ eta)
    (hcrop : 2*(buffer : ℝ) ≤ eta) (N : ℕ) (p : ℕ × ℕ)
    (hp : pairPoint N p ∈ originalPairDomain sixth eta) :
    2*coordinate N p.2 < rootSeed sixth buffer N p ∧
      coordinate N p.2+2*coordinate N p.1 < rootSeed sixth buffer N p ∧
      coordinate N p.2+coordinate N p.1+2*(417/5000 : ℝ) < rootSeed sixth buffer N p := by
  cases sixth with
  | false =>
      simpa [originalPairDomain,pairPoint,rootSeed,rootLevel] using
        fifth_buffered_root_squares hp buffer hb
  | true =>
      simpa [originalPairDomain,pairPoint,rootSeed,rootLevel] using
        sixth_buffered_root_squares heta hp buffer hb hcrop

/-- Actual ORIGINAL pair root now has integer full/selected-complement
    gates at the double-buffer cap. There is no input root-gate licence. -/
theorem original_integer_root_gates (sixth : Bool) (buffer : ℚ)
    (hb : buffer ≤ 1/1000) {eta : ℝ} (heta : 0 ≤ eta)
    (hcrop : 2*(buffer : ℝ) ≤ eta) {N : ℕ} (hN : 1 < (N : ℝ))
    (p : ℕ × ℕ) (hp1 : p.1.Prime) (hp2 : p.2.Prime)
    (hp : pairPoint N p ∈ originalPairDomain sixth eta) :
    let slots := [(p.2,true),(p.1,true)]
    IntegerSquareGates N (rootSeed sixth buffer N p) 1 (slots.map Prod.fst) ∧
      IntegerSquareGates N (rootSeed sixth buffer N p)
        (selectedPrimes slots).prod (remainingPrimes slots) := by
  let slots := [(p.2,true),(p.1,true)]
  have hsq := original_buffered_root_squares sixth buffer hb heta hcrop N p hp
  have hpos : ∀ v ∈ slots, 0 < v.1 := by
    intro v hv
    simp only [slots,List.mem_cons,List.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hp2.pos
    · exact hp1.pos
  apply physical_slots_to_integer hN slots hpos (rootSeed sixth buffer N p)
  · simpa [slots,logSlots,SquareGates] using And.intro hsq.1.le (And.intro hsq.2.1.le True.intro)
  · simp [slots,logSlots,selectedWord,remainingWord,SquareGates]

/-- The root-domain premise is discharged by the independently defined
    ORIGINAL U5 prime selector, preserving both original prime labels. -/
theorem fifth_selector_root_gates (buffer : ℚ) (hbuffer : 0 ≤ buffer)
    (hb : buffer ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N) {p : ℕ × ℕ}
    (hp : p ∈ P5OriginalU5CausalFinite.pairSupport N) :
    let slots := [(p.2,true),(p.1,true)]
    IntegerSquareGates N (rootSeed false buffer N p) 1 (slots.map Prod.fst) ∧
      IntegerSquareGates N (rootSeed false buffer N p)
        (selectedPrimes slots).prod (remainingPrimes slots) := by
  have hpoint := P5OriginalU5CausalFinite.coordinates_mem_triangle hN hp
  have hcoordinates : P5OriginalU5CausalFinite.coordinates N p = pairPoint N p := by
    funext i
    fin_cases i <;> rfl
  have hdomain : pairPoint N p ∈ originalPairDomain false (2*(buffer : ℝ)) := by
    change pairPoint N p ∈ Part5OriginalUpsilon5CausalDictionary.triangle
    rw [← hcoordinates]
    exact hpoint
  obtain ⟨hc,hA,horder,hH⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hc
  have hbR : 0 ≤ (buffer : ℝ) := by exact_mod_cast hbuffer
  exact original_integer_root_gates false buffer hb (by positivity) (le_refl _)
    (by exact_mod_cast (show 1<N by omega)) p
    (mem_chenAdditivePrimeCarrier.mp hp1).2.1
    (mem_chenAdditivePrimeCarrier.mp hp2).2.1 hdomain

/-- The ORIGINAL retained L6 selector supplies the extra product crop,
    centre-coprime primes and exactly the same complement of E. Full
    lowerRows without this product gate are deliberately not substituted. -/
theorem sixth_selector_root_gates (buffer : ℚ) (hb : buffer ≤ 1/1000)
    {eta : ℝ} (heta : 0 ≤ eta) (hcrop : 2*(buffer : ℝ) ≤ eta)
    {N : ℕ} (hN : 1 < (N : ℝ)) (E : ℕ × ℕ → Prop) {p : ℕ × ℕ}
    (hp : p ∈ currentChenUpsilon6RetainedSelector N E eta) :
    let slots := [(p.2,true),(p.1,true)]
    ¬ E p ∧ IntegerSquareGates N (rootSeed true buffer N p) 1 (slots.map Prod.fst) ∧
      IntegerSquareGates N (rootSeed true buffer N p)
        (selectedPrimes slots).prod (remainingPrimes slots) := by
  have hret := (mem_currentChenUpsilon6RetainedSelector_log_iff hN E eta p).mp hp
  have hdomain : pairPoint N p ∈ originalPairDomain true eta := by
    simpa [pairPoint,originalPairDomain,currentChenUpsilon6LogCoordinates,coordinate]
      using hret.2.2.2
  have hgates := original_integer_root_gates true buffer hb heta hcrop hN p
    (mem_chenAdditivePrimeCarrier.mp hret.1).2.1
    (mem_chenAdditivePrimeCarrier.mp hret.2.1).2.1 hdomain
  exact ⟨hret.2.2.1,hgates.1,hgates.2⟩

/-- The literal U5 small Rosser level fits the second buffer from its
    actual exponent allocation; L<=N^buffer is not assumed as a final bound. -/
theorem fifth_native_small_level_budget {N : ℕ} (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (buffer : ℚ)
    (halloc : P5OriginalU5CausalFinite.attachmentNu*epsilon ≤ (buffer : ℝ)) :
    P5OriginalU5CausalFinite.smallLevel N epsilon ≤ (N : ℝ)^(buffer : ℝ) := by
  exact Real.rpow_le_rpow_of_exponent_le hN.le halloc

end
end ImbalancedChen.P2OriginalPairBufferedRootProvenance
