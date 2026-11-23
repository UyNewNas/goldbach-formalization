import ImbalancedChen.P2OriginalW2CountTupleReindex
import ImbalancedChen.Part5OriginalH430SelectedOrdinaryPairCounts
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairClassicalPorts

/-! The four actual good mother windows as masks of complete Wu labels.
The cutoffs of the counted objects are unchanged, including the moving
first prime in lanes seven and eight. The outer mask precedes BV. -/
namespace ImbalancedChen.P2OriginalWuGoodPairLabels
noncomputable section
open Finset Set Real Wu2008DoubleSieve
open Wu2008DoubleSieve.MotherPair
open P5OriginalActionMassBound P2W2PhysicalChildFeedback
open P2OriginalW2CountTupleReindex P2OriginalW2MotherOccurrenceReindex
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2FrozenReceiverCountActions (frozenCount frozenCarrier)
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430W2UpperPolygons (parameterQ physical original_parameters)
open scoped Classical BigOperators

def firstUpper (a : W2Parameters) (j : Fin 4) : ℝ := ![a2 a,a1 a,a1 a,a1 a] j
def secondLower (a : W2Parameters) (j : Fin 4) : ℝ := ![a0 a,a2 a,a0 a,a1 a] j
def secondUpper (a : W2Parameters) (j : Fin 4) : ℝ := ![a2 a,a3 a,a1 a,a2 a] j

def goodLabels {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (a : W2Parameters) (j : Fin 4) : Finset Gamma5ClassicalLabel :=
  (rectLabels N δ W (a0 a) (firstUpper a j) (secondLower a j) (secondUpper a j)).filter
    (fun x => PairGate ((N:ℝ)^(1/2-δ)) x.1 x.2.1 x.2.2)

def rawWindow (N : ℕ) (Q : ℝ) (d : ℕ) (a : W2Parameters) (j : Fin 4)
    (F : ℕ → ℕ → ℝ) : ℝ :=
  let R := Q/d
  ∑ p∈primeWindow N (R^(a0 a)) (R^(firstUpper a j)),
    ∑ q∈primeWindow N (R^(secondLower a j)) (R^(secondUpper a j)),
      if p<q ∧ PairGate Q d p q then F p q else 0

private theorem band_bounds {a : W2Parameters} (ha : W2Geometry a) (j : Fin 4) :
    firstUpper a j ≤ 1 ∧ secondUpper a j ≤ a3 a := by
  rcases ha with ⟨h0,h01,h12,h23,h3,_⟩
  fin_cases j <;> norm_num [firstUpper,secondUpper] <;> linarith

/-- This auxiliary cap belongs to the ordinary classical sieve. Every
original pair has second coordinate below it. -/
private theorem cap_bound (a : Fin 36) : a3 (originalW2At a) ≤ 49/100 := by
  rw [←original_parameters a]
  change 1/(parameterQ a 4:ℝ) ≤ 49/100
  fin_cases a <;> norm_num [parameterQ]

theorem goodLabels_subset_cap {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2≤N) (hδ : 0<δ) (hδhi : δ<1/2) (hb : wuSourceBox k δ N i Δ V)
    (a : Fin 36) (j : Fin 4) :
    goodLabels N δ (convolutionWuWindows N Δ V) (originalW2At a) j ⊆
      capLabels 5 (49/100) N δ (convolutionWuWindows N Δ V) := by
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem a)
  intro x hx
  have hx' := (mem_filter.mp hx).1
  obtain ⟨hprod,hp,hq,hpN,hqN,hpa,_,_,hqd,hpq⟩ := mem_filter.mp hx'
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb (mem_product.mp hprod).1).2.2.1
  exact mem_filter.mpr ⟨hprod,hp,hq,hpN,hqN,
    (rpow_le_rpow_of_exponent_le hR.le hg.1).trans hpa,hpq,
    hqd.trans_le (rpow_le_rpow_of_exponent_le hR.le
      ((band_bounds hg j).2.trans (cap_bound a)))⟩

theorem sum_labels {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2≤N) (hδ : 0<δ) (hδhi : δ<1/2) (hb : wuSourceBox k δ N i Δ V)
    {a : W2Parameters} (ha : W2Geometry a) (j : Fin 4) (F : ℕ → ℕ → ℕ → ℝ) :
    let W := convolutionWuWindows N Δ V
    let Q := (N:ℝ)^(1/2-δ)
    (∑ x∈goodLabels N δ W a j, (convolutionCoeff W x.1:ℝ)*F x.1 x.2.1 x.2.2) =
      ∑ d∈boxConvolutionSupport W, (convolutionCoeff W d:ℝ)*rawWindow N Q d a j (F d) := by
  dsimp only
  rw [goodLabels,sum_filter,rect_sum]
  · apply sum_congr rfl
    intro d _
    simp only [rawWindow,mul_sum]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    by_cases hpq : p<q <;> by_cases hgate : PairGate ((N:ℝ)^(1/2-δ)) d p q <;>
      simp [hpq,hgate]
  · exact fun d hd => cutoff_le_N hN hδ hδhi hb (band_bounds ha j).1 hd
  · exact fun d hd => cutoff_le_N hN hδ hδhi hb
      ((band_bounds ha j).2.trans (ha.2.2.2.2.1.trans (by norm_num))) hd

theorem rawWindow_eq_physical {N d : ℕ} {Q L : ℝ} (hd : 0<d) (hQ : Q=(d:ℝ)*(N:ℝ)^L)
    (a : W2Parameters) (j : Fin 4) (F : ℕ → ℕ → ℝ) :
    rawWindow N Q d a j F = windowOccurrence N Q L d a j F := by
  have hz (s : ℝ) : (Q/d)^(1/s) = (N:ℝ)^(L*(1/s)) := by
    change cutoff Q d s = _
    rw [cutoff_eq_physical_power hd hQ]
    congr 1
    ring
  fin_cases j <;>
    simp only [rawWindow,windowOccurrence,firstUpper,secondLower,secondUpper,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      a0,a1,a2,a3,hz]

theorem rawWindow_count (N : ℕ) (Q : ℝ) (d : ℕ) (a : W2Parameters) (j : Fin 4) :
    rawWindow N Q d a j
      (fun p q => (actualState N).upper (d*p*q) (occurrenceCutoff Q d a j p q)) =
      sourceGoodOccurrence N Q (actualState N) d a j := by
  fin_cases j <;>
    norm_num [rawWindow,firstUpper,secondLower,secondUpper,sourceGoodOccurrence,
      goodPairCount,occurrenceCutoff,cutoff,a0,a1,a2,a3]

theorem marked_count_le_fixed {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2≤N) (hδ : 0<δ) (hδhi : δ<1/2) (hb : wuSourceBox k δ N i Δ V)
    (a : Fin 36) (j : Fin 4) :
    let W := convolutionWuWindows N Δ V
    let Q := (N:ℝ)^(1/2-δ)
    (∑ d∈boxConvolutionSupport W,(convolutionCoeff W d:ℝ)*
      sourceGoodOccurrence N Q (actualState N) d (originalW2At a) j) ≤
      fixedCount 5 N δ W (goodLabels N δ W (originalW2At a) j) := by
  let P := originalW2At a
  let Q := (N:ℝ)^(1/2-δ)
  let W := convolutionWuWindows N Δ V
  let F (d p q : ℕ) := (actualState N).upper (d*p*q) (occurrenceCutoff Q d P j p q)
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem a)
  have hsum := sum_labels hN hδ hδhi hb hg j F
  dsimp only at hsum ⊢
  change (∑ x∈goodLabels N δ W P j,(convolutionCoeff W x.1:ℝ)*F x.1 x.2.1 x.2.2) =
    ∑ d∈boxConvolutionSupport W,(convolutionCoeff W d:ℝ)*rawWindow N Q d P j (F d) at hsum
  simp only [F,rawWindow_count] at hsum
  rw [←hsum]
  apply sum_le_sum
  intro x hx
  obtain ⟨d,p,q⟩ := x
  have hc := (mem_filter.mp (goodLabels_subset_cap hN hδ hδhi hb a j hx)).2
  obtain ⟨hp,hq,_,_,hzp,hpq,_⟩ := hc
  let z := wuLocalCutoff N δ d 5
  have hzq : z≤(q:ℝ) := hzp.trans (by exact_mod_cast hpq.le)
  have hd := (mem_product.mp (mem_filter.mp (mem_filter.mp hx).1).1).1
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
  have ha0 : z≤cutoff Q d P.s0 := rpow_le_rpow_of_exponent_le hR.le hg.1
  have hz : z≤occurrenceCutoff Q d P j p q := by
    unfold occurrenceCutoff
    split_ifs <;> assumption
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  change (frozenCount N (d*p*q) (P5OriginalU5FrozenSource.receiver N)
    (occurrenceCutoff Q d P j p q):ℝ) ≤ (sourceSieveCount N (d*p*q) (d*N) z:ℝ)
  rw [gamma5Classical_source_count_eq hp hq hzp hzq]
  apply le_trans _ (gamma5Classical_source_count_antitone N (d*p*q) ((d*p*q)*N) hz)
  simp only [frozenCount,frozenCarrier,Int.cast_natCast,sourceSieveCount]
  exact_mod_cast card_le_card (filter_subset _ _)

theorem marked_main_exact {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2≤N) (hδ : 0<δ) (hδhi : δ<1/2) (hb : wuSourceBox k δ N i Δ V)
    (a : Fin 36) (j : Fin 4) :
    let W := convolutionWuWindows N Δ V
    let Q := (N:ℝ)^(1/2-δ)
    gamma5ClassicalMainMass N δ W (goodLabels N δ W (originalW2At a) j) =
      ∑ d∈boxConvolutionSupport W,(convolutionCoeff W d:ℝ) *
        rawWindow N Q d (originalW2At a) j (fun p q => thetaAtom N Q (d*p*q)) := by
  dsimp only
  rw [←sum_labels hN hδ hδhi hb (originalRepairedW2Bank_geometry _ (originalW2At_mem a))]
  unfold gamma5ClassicalMainMass
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  unfold thetaAtom gamma5ClassicalProduct
  ring

end
end ImbalancedChen.P2OriginalWuGoodPairLabels
