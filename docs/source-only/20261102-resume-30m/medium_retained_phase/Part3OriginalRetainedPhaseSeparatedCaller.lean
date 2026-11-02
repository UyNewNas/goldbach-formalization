import ImbalancedChen.Part3OriginalRetainedPhaseOriginalScale
import ImbalancedChen.Part3OriginalReciprocalAbelCaller

/-!
SOURCE ONLY / NOT COMPILED / ZERO FORMAL CREDIT.
Literal coefficient-prefix -> original rectangle -> K separated source.
This dictionary explains precisely where the retained phase went: it is
already in the ONE weight5 variation, never silently removed from a row.
All original masks, n2 summation, 64 polarization labels, independent smooth
labels, signed product branches and signed f survive the K source theorem.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalQAbel
open ImbalancedChen.Part3.OriginalMediumAbelOneCoordinate
open ImbalancedChen.Part3.OriginalMediumPhysicalFiveAbelTower
open ImbalancedChen.Part3.OriginalMediumPhysicalShiftReindex
open ImbalancedChen.Part3.OriginalMediumOneTimeVariationTransfer
open ImbalancedChen.Part3.OriginalActualPoissonTightH20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalActualProductBoundDifferences20261028
open ImbalancedChen.Part3.OriginalReciprocalAbelCaller20261102
open ImbalancedChen.Part3.OriginalRetainedPhaseOriginalScale20261102
open ImbalancedChen.Part3.OriginalSourcePhysicalAbelCaller20261028

namespace ImbalancedChen.Part3.OriginalRetainedPhaseSeparatedCaller20261102
attribute [local instance] Classical.propDecidable

def anchoredRectangle (B : FixedBlock) (q w1 w2 n h : ℕ) : Rectangle where
  qLo := B.qLo
  qHi := B.qLo + q
  w1Lo := wBase B
  w1Hi := wBase B + w1
  w2Lo := wBase B
  w2Hi := wBase B + w2
  n1Lo := nBase B
  n1Hi := nBase B + n
  hLo := B.hLo
  hHi := B.hLo + (h : ℤ)

abbrev PrefixRaw := ℕ × (ℕ × (ℕ × (ℕ × (ℕ × ℕ))))

def prefixCarrier (B : FixedBlock) (q w1 w2 n h : ℕ) : Finset PrefixRaw :=
  (range (h+1)) ×ˢ ((range (n+1)) ×ˢ ((range (w2+1)) ×ˢ
    ((range (w1+1)) ×ˢ ((range (q+1)) ×ˢ B.nCarrier))))

def prefixPack (B : FixedBlock) (r : PrefixRaw) : Index :=
  rowIndex (B.qLo+r.2.2.2.2.1) (wBase B+r.2.2.2.1)
    (wBase B+r.2.2.1) (nBase B+r.2.1) r.2.2.2.2.2 (B.hLo+(r.1 : ℤ))

theorem prefixPack_injective (B : FixedBlock) : Function.Injective (prefixPack B) := by
  rintro ⟨h,n,w2,w1,q,n2⟩ ⟨h',n',w2',w1',q',n2'⟩ he
  simp only [prefixPack,rowIndex,Index.mk.injEq] at he
  have hh : h = h' := by omega
  have hn : n = n' := by omega
  have hw2 : w2 = w2' := by omega
  have hw1 : w1 = w1' := by omega
  have hq : q = q' := by omega
  have hn2 : n2 = n2' := he.2.2.2.2.1
  subst h'; subst n'; subst w2'; subst w1'; subst q'; subst n2'
  rfl

theorem prefixPack_mem_rectangle (B : FixedBlock) (q w1 w2 n h : ℕ)
    {r : PrefixRaw} (hr : r ∈ prefixCarrier B q w1 w2 n h) :
    (anchoredRectangle B q w1 w2 n h).contains (prefixPack B r) := by
  rcases r with ⟨ih,inn,iw2,iw1,iq,n2⟩
  simp only [prefixCarrier,mem_product,mem_range] at hr
  simp only [Rectangle.contains,anchoredRectangle,prefixPack,rowIndex,mem_Icc]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

theorem coeff5_eq_filtered_prefix (B : FixedBlock) (q w1 w2 n h : ℕ) :
    coeff5 B q w1 w2 n h =
      ∑ r ∈ (prefixCarrier B q w1 w2 n h).filter
        (fun r => prefixPack B r ∈ B.carrier), B.coeff (prefixPack B r) := by
  simp only [coeff5,coeff4,coeff3,coeff2,coeff1,
    prefixH,prefixN1,prefixW2,prefixW1,prefixQ,prefix,coeff0,rowCoeff,
    prefixCarrier,prefixPack,sum_filter,sum_product]

/-- The actual five-coordinate prefix, with n2 still full, is an
original anchored rectangle. There is no source identity premise. -/
theorem coeff5_eq_original_rectangle (B : FixedBlock) (q w1 w2 n h : ℕ) :
    coeff5 B q w1 w2 n h =
      B.rectangleSum (anchoredRectangle B q w1 w2 n h) := by
  rw [coeff5_eq_filtered_prefix]
  unfold FixedBlock.rectangleSum
  apply sum_bij (fun r _ => prefixPack B r)
  · intro r hr
    exact mem_filter.mpr ⟨(mem_filter.mp hr).2,
      prefixPack_mem_rectangle B q w1 w2 n h (mem_filter.mp hr).1⟩
  · intro r hr s hs he
    exact prefixPack_injective B he
  · intro t ht
    have htB := (mem_filter.mp ht).1
    have hR := (mem_filter.mp ht).2
    have hn2 := (carrier_members B htB).2.2.2.2.1
    simp only [Rectangle.contains,anchoredRectangle,mem_Icc] at hR
    let r : PrefixRaw := ((t.h-B.hLo).toNat,
      t.n1-nBase B, t.w2-wBase B, t.w1-wBase B, t.q-B.qLo, t.n2)
    have he : prefixPack B r = t := by
      cases t
      simp only [prefixPack,r,rowIndex,Index.mk.injEq]
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · rfl
      · omega
    refine ⟨r, mem_filter.mpr ⟨?_, by simpa only [he] using htB⟩, he⟩
    simp only [prefixCarrier,r,mem_product,mem_range]
    exact ⟨by omega, by omega, by omega, by omega, by omega, hn2⟩
  · intro r hr
    rfl

/-- Tightening the enclosing h interval did not alter the physical
coefficient or the actual carrier, so the same rectangle reaches K. -/
theorem tight_rectangle_eq_original
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (R : Rectangle) :
    (tightPoissonAtlasBlock atom z y k hA Csep j small hd negative).rectangleSum R =
      (poissonAtlasBlock atom z y k hA Csep j small hd negative).rectangleSum R := by
  unfold FixedBlock.rectangleSum
  rw [tightPoissonAtlasBlock_carrier]
  rfl

/-- Full source association after the once-only phase debit. The K
identity is invoked at precisely the rectangle forced by this prefix. -/
theorem tight_coeff5_eq_four_separated_sources
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (q w1 w2 n h : ℕ) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
    let R := anchoredRectangle T q w1 w2 n h
    coeff5 T q w1 w2 n h =
      upperSeparatedSource B atom z y k small R (upperProductBound k) (upperProductBound k) -
      upperSeparatedSource B atom z y k small R (lowerProductBound k) (upperProductBound k) -
      upperSeparatedSource B atom z y k small R (upperProductBound k) (lowerProductBound k) +
      upperSeparatedSource B atom z y k small R (lowerProductBound k) (lowerProductBound k) := by
  dsimp only
  rw [coeff5_eq_original_rectangle, tight_rectangle_eq_original]
  exact actual_rectangleSum_eq_four_separated_sources atom z y k hA Csep j small hd negative _

def fourAbelCharge (B : FixedBlock) (atom : MediumAtom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) : ℝ :=
  upperAbelCharge B atom z y k small R (upperProductBound k) (upperProductBound k) +
  upperAbelCharge B atom z y k small R (lowerProductBound k) (upperProductBound k) +
  upperAbelCharge B atom z y k small R (upperProductBound k) (lowerProductBound k) +
  upperAbelCharge B atom z y k small R (lowerProductBound k) (lowerProductBound k)

def separatedEnvelope (B T : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) : ℝ :=
  (insert 0 ((box T).image (fun r => fourAbelCharge B atom z y k small
    (anchoredRectangle T r.2.2.2.2 r.2.2.2.1 r.2.2.1 r.2.1 r.1)))).max'
      ⟨0, by simp⟩

theorem separatedEnvelope_nonneg (B T : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) :
    0 ≤ separatedEnvelope B T atom z y k small :=
  Finset.le_max' _ _ (by simp)

theorem tight_prefix_le_separatedEnvelope
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (r : Raw5)
    (hr : r ∈ box (tightPoissonAtlasBlock atom z y k hA Csep j small hd negative)) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
    ‖value (coeff5 T) r‖ ≤ separatedEnvelope B T atom z y k small := by
  dsimp only
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
  unfold value
  rw [coeff5_eq_original_rectangle, tight_rectangle_eq_original]
  apply (actual_rectangleSum_norm_le_four_Abel_charges atom z y k hA Csep j
    small hd negative (anchoredRectangle T r.2.2.2.2 r.2.2.2.1 r.2.2.1 r.2.1 r.1)).trans
  change fourAbelCharge B atom z y k small
    (anchoredRectangle T r.2.2.2.2 r.2.2.2.1 r.2.2.1 r.2.1 r.1) ≤
      separatedEnvelope B T atom z y k small
  apply Finset.le_max'
  exact mem_insert.mpr (Or.inr (mem_image.mpr ⟨r, hr, rfl⟩))

/-- Source-connected once-only debit through K: the retained phase costs
C*x^(5*kappa)*log(x)^25, and the exact separated prefix/outer energies
remain explicit. No uniform spectral or outer-energy estimate is assumed. -/
theorem actual_E3_le_separatedEnvelope_once
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (hκ : 0 ≤ κ) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
    ‖B.E3‖ ≤ separatedEnvelope B T atom z y k small *
      (retainedConstant * atom.scale ^ (5 * κ) * Real.log atom.scale ^ 25) := by
  dsimp only
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
  have hE := separatedEnvelope_nonneg B T atom z y k small
  have hx := admissible_scale_gt_one hA
  have hnonneg : 0 ≤ separatedEnvelope B T atom z y k small *
      (retainedConstant * atom.scale ^ (5*κ) * Real.log atom.scale ^ 25) := by
    exact mul_nonneg hE
      (mul_nonneg (mul_nonneg retainedConstant_nonneg
        (Real.rpow_nonneg (zero_le_one.trans hx.le) _))
        (pow_nonneg (Real.log_nonneg hx.le) _))
  by_cases ho : OrderedBox B
  · by_cases hH : 1 ≤ B.H
    · have hp := tightPoissonAtlasBlock_physicalBox atom z y k hA Csep j small hd negative ho hH
      rw [← tightPoissonAtlasBlock_E3 atom z y k hA Csep j small hd negative]
      exact (E3_le_prefix_times_variation T hp.toOrderedBox
        (separatedEnvelope B T atom z y k small) hE
        (tight_prefix_le_separatedEnvelope atom z y k hA Csep j small hd negative)).trans
          (mul_le_mul_of_nonneg_left
            (tight_variation_original_scale atom z y k hA hκ Csep j small hd negative ho hH) hE)
    · rw [E3_zero_of_H_lt_one B (lt_of_not_ge hH), norm_zero]
      exact hnonneg
  · rw [E3_zero_of_not_ordered B ho, norm_zero]
    exact hnonneg

theorem actual_E3_le_separatedEnvelope_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (b : ℕ) (σ κ c0 : ℝ) (atom : MediumAtom) (z y : ℝ) (k : Key)
      (hA : MediumAdmissible b σ κ c0 atom) (hκ : 0 ≤ κ) (Csep : ℕ)
      (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool),
      X ≤ atom.scale →
      let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
      let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
      ‖B.E3‖ ≤ separatedEnvelope B T atom z y k small *
        (retainedConstant * atom.scale ^ (5 * κ + ε)) := by
  obtain ⟨X,hX⟩ := Filter.eventually_atTop.mp (log25_eventually_le_rpow hε)
  refine ⟨X, ?_⟩
  intro b σ κ c0 atom z y k hA hκ Csep j small hd negative hxX
  dsimp only
  have hx : 0 < atom.scale := zero_lt_one.trans (admissible_scale_gt_one hA)
  apply (actual_E3_le_separatedEnvelope_once atom z y k hA hκ Csep j small hd negative).trans
  apply mul_le_mul_of_nonneg_left _ (separatedEnvelope_nonneg _ _ _ _ _ _ _)
  rw [Real.rpow_add hx]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hX atom.scale hxX)
    (mul_nonneg retainedConstant_nonneg (Real.rpow_nonneg hx.le _))

end ImbalancedChen.Part3.OriginalRetainedPhaseSeparatedCaller20261102
