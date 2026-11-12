import ImbalancedChen.P2AllW1FrozenReceiverFiniteAction
import ImbalancedChen.P2EnhancedTwentyOneQuotientFinite

/-! The four-band weight holds for each additive-prime label before summation.
Keep its signed part on that label. Only nonnegative labelled incidences
may be enlarged to the full mother source. -/
namespace ImbalancedChen.Part5OriginalH430ReceiptFourBand

noncomputable section
open Finset Wu2008DoubleSieve
open P2FrozenReceiverCountActions
open P2AllW1FrozenReceiverFiniteAction (negative_child_eq_frozen)
open P2EnhancedTwentyOneQuotientFinite
open scoped Classical BigOperators

abbrev count (N d : ℕ) (E : ℕ → Prop) (z : ℝ) : ℝ := (frozenCount N d E z : ℝ)

def maskedSingle (N d : ℕ) (E : ℕ → Prop) (a u : ℝ) : ℝ :=
  ∑ q ∈ primeWindow (d*N) a u, count N (d*q) E a

def positiveLabels (s : Finset ℕ) (χ : ℕ → ℕ) : ℝ :=
  ((fourthRowMotherLowPairs s χ).card : ℝ) + ((fourthRowMotherCrossPairs s χ).card : ℝ) +
    (secondFunctionalMotherPrefixIndices.map fun i => (secondFunctionalMotherGammaLabels s χ i : ℝ)).sum

def positiveMass (N d : ℕ) (E : ℕ → Prop) (a b c e f : ℝ) : ℝ :=
  ∑ ell ∈ (sieveCarrier N d (d*N) a).filter E,
    positiveLabels (divisorsIn (primeWindow (d*N) a f) ((N-ell)/d))
      (secondFunctionalMotherColour b c e)

theorem count_card (N d : ℕ) (E : ℕ → Prop) (a : ℝ) :
    count N d E a = (((sieveCarrier N d (d*N) a).filter E).card : ℝ) := by
  simp only [count,frozenCount,frozenCarrier,(source_double_sieve_carriers N d a).1,Int.cast_natCast]

theorem count_mono {E F : ℕ → Prop} (h : ∀ ell, E ell → F ell) (N d : ℕ) (z : ℝ) :
    count N d E z ≤ count N d F z := by
  rw [count_card,count_card]
  have hi : (sieveCarrier N d (d*N) z).filter E ⊆ (sieveCarrier N d (d*N) z).filter F :=
    fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,h x (mem_filter.mp hx).2⟩
  exact_mod_cast card_le_card hi

theorem count_cutoff_antitone (N d : ℕ) (E : ℕ → Prop) {a f : ℝ} (haf : a ≤ f) :
    count N d E f ≤ count N d E a := by
  rw [count_card,count_card,← siftedIndices_sieveCarrier N d (d*N) haf]
  exact_mod_cast card_le_card (show
    (siftedIndices (sieveCarrier N d (d*N) a) (fun ell => (N-ell)/d)
      (primeWindow (d*N) a f)).filter E ⊆ (sieveCarrier N d (d*N) a).filter E
    from fun x hx => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hx).1).1,(mem_filter.mp hx).2⟩)

theorem masked_cutoff (N d : ℕ) (E : ℕ → Prop) {a u : ℝ} (hau : a ≤ u) :
    count N d E u = ∑ ell ∈ (sieveCarrier N d (d*N) a).filter E,
      if divisorsIn (primeWindow (d*N) a u) ((N-ell)/d) = ∅ then (1:ℝ) else 0 := by
  rw [count_card,sum_boole,← siftedIndices_sieveCarrier N d (d*N) hau]
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  ext ell
  simp only [siftedIndices,mem_filter]
  tauto

theorem masked_single_mass (N d : ℕ) (E : ℕ → Prop) (a u : ℝ) :
    maskedSingle N d E a u = ∑ ell ∈ (sieveCarrier N d (d*N) a).filter E,
      ((divisorsIn (primeWindow (d*N) a u) ((N-ell)/d)).card : ℝ) := by
  unfold maskedSingle
  simp only [divisorsIn,← sum_boole]
  rw [sum_comm (s := (sieveCarrier N d (d*N) a).filter E)]
  apply sum_congr rfl
  intro q hq
  obtain ⟨hprime,_,hz,_⟩ := mem_primeWindow.mp hq
  rw [sum_boole]
  change (frozenCount N (d*q) E a : ℝ) = _
  rw [← negative_child_eq_frozen N d E hprime hz]
  simp only [quotientCount,Int.cast_natCast]
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  rw [← singleCarrier_eq N d (d*N) hprime hz]
  ext ell
  simp only [mem_filter]
  tauto

/-- The same arbitrary mask at BOTH anchors, all three negative singleton
windows and every positive incidence. The hard inequality is applied at
each ell. An unmasked aggregate inequality could not justify this step. -/
theorem masked_mother (N d : ℕ) (E : ℕ → Prop) {a b c e f : ℝ}
    (hab : a≤b) (hbc : b≤c) (hce : c≤e) (hef : e≤f) :
    5*count N d E f ≤ 4*count N d E a + count N d E b -
      maskedSingle N d E a f - maskedSingle N d E a c - maskedSingle N d E a e +
      positiveMass N d E a b c e f := by
  let A := (sieveCarrier N d (d*N) a).filter E
  let s := fun ell : ℕ => divisorsIn (primeWindow (d*N) a f) ((N-ell)/d)
  let χ := secondFunctionalMotherColour b c e
  have hw : 5*count N d E f ≤ ∑ ell ∈ A, secondFunctionalMotherLabelWeight (s ell) χ := by
    rw [masked_cutoff N d E (hab.trans (hbc.trans (hce.trans hef))),mul_sum]
    apply sum_le_sum
    intro ell _
    simpa only [mul_ite,mul_one,mul_zero] using secondFunctionalMother_label_weight
      (s ell) χ (secondFunctionalMother_colour_monotone b c e)
      (fun q _ => secondFunctionalMother_colour_le_three b c e q)
  have he (ell : ℕ) : secondFunctionalMotherLabelWeight (s ell) χ =
      4 + (if divisorsIn (primeWindow (d*N) a b) ((N-ell)/d) = ∅ then (1:ℝ) else 0) -
      ((s ell).card : ℝ) - ((divisorsIn (primeWindow (d*N) a c) ((N-ell)/d)).card : ℝ) -
      ((divisorsIn (primeWindow (d*N) a e) ((N-ell)/d)).card : ℝ) + positiveLabels (s ell) χ := by
    simp only [s,χ,positiveLabels,secondFunctionalMotherLabelWeight,
      secondFunctionalMother_band_zero _ _ (hbc.trans (hce.trans hef)),
      secondFunctionalMother_band_low _ _ hbc (hce.trans hef),
      secondFunctionalMother_band_mid _ _ hbc hce hef]
    ring
  simp_rw [he] at hw
  simp only [sum_add_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul] at hw
  rw [masked_cutoff N d E hab,masked_single_mass,masked_single_mass,masked_single_mass,
    count_card N d E a]
  unfold positiveMass
  dsimp only [A,s,χ] at hw
  linarith

theorem positiveLabels_nonneg (s : Finset ℕ) (χ : ℕ → ℕ) : 0 ≤ positiveLabels s χ := by
  have hh : 0 ≤ (secondFunctionalMotherPrefixIndices.map fun i =>
      (secondFunctionalMotherGammaLabels s χ i : ℝ)).sum := by
    apply List.sum_nonneg
    intro y hy
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hy
    exact Nat.cast_nonneg _
  unfold positiveLabels
  positivity

theorem positiveMass_mono {E F : ℕ → Prop} (h : ∀ ell, E ell → F ell)
    (N d : ℕ) (a b c e f : ℝ) :
    positiveMass N d E a b c e f ≤ positiveMass N d F a b c e f := by
  unfold positiveMass
  apply sum_le_sum_of_subset_of_nonneg
    (show _ ⊆ _ from fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,h x (mem_filter.mp hx).2⟩)
  exact fun _ _ _ => positiveLabels_nonneg _ _

/-- Ordinary positive sources on the original N-windows. Each occurrence of
the 22 words is retained. The switched-mask cost remains in the last term. -/
theorem positiveMass_le_original (N d : ℕ) (E : ℕ → Prop) {a b c e f : ℝ}
    (hab : a≤b) (hbc : b≤c) (hce : c≤e) (hef : e≤f) :
    positiveMass N d E a b c e f ≤
      fourthRowMotherPair N d N a c a c + fourthRowMotherPair N d N a b c e +
      quotientSwitched N d N a b c e f + collisionSwitched N d N a b c e f := by
  have hw := (positiveMass_mono (E:=E) (F:=fun _ => True) (fun _ _ => trivial) N d a b c e f)
  have hid (A : Finset ℕ) : A.filter (fun _ => True) = A :=
    filter_eq_self.mpr (fun _ _ => trivial)
  simp only [positiveMass,hid,positiveLabels,sum_add_distrib] at hw
  rw [← secondFunctionalMother_gamma5_mass N d hbc (hce.trans hef),
    ← secondFunctionalMother_gamma6_mass N d hab hbc hce hef] at hw
  have h5 := fourthRowMother_pair_mono N d a c a c
  have h6 := fourthRowMother_pair_mono N d a b c e
  have hpack := secondFunctionalMother_package_mass_le N d a b c e f
    secondFunctionalMotherPrefixIndices secondFunctionalMother_prefix_lengths
  have hwin := secondFunctionalMother_list_sum_mono secondFunctionalMotherPrefixIndices
    (fun i => ((secondFunctionalMotherGammaWords i).map
      (secondFunctionalMotherPrefixTerm N d (d*N) a b c e f)).sum)
    (fun i => ((secondFunctionalMotherGammaWords i).map
      (secondFunctionalMotherPrefixTerm N d N a b c e f)).sum)
    (fun i _ => secondFunctionalMother_list_sum_mono (secondFunctionalMotherGammaWords i)
      _ _ (fun cs _ => secondFunctionalMother_prefix_mono N d a b c e f cs))
  have hsw := switched_le_quotient_add_collision N d N a b c e f
  unfold positiveMass positiveLabels
  simp only [sum_add_distrib]
  linarith

end
end ImbalancedChen.Part5OriginalH430ReceiptFourBand
