import ImbalancedChen.Part3TwoLongActualHBShortMass
import ImbalancedChen.P5ActualLowerRetainedCubeModes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
An actual Cartesian reindex of the retained lower HB row, before norms.
The positions, real Mobius cutoff, signed short fibres, physical rho,
complete integer and exact coprime mean are unchanged. Selection of the
two long positions and rough-to-smooth restoration remain separate.
-/
namespace ImbalancedChen.Part3.TwoLongRetainedRowReindex
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
open TwoLongActualHBShortMass
open ImbalancedChen.P5Z.HBRightClosedDyadicRoles
open ImbalancedChen.P5Z.ActualHBDyadicProductWindow
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P5Z.ActualLowerNormalizedBlockGeometry
open ImbalancedChen.P5Z.ActualLowerNormalizedPostModulusTail
open ImbalancedChen.P5Z.ActualLowerRetainedCubeModes
open ImbalancedChen.P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open ImbalancedChen.P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b (phase)
open ImbalancedChen.PrimeProducts

variable {r : ℕ}

def complementBox (S : Fin r → Finset ℕ) (i j : Fin r) :
    Finset (ShortPositions i j → ℕ) :=
  Fintype.piFinset (fun a => S a.val)

def restrict (i j : Fin r) (n : Fin r → ℕ) : ShortPositions i j → ℕ :=
  fun a => n a.val

/-- The two chosen coordinates are positions, even when their values
coincide. No ordering by numerical value is introduced. -/
def assemble (i j : Fin r) (u v : ℕ) (s : ShortPositions i j → ℕ) : Fin r → ℕ :=
  fun a => if hi : a = i then u else if hj : a = j then v else s ⟨a, hi, hj⟩

@[simp] theorem assemble_left (i j : Fin r) (u v : ℕ) (s : ShortPositions i j → ℕ) :
    assemble i j u v s i = u := by simp [assemble]

@[simp] theorem assemble_right (i j : Fin r) (hij : i ≠ j)
    (u v : ℕ) (s : ShortPositions i j → ℕ) :
    assemble i j u v s j = v := by simp [assemble, hij.symm]

@[simp] theorem restrict_assemble (i j : Fin r) (u v : ℕ)
    (s : ShortPositions i j → ℕ) : restrict i j (assemble i j u v s) = s := by
  funext a
  simp [restrict, assemble, a.property.1, a.property.2]

theorem assemble_restrict (i j : Fin r) (n : Fin r → ℕ) :
    assemble i j (n i) (n j) (restrict i j n) = n := by
  funext a
  by_cases hi : a = i
  · subst a; simp
  · by_cases hj : a = j
    · subst a; simp [assemble, hi]
    · simp [assemble, restrict, hi, hj]

theorem assemble_mem (S : Fin r → Finset ℕ) (i j : Fin r)
    {u v : ℕ} {s : ShortPositions i j → ℕ}
    (hu : u ∈ S i) (hv : v ∈ S j) (hs : s ∈ complementBox S i j) :
    assemble i j u v s ∈ Fintype.piFinset S := by
  apply Fintype.mem_piFinset.mpr
  intro a
  by_cases hi : a = i
  · subst a; simpa using hu
  · by_cases hj : a = j
    · subst a; simpa [assemble, hi] using hv
    · simpa [assemble, hi, hj] using
        Fintype.mem_piFinset.mp hs (⟨a, hi, hj⟩ : ShortPositions i j)

/-- Full finite bijection, not an equality supplied by the caller.
It applies equally to unit/right-closed HB blocks and to smooth covers. -/
theorem sum_two_positions (S : Fin r → Finset ℕ) (i j : Fin r) (hij : i ≠ j)
    (F : (Fin r → ℕ) → ℂ) :
    (∑ n ∈ Fintype.piFinset S, F n) =
      ∑ u ∈ S i, ∑ v ∈ S j, ∑ s ∈ complementBox S i j,
        F (assemble i j u v s) := by
  calc
    _ = ∑ t ∈ (S i ×ˢ S j) ×ˢ complementBox S i j,
        F (assemble i j t.1.1 t.1.2 t.2) := by
      refine Finset.sum_bij (fun n _ => ((n i, n j), restrict i j n)) ?_ ?_ ?_ ?_
      · intro n hn
        refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨Fintype.mem_piFinset.mp hn i, Fintype.mem_piFinset.mp hn j⟩, ?_⟩
        exact Fintype.mem_piFinset.mpr (fun a => Fintype.mem_piFinset.mp hn a.val)
      · intro n hn n' hn' he
        have hi := congrArg (fun t : (ℕ × ℕ) × (ShortPositions i j → ℕ) => t.1.1) he
        have hj := congrArg (fun t : (ℕ × ℕ) × (ShortPositions i j → ℕ) => t.1.2) he
        have hs := congrArg (fun t : (ℕ × ℕ) × (ShortPositions i j → ℕ) => t.2) he
        calc
          n = assemble i j (n i) (n j) (restrict i j n) := (assemble_restrict i j n).symm
          _ = assemble i j (n' i) (n' j) (restrict i j n') := by rw [hi, hj, hs]
          _ = n' := assemble_restrict i j n'
      · intro t ht
        obtain ⟨huv, hs⟩ := Finset.mem_product.mp ht
        obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
        refine ⟨assemble i j t.1.1 t.1.2 t.2, assemble_mem S i j hu hv hs, ?_⟩
        simp [assemble_right i j hij]
      · intro n hn
        rw [assemble_restrict]
    _ = _ := by simp only [Finset.sum_product]

def longWeight (b : Block) (Z y t : ℝ) (role : Role) (u : ℕ) : ℂ :=
  actual Z y role u * phase t ((u : ℝ) / lower b)

/-- The whole ordered rectangle is pushed forward only in the SHORT
product. All collisions are summed with their original complex signs. -/
theorem rectangle_signed_pushforward (bs : Fin r → Block) (Z : ℝ)
    (y xi : Fin r → ℝ) (rs : Fin r → Role) (i j : Fin r) (hij : i ≠ j)
    (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ n ∈ rectangle bs, shortWeight bs Z y xi rs n *
      F (shortProduct (restrict i j n)) (n i) (n j)) =
      ∑ m ∈ shortSupport (fun a : ShortPositions i j => bs a.val),
        shortSequence (fun a : ShortPositions i j => bs a.val) Z
          (fun a => y a.val) (fun a => xi a.val) (fun a => rs a.val) m *
        ∑ u ∈ blockIntegers (bs i), ∑ v ∈ blockIntegers (bs j),
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v * F m u v := by
  let W := shortWeight (fun a : ShortPositions i j => bs a.val) Z
    (fun a => y a.val) (fun a => xi a.val) (fun a => rs a.val)
  let C := shortRectangle (fun a : ShortPositions i j => bs a.val)
  calc
    _ = ∑ u ∈ blockIntegers (bs i), ∑ v ∈ blockIntegers (bs j), ∑ s ∈ C,
        W s * (longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v * F (shortProduct s) u v) := by
      rw [rectangle, sum_two_positions _ i j hij]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro s hs
      rw [shortWeight_split bs Z y xi rs _ i j hij]
      simp only [assemble_left, assemble_right i j hij]
      change _ * shortWeight _ _ _ _ _ (restrict i j (assemble i j u v s)) *
        F (shortProduct (restrict i j (assemble i j u v s))) u v = _
      rw [restrict_assemble]
      dsimp [W, longWeight]
      ring
    _ = ∑ u ∈ blockIntegers (bs i), ∑ s ∈ C, ∑ v ∈ blockIntegers (bs j),
        W s * (longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v * F (shortProduct s) u v) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ s ∈ C, W s *
        ∑ u ∈ blockIntegers (bs i), ∑ v ∈ blockIntegers (bs j),
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v * F (shortProduct s) u v := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := (shortSequence_pushforward _ Z _ _ _ _).symm

def roughFibreCore (bs : Fin r → Block) (Z : ℝ) (y xi : Fin r → ℝ)
    (rs : Fin r → Role) (i j : Fin r) (m N q : ℕ) : ℂ :=
  ∑ u ∈ blockIntegers (bs i), ∑ v ∈ blockIntegers (bs j),
    longWeight (bs i) Z (y i) (xi i) (rs i) u *
    longWeight (bs j) Z (y j) (xi j) (rs j) v *
      MellinInsertion20261028.residueKernel q N (m*u*v)

/-- Literal retained arithmetic mode, with the production lower Q/rho.
No estimate, source identity, or P2 hypothesis is used in its reindex. -/
theorem retained_mode_eq_fibres (bs : Fin r → Block) (Z : ℝ)
    (y xi : Fin r → ℝ) (rs : Fin r → Role) (i j : Fin r) (hij : i ≠ j)
    (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    MellinInsertion20261028.exactDiscrepancy (rectangle bs)
      (lowerQ policy N cap w z) (lowerRho policy N cap w z L) completeProduct N
      (fun n => hbSlots Z y rs n * occurrenceMode (scales bs) n xi) =
      ∑ m ∈ shortSupport (fun a : ShortPositions i j => bs a.val),
        shortSequence (fun a : ShortPositions i j => bs a.val) Z
          (fun a => y a.val) (fun a => xi a.val) (fun a => rs a.val) m *
        ∑ q ∈ lowerQ policy N cap w z, lowerRho policy N cap w z L q *
          roughFibreCore bs Z y xi rs i j m N q := by
  simp_rw [retained_tensor_eq_shortWeight]
  unfold MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
  have hp (n : Fin r → ℕ) : completeProduct n = shortProduct (restrict i j n) * n i * n j := by
    rw [completeProduct, product_two_positions i j hij]
    dsimp [shortProduct, restrict]
    ring
  simp_rw [hp]
  rw [rectangle_signed_pushforward bs Z y xi rs i j hij]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  calc
    _ = ∑ u ∈ blockIntegers (bs i), ∑ v ∈ blockIntegers (bs j),
        ∑ q ∈ lowerQ policy N cap w z,
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v *
          (lowerRho policy N cap w z L q *
            MellinInsertion20261028.residueKernel q N (m*u*v)) := by
      simp only [Finset.mul_sum]
    _ = ∑ u ∈ blockIntegers (bs i), ∑ q ∈ lowerQ policy N cap w z,
        ∑ v ∈ blockIntegers (bs j),
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v *
          (lowerRho policy N cap w z L q *
            MellinInsertion20261028.residueKernel q N (m*u*v)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ q ∈ lowerQ policy N cap w z, ∑ u ∈ blockIntegers (bs i),
        ∑ v ∈ blockIntegers (bs j),
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v *
          (lowerRho policy N cap w z L q *
            MellinInsertion20261028.residueKernel q N (m*u*v)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      unfold roughFibreCore
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      ring

/-- The exact integer modulus support is the occupied support, with no
claim about the size of its inactive members. This is the support used by
J's moment theorem, not a different rho or a JOINT coefficient. -/
theorem lower_sum_eq_occupied (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (F : ℕ → ℂ) :
    (∑ q ∈ lowerQ policy N cap w z, lowerRho policy N cap w z L q * F q) =
      ∑ q ∈ (lowerQ policy N cap w z).filter
        (fun q => lowerRho policy N cap w z L q ≠ 0),
        lowerRho policy N cap w z L q * F q := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq hnot
  have hz : lowerRho policy N cap w z L q = 0 := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hq, hn⟩)
  simp [hz]

/-- A selected block above the REAL Mobius cutoff cannot carry an
active Mobius occurrence. This supplies the role exclusion locally;
finding the long positions from the no-medium geometry remains open. -/
theorem long_role_of_active_tuple (bs : Fin r → Block) (Z : ℝ)
    (y xi : Fin r → ℝ) (rs : Fin r → Role) {n : Fin r → ℕ}
    (hn : n ∈ rectangle bs) (hweight : shortWeight bs Z y xi rs n ≠ 0)
    (a : Fin r) (hlarge : y a < (lower (bs a) : ℝ)) :
    rs a = .one ∨ rs a = .logarithm := by
  have hfactor : actual Z (y a) (rs a) (n a) *
      phase (xi a) ((n a : ℝ)/lower (bs a)) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hweight) a (Finset.mem_univ a)
  have hlo : (lower (bs a) : ℝ) ≤ n a := (rectangle_bounds bs hn a).2.1
  have hcut : ¬(n a : ℝ) ≤ y a := not_le.mpr (hlarge.trans_le hlo)
  cases hrole : rs a with
  | mobius => simp [hrole, actual, roughMuTrunc, hcut] at hfactor
  | one => exact Or.inl rfl
  | logarithm => exact Or.inr rfl

/-- This is the actual I retained literal row, including its original
HB binomial sign and normalized Fourier amplitude. Whole-group inverse
logs stay in amplitude; they are not moved into alpha or the long slots. -/
theorem retained_literal_row_eq_fibres (kappa : ℝ) (B N cj h : ℕ) (kappa0 : ℝ)
    (bs : Fin (2*(h+1)) → Block) (i j : Fin (2*(h+1))) (hij : i ≠ j)
    (policy : List ℕ → Bool) (cap : ℕ) (w z L H : ℝ) :
    retainedLiteralRow kappa B N cj h kappa0 bs policy cap w z L H =
      ImbalancedChen.P5Z.SmoothChartHBDyadicPartition.scalar h *
      ∫ xi in (ImbalancedChen.P5Z.AllRankCauchyCubeTail.outsideCube (2*(h+1)) H)ᶜ,
        amplitude kappa B N cj kappa0 bs xi *
        ∑ m ∈ shortSupport (fun a : ShortPositions i j => bs a.val),
          shortSequence (fun a : ShortPositions i j => bs a.val)
            (ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition.beforeHBCutoff 1 [cj])
            (fun _ => ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward.hbCutoff cj)
            (fun a => xi a.val) (fun a => rowRoles h a.val) m *
          ∑ q ∈ lowerQ policy N cap w z, lowerRho policy N cap w z L q *
            roughFibreCore bs
              (ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition.beforeHBCutoff 1 [cj])
              (fun _ => ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward.hbCutoff cj)
              xi (rowRoles h) i j m N q := by
  rw [retainedLiteralRow, retainedAtom_eq_modes]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun xi => by
    rw [retained_mode_eq_fibres bs _ _ xi _ i j hij])

end
end ImbalancedChen.Part3.TwoLongRetainedRowReindex
