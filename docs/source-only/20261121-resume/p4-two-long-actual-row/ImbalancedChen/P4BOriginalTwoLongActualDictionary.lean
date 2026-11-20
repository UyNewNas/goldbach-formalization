import ImbalancedChen.P4BOriginalNoMediumPairRows
import ImbalancedChen.Part3TwoLongLiteralBrunSubstitution
import ImbalancedChen.P4BOriginalTwoLongExpandedCore

/-! SOURCE ONLY / UNCOMPILED. Generic finite source identities specialized
only at the outer boundary to the true P4 coefficient. No lowerQ/lowerRho
wrapper is used. This file does not equate a rough row with its Brun
polynomial; the two displayed identities have distinct literal sources. -/
namespace ImbalancedChen.P4BOriginalTwoLongActualDictionary
noncomputable section
open Classical
open scoped BigOperators
open PrimeProducts
open Part3.TwoLongActualHBShortMass
open Part3.TwoLongRetainedRowReindex
open Part3.TwoLongLiteralBrunSubstitution
open Part3.TwoLongHBMellinBrunProfiles
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle scales blockIntegers)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)

variable {r : ℕ}
theorem same_rho_mode_eq_fibres (bs : Fin r → Block) (Z : ℝ)
    (y xi : Fin r → ℝ) (rs : Fin r → Role) (i j : Fin r) (hij : i ≠ j)
    (N : ℕ) (S : Finset ℕ) (rho : ℕ → ℂ) :
    MellinInsertion20261028.exactDiscrepancy (rectangle bs)
      S rho completeProduct N
      (fun n => hbSlots Z y rs n * occurrenceMode (scales bs) n xi) =
      ∑ m ∈ shortSupport (fun a : ShortPositions i j => bs a.val),
        shortSequence (fun a : ShortPositions i j => bs a.val) Z
          (fun a => y a.val) (fun a => xi a.val) (fun a => rs a.val) m *
        ∑ q ∈ S, rho q *
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
        ∑ q ∈ S,
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v *
          (rho q *
            MellinInsertion20261028.residueKernel q N (m*u*v)) := by
      simp only [Finset.mul_sum]
    _ = ∑ u ∈ blockIntegers (bs i), ∑ q ∈ S,
        ∑ v ∈ blockIntegers (bs j),
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v *
          (rho q *
            MellinInsertion20261028.residueKernel q N (m*u*v)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ q ∈ S, ∑ u ∈ blockIntegers (bs i),
        ∑ v ∈ blockIntegers (bs j),
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v *
          (rho q *
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

/-- The exact rough mode from the two original Fin.append mothers.
The finite carriers and scales agree definitionally with the reusable
generic rectangle identity; the physical Q and signed coefficient do not. -/
theorem actual_pair_mode {j l : ℕ} (cj ck : ℕ)
    (bs : Fin (2*(j+1))→Block) (cs : Fin (2*(l+1))→Block)
    (Z : ℝ) (xi : Fin (2*(j+1)+2*(l+1))→ℝ)
    (i k : Fin (2*(j+1)+2*(l+1))) (hik : i≠k)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (index N : ℕ) (L : ℝ) (S : Finset ℕ) :
    MellinInsertion20261028.exactDiscrepancy
      (P5Z.OrderedFactorTupleRectangleReindex.rectangle (Fin.append bs cs)) S
      (P4BOriginalTwoLongExpandedCore.rho m r n e q a omega index N L) completeProduct N
      (fun y => hbSlots Z
        (Fin.append (fun _ => P5Z.PerGroupIntegerHBAtlasPushforward.hbCutoff cj)
          (fun _ => P5Z.PerGroupIntegerHBAtlasPushforward.hbCutoff ck))
        (Fin.append (P4BUpperPairOrderedRowGeometry.rowRoles j)
          (P4BUpperPairOrderedRowGeometry.rowRoles l)) y *
        occurrenceMode (P4BUpperPairOrderedRowGeometry.blockScales (Fin.append bs cs)) y xi) =
      ∑ short ∈ shortSupport (fun t : ShortPositions i k => Fin.append bs cs t.val),
        shortSequence (fun t : ShortPositions i k => Fin.append bs cs t.val) Z
          (fun t => Fin.append (fun _ => P5Z.PerGroupIntegerHBAtlasPushforward.hbCutoff cj)
            (fun _ => P5Z.PerGroupIntegerHBAtlasPushforward.hbCutoff ck) t.val)
          (fun t => xi t.val)
          (fun t => Fin.append (P4BUpperPairOrderedRowGeometry.rowRoles j)
            (P4BUpperPairOrderedRowGeometry.rowRoles l) t.val) short *
          ∑ v ∈ S,P4BOriginalTwoLongExpandedCore.rho m r n e q a omega index N L v *
            roughFibreCore (Fin.append bs cs) Z
              (Fin.append (fun _ => P5Z.PerGroupIntegerHBAtlasPushforward.hbCutoff cj)
                (fun _ => P5Z.PerGroupIntegerHBAtlasPushforward.hbCutoff ck)) xi
              (Fin.append (P4BUpperPairOrderedRowGeometry.rowRoles j)
                (P4BUpperPairOrderedRowGeometry.rowRoles l)) i k short N v := by
  exact same_rho_mode_eq_fibres (Fin.append bs cs) Z _ xi _ i k hik N S _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Literal long-integer Brun-polynomial source, with the original short
ordered fibre and actual final P4 rho. This is not defined as a P2 bound. -/
def polynomialRow (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (index N : ℕ)
    (L Z : ℝ) (S : Finset ℕ) (h : ℕ) (b1 b2 : Bool) (delta U V t1 t2 : ℝ)
    (label : Fin 3) (log1 log2 : Bool) (bs : ι→Block) (ys xi : ι→ℝ) (rs : ι→Role) : ℂ :=
  ∑ v ∈ S,P4BOriginalTwoLongExpandedCore.rho m r n e q a omega index N L v *
    ∑ short ∈ shortSupport bs,
      smoothBrunTupleCore Z h b1 b2 delta U V t1 t2 label log1 log2
        (shortSequence bs Z ys xi rs short) short N v

/-- Reuse the proved exact divisor substitution at each original v.
Both signed outer sums are only interchanged; no norm or rough/Brun
identification enters this equality. -/
theorem polynomialRow_eq_core (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (index N : ℕ) (L : ℝ) (S : Finset ℕ) {Z delta U V : ℝ}
    (hZ : 1≤Z) (hd : 0<delta) (hs : delta≤1/4) (hU : 0<U) (hV : 0<V)
    (h : ℕ) (b1 b2 : Bool) (t1 t2 : ℝ) (label : Fin 3) (log1 log2 : Bool)
    (bs : ι→Block) (ys xi : ι→ℝ) (rs : ι→Role) :
    polynomialRow m r n e q a omega index N L Z S h b1 b2 delta U V t1 t2
      label log1 log2 bs ys xi rs =
    P4BOriginalTwoLongExpandedCore.rowCore m r n e q a omega index N L Z S h b1 b2
      delta U V t1 t2 label log1 log2 bs ys xi rs := by
  unfold polynomialRow P4BOriginalTwoLongExpandedCore.rowCore P4BOriginalTwoLongExpandedCore.brunCore
  simp_rw [smoothBrunTupleCore_eq_expansion hZ hd hs hU hV]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

end
end ImbalancedChen.P4BOriginalTwoLongActualDictionary

