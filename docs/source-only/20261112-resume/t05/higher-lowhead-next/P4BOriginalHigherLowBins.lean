import ImbalancedChen.P4BOriginalHigherLowRepresentative
import ImbalancedChen.P4BOriginalMediumTriplePowers
import ImbalancedChen.P1ActualHighWWholeBoxNativeRegroup

namespace ImbalancedChen.P4BOriginalHigherLowBins
noncomputable section
open Classical
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (ownerHead)
open P4BOriginalCollisionThirdFactor (splitAt)
open P4BOriginalHigherLowRootRows (Row)
open P4BOriginalHigherLowRepresentative (primeWord level atThird row front_eq t)
open P4AOriginalFiniteFallbackPhysicalSelected (head)
open P4AOriginalFiniteFallbackSelectedMask (front)
open P4BOriginalMediumTriplePowers (power)
open P4BUpperSelectedBoxCapacity (groups groups_partition)
open Part3.ActualWFineWordAdapter (fineSlots)
abbrev Groups := List ℕ × List ℕ × List ℕ

def selected (b : Row) (p : Fin 3→ℕ) : List ℕ := match b with
  | .first => [p 0] | .xy => [p 0,p 1] | .xyz => [p 0,p 1,p 2]
  | .xz => [p 0,p 2] | .yz => [p 1,p 2] | .rescue => []

def rest (b : Row) (p : Fin 3→ℕ) (xs : List ℕ) : List ℕ := match b with
  | .first => p 1::p 2::xs | .xy => p 2::xs | .xyz => xs
  | .xz => p 1::xs | .yz => p 0::xs | .rescue => front p xs

theorem perm (b : Row) (p : Fin 3→ℕ) (xs : List ℕ) :
    (selected b p++rest b p xs).Perm (front p xs) := by
  cases b <;> try exact List.Perm.refl _
  · exact (List.Perm.swap _ _ _).cons _
  · exact ((List.perm_append_comm (l₁:=[p 1,p 2]) (l₂:=[p 0])).append_right xs)

def cover (b : Row) (L e : ℝ) := L+(if b=.rescue then e else e/4)
def theta (N : ℕ) (x eta C : ℝ) := power x (N:ℝ)*C+2*eta

def bins (N : ℕ) (tau x U eta e L : ℝ) (b : Row) (J : List ℕ) : Groups :=
  let p := head J
  let xs := J.drop 3
  let A := U/x^eta
  let ell := cover b L e
  let v := theta N x eta ell
  if b=.rescue then
    let out := fineSlots N tau A (x^(2*v-1)) (x^(1-v-2*eta)/A) p xs
    (out.left,out.middle,out.right)
  else groups (x^(v-2*eta)) A (actualPrimeFineLabelIntegerUpper N tau)
    (selected b p) (rest b p xs) J

theorem bins_perm (N : ℕ) (tau x U eta e L : ℝ) (b : Row) (J : List ℕ) (hJ : 3≤J.length) :
    let S := bins N tau x U eta e L b J
    (S.1++(S.2.1++S.2.2)).Perm J := by
  unfold bins
  split_ifs
  · let v := theta N x eta (cover b L e)
    let out := fineSlots N tau (U/x^eta) (x^(2*v-1))
      (x^(1-v-2*eta)/(U/x^eta)) (head J) (J.drop 3)
    have h : (out.left++(out.middle++out.right)).Perm (front (head J) (J.drop 3)) := by
      simpa only [Part3.ActualWFineWordAdapter.flatten,List.append_assoc,front] using
        (P1ActualHighWWholeBoxNativeRegroup.fine_slots_perm N tau (U/x^eta) (x^(2*v-1))
          (x^(1-v-2*eta)/(U/x^eta)) (head J) (J.drop 3))
    rwa [front_eq J hJ] at h
  · apply groups_partition
    simpa only [front_eq J hJ] using perm b (head J) (J.drop 3)

def useRoot (P : Params) (J : List ℕ) : Prop :=
  4≤J.length ∧ t P J 0≤VariableEnvelope.mu ∧ atThird P J

/-- The new choice is made once for an original clipped label word, before
an HB tuple, residue test, or dyadic modulus owner is evaluated. -/
def split (P : Params) (x U eta : ℝ) (J : List ℕ) : Groups :=
  if useRoot P J then bins P.N P.T x U eta (P.e:ℝ) (level P J) (row P J) J
  else splitAt P x U eta J

theorem off_root (P : Params) (x U eta : ℝ) {J : List ℕ} (h : ¬useRoot P J) :
    split P x U eta J=splitAt P x U eta J := if_neg h

theorem split_perm (P : Params) (x U eta : ℝ) {J : List ℕ} (hJ : J∈P.words) :
    let S := split P x U eta J
    (S.1++(S.2.1++S.2.2)).Perm J := by
  unfold split
  split_ifs
  · exact bins_perm _ _ _ _ _ _ _ _ _ (Finset.mem_filter.mp hJ).2
  · exact P4AOriginalFiniteFallbackGroupedAtoms.partition _ _ _ _ _ _ _ _ _ _ (Finset.mem_filter.mp hJ).2

theorem four_used (P : Params) (hN : 1<P.N) (he : 0≤P.e) (ho : 0≤P.omega) {J}
    (hJ : J∈P.words) (h4 : J.length=4) (hlow : t P J 0≤VariableEnvelope.mu) : useRoot P J :=
  ⟨h4.ge,hlow,P4BOriginalHigherLowRepresentative.covered_of_last_le P hN ho hJ
    (P4BOriginalHigherLowRepresentative.four P hN he ho hJ h4 hlow).le⟩

end
end ImbalancedChen.P4BOriginalHigherLowBins
