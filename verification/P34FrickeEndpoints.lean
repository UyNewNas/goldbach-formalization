import ImbalancedChen.Part3AllLevelContinuedMaass
import ImbalancedChen.Part3LevelOldformFrickeIdentity

noncomputable section
open MeasureTheory Matrix
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.LevelOldformFricke20261026a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein

example (N : ℕ) : frickeMatrix N =
    !![0, -(1 / Real.sqrt (N : ℝ)); Real.sqrt (N : ℝ), 0] := rfl

example (N : ℕ) (hN : 0 < N) :
    Function.Involutive (fun z : UpperHalfPlane => frickeSL N hN • z) :=
  frickeSL_action_involutive N hN

example (N : ℕ) (hN : 0 < N) :
    MeasurePreserving (fun z : UpperHalfPlane => frickeSL N hN • z)
      (volume : Measure UpperHalfPlane) (volume : Measure UpperHalfPlane) :=
  frickeSL_measurePreserving N hN

example (N : ℕ) (hN : 0 < N) (z : UpperHalfPlane) :
    ((frickeSL N hN • z : UpperHalfPlane) : ℂ) = -1 / ((N : ℂ) * (z : ℂ)) :=
  fricke_action_coe N hN z

example (N : ℕ) (hN : 0 < N) (s : ℂ) (t : ℕ+ × ℂ)
    (ht : t ∈ oldformTerms (canonicalPrimeList N) s) : (t.1 : ℕ) ∣ N :=
  canonical_oldform_index_dvd N hN s t ht

example (N : ℕ) (hN : 0 < N) (n : ℕ+) (hn : (n : ℕ) ∣ N)
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (z : UpperHalfPlane) :
    completedActualEisenstein s (pnatDilate n (frickeSL N hN • z)) =
      completedActualEisenstein s (pnatDilate (complementaryIndex N hN n hn) z) :=
  completed_levelOne_fricke_integer N hN n hn s hs0 hs1 z

example (N : ℕ) (hN : 0 < N) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (z : UpperHalfPlane) :
    completedLevelOldform N s (frickeSL N hN • z) = reflectedCompletedLevel N hN s z :=
  completedLevelOldform_fricke N hN s hs0 hs1 z

example (N : ℕ) (hN : 0 < N) (z : UpperHalfPlane) :
    completedLevelOldform N (1 / 2) (frickeSL N hN • z) =
      reflectedCompletedLevel N hN (1 / 2) z :=
  completedLevelOldform_fricke_half N hN z

example (N : ℕ) (hN : 0 < N) (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    reflectedCompletedLevel N hN s z =
      completionFactor s * actualComplexParabolicEisenstein N s (frickeSL N hN • z) :=
  reflectedCompletedLevel_eq_actualParabolic N hN s hs z
