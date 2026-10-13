import ImbalancedChen.HistoricalPrefixCertificate
import ImbalancedChen.StoredHistoricalBoxPermit
set_option warningAsError true

/-! Bridge: whole-cell stored cap checks imply historical inherited levels. -/
namespace ImbalancedChen
noncomputable section
namespace HistoricalPrefixCapData

theorem levelCheck_of_storedMeshCapChecks
    (D : HistoricalPrefixCapData)
    (I3 : (Fin 3 → Fin (D.m + 1)) → Finset (Fin 3))
    (I4 : (Fin 4 → Fin (D.m + 1)) → Finset (Fin 4))
    (I5 : (Fin 5 → Fin (D.m + 1)) → Finset (Fin 5))
    (nu3 : (Fin 3 → Fin (D.m + 1)) → ℚ)
    (nu4 : (Fin 4 → Fin (D.m + 1)) → ℚ)
    (nu5 : (Fin 5 → Fin (D.m + 1)) → ℚ)
    (h3 : storedMeshCapCheck D.a D.b D.m D.cells3 I3
      (fun _ => D.old) nu3 D.cap3 = true)
    (h4 : storedMeshCapCheck D.a D.b D.m D.cells4 I4 D.old4 nu4 D.cap4 = true)
    (h5 : storedMeshCapCheck D.a D.b D.m D.cells5 I5 D.old5 nu5 D.cap5 = true) :
    D.levelCheck = true := by
  have h3lt : ∀ j ∈ D.cells3, D.old < D.cap3 j :=
    storedMeshCapCheck_old_lt D.a D.b D.m D.cells3 I3
      (fun _ => D.old) nu3 D.cap3 h3
  have h4lt : ∀ j ∈ D.cells4, D.old4 j < D.cap4 j :=
    storedMeshCapCheck_old_lt D.a D.b D.m D.cells4 I4 D.old4 nu4 D.cap4 h4
  have h5lt : ∀ j ∈ D.cells5, D.old5 j < D.cap5 j :=
    storedMeshCapCheck_old_lt D.a D.b D.m D.cells5 I5 D.old5 nu5 D.cap5 h5
  simp only [levelCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun j hj => (h3lt j hj).le,
    fun j hj => (h4lt j hj).le,
    fun j hj => (h5lt j hj).le⟩

end HistoricalPrefixCapData
end
end ImbalancedChen
