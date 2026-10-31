import Mathlib.Data.Int.Basic

/-! Literal historical Q80 carrier, moved without changing its namespace,
fields, constructors or deriving clauses. The legacy DefectLookup module
imports and re-exports it; no duplicate carrier is introduced. -/
namespace ImbalancedChen.Certificates.P2HistoricQ80DefectLookup

structure I80 where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

end ImbalancedChen.Certificates.P2HistoricQ80DefectLookup
