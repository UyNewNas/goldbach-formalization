-- SOURCE_ONLY / UNCOMPILED / NOT PASS / OPEN30.
-- Proposed installation: ImbalancedChen.Certificates.OriginalNodeArraysV1.All40ReaderExtensionalAPI
import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40CheckedTable

namespace P0All40ReaderExtensionalAPI

open ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly
open ImbalancedChen.OriginalU2All40CheckedTable20261024wSourceOnly

/-- Preserve request order and duplicates when materializing an arbitrary finite row list. -/
def sampleRowsList (read : Nat → OriginalNode) (indices : List Nat) : List OriginalNode :=
  indices.map read

/-- Array clients use the same total reader, including both default branches. -/
def sampleRowsArray (read : Nat → OriginalNode) (indices : Array Nat) : Array OriginalNode :=
  indices.map read

/-- Materialize a finite indexed request table without imposing sortedness or coverage. -/
def sampleIndexTable {n : Nat} (read : Nat → OriginalNode) (indices : Fin n → Nat) :
    Array OriginalNode :=
  Array.ofFn (fun j => read (indices j))

/-- A client may project any coordinate or computed value from each sampled node. -/
def sampleValuesList {α : Type} (project : OriginalNode → α)
    (read : Nat → OriginalNode) (indices : List Nat) : List α :=
  indices.map (fun i => project (read i))

theorem literal_sampleRowsList (indices : List Nat) :
    sampleRowsList (assembledRead literalBlocks) indices =
      sampleRowsList originalFinalNodes indices := by
  rw [literalBlocks_read_eq_original]

theorem literal_sampleRowsArray (indices : Array Nat) :
    sampleRowsArray (assembledRead literalBlocks) indices =
      sampleRowsArray originalFinalNodes indices := by
  rw [literalBlocks_read_eq_original]

theorem literal_sampleIndexTable {n : Nat} (indices : Fin n → Nat) :
    sampleIndexTable (assembledRead literalBlocks) indices =
      sampleIndexTable originalFinalNodes indices := by
  rw [literalBlocks_read_eq_original]

theorem literal_sampleValuesList {α : Type} (project : OriginalNode → α)
    (indices : List Nat) :
    sampleValuesList project (assembledRead literalBlocks) indices =
      sampleValuesList project originalFinalNodes indices := by
  rw [literalBlocks_read_eq_original]

/-- Table lookup agrees even at out-of-range positions, for the same explicit fallback. -/
theorem literal_sampleIndexTable_getD {n : Nat} (indices : Fin n → Nat)
    (j : Nat) (fallback : OriginalNode) :
    (sampleIndexTable (assembledRead literalBlocks) indices).getD j fallback =
      (sampleIndexTable originalFinalNodes indices).getD j fallback := by
  rw [literal_sampleIndexTable indices]

theorem literal_sampleRowsList_getD (indices : List Nat)
    (j : Nat) (fallback : OriginalNode) :
    (sampleRowsList (assembledRead literalBlocks) indices).getD j fallback =
      (sampleRowsList originalFinalNodes indices).getD j fallback := by
  rw [literal_sampleRowsList indices]

theorem literal_sampleRowsArray_getD (indices : Array Nat)
    (j : Nat) (fallback : OriginalNode) :
    (sampleRowsArray (assembledRead literalBlocks) indices).getD j fallback =
      (sampleRowsArray originalFinalNodes indices).getD j fallback := by
  rw [literal_sampleRowsArray indices]

/-- Exact preservation of an arbitrary program whose input is the sampled finite table. -/
theorem literal_finite_table_program {n : Nat} {α : Type}
    (indices : Fin n → Nat) (program : Array OriginalNode → α) :
    program (sampleIndexTable (assembledRead literalBlocks) indices) =
      program (sampleIndexTable originalFinalNodes indices) := by
  rw [literal_sampleIndexTable indices]

/-- Keep lower and upper outputs paired for each signed rational request. -/
def queryPair (read : Nat → OriginalNode) (request : Int × Int) : Int × Int :=
  (readQueryLo160 read request.1 request.2,
    readQueryHi160 read request.1 request.2)

def literalQueryPair (request : Int × Int) : Int × Int :=
  (literalQueryLo160 request.1 request.2, literalQueryHi160 request.1 request.2)

/-- A real finite query program; neither rational requests nor outputs are deduplicated. -/
def queryBatchList (read : Nat → OriginalNode) (requests : List (Int × Int)) :
    List (Int × Int) :=
  requests.map (queryPair read)

def queryBatchArray (read : Nat → OriginalNode) (requests : Array (Int × Int)) :
    Array (Int × Int) :=
  requests.map (queryPair read)

theorem queryPair_original_function :
    queryPair originalFinalNodes = literalQueryPair := by
  funext request
  exact Prod.ext (readQuery_original request.1 request.2).1
    (readQuery_original request.1 request.2).2

/-- Batched exact integer answers agree for all signed requests and denominators. -/
theorem literal_queryBatchList (requests : List (Int × Int)) :
    queryBatchList (assembledRead literalBlocks) requests = requests.map literalQueryPair := by
  rw [literalBlocks_read_eq_original]
  unfold queryBatchList
  rw [queryPair_original_function]

theorem literal_queryBatchArray (requests : Array (Int × Int)) :
    queryBatchArray (assembledRead literalBlocks) requests = requests.map literalQueryPair := by
  rw [literalBlocks_read_eq_original]
  unfold queryBatchArray
  rw [queryPair_original_function]

/-- Query-result table defaults are also preserved, without a bound on the lookup index. -/
theorem literal_queryBatchArray_getD (requests : Array (Int × Int))
    (j : Nat) (fallback : Int × Int) :
    (queryBatchArray (assembledRead literalBlocks) requests).getD j fallback =
      (requests.map literalQueryPair).getD j fallback := by
  rw [literal_queryBatchArray requests]

/-- Any consumer of the finite batch sees the same exact original query answers. -/
theorem literal_queryBatchList_program {α : Type}
    (requests : List (Int × Int)) (program : List (Int × Int) → α) :
    program (queryBatchList (assembledRead literalBlocks) requests) =
      program (requests.map literalQueryPair) := by
  rw [literal_queryBatchList requests]

end P0All40ReaderExtensionalAPI
