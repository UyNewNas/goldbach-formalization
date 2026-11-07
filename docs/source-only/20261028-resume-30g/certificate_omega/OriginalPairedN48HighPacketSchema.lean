import ImbalancedChen.P2N48SavedParentRowRecost

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Literal witness schema, not an Omega evaluator. For columns
(term,ix,iy,iz,iw,method,floorQ), the mixed-radix packet is
term+2*(ix+48*(iy+48*(iz+48*(iw+48*(method+16*floorQ))))).
All seven archived fields are transcribed, including ordinary methods.
JSON-byte parsing/transcription correctness is NOT a proved theorem here.
-/
namespace ImbalancedChen.OriginalPairedN48HighPacketSchema
open P2N48SavedParentRowRecost

def packetTerm (p : ℕ) : Fin 2 := ⟨p % 2, Nat.mod_lt _ (by decide)⟩
def packetX (p : ℕ) : Fin 48 := ⟨p / 2 % 48, Nat.mod_lt _ (by decide)⟩
def packetY (p : ℕ) : Fin 48 := ⟨p / 96 % 48, Nat.mod_lt _ (by decide)⟩
def packetZ (p : ℕ) : Fin 48 := ⟨p / 4608 % 48, Nat.mod_lt _ (by decide)⟩
def packetW (p : ℕ) : Fin 48 := ⟨p / 221184 % 48, Nat.mod_lt _ (by decide)⟩
def packetMethod (p : ℕ) : ℕ := p / 10616832 % 16
def packetFloor (p : ℕ) : ℕ := p / 169869312

def decodeOriginalPacket (ordinal p : ℕ) : SourceRow :=
  ⟨ordinal, packetTerm p, packetX p, packetY p, packetZ p,
    packetW p, packetMethod p, packetFloor p⟩

theorem decoded_ordinal (ordinal p : ℕ) :
    (decodeOriginalPacket ordinal p).ordinal = ordinal := rfl

theorem decoded_archived_fields (ordinal p : ℕ) :
    (decodeOriginalPacket ordinal p).term = packetTerm p ∧
    (decodeOriginalPacket ordinal p).ix = packetX p ∧
    (decodeOriginalPacket ordinal p).iy = packetY p ∧
    (decodeOriginalPacket ordinal p).iz = packetZ p ∧
    (decodeOriginalPacket ordinal p).iw = packetW p ∧
    (decodeOriginalPacket ordinal p).method = packetMethod p ∧
    (decodeOriginalPacket ordinal p).floorQ = packetFloor p := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end ImbalancedChen.OriginalPairedN48HighPacketSchema
