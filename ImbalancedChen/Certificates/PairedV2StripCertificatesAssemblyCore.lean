import ImbalancedChen.Certificates.PairedV2FullCertificateData

/-! Proof-side embeddings and a two-branch composition lemma only.
The actual Row, approximation, selector and checker are unchanged. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace StripAssembly

abbrev StripChecked (i : Fin 186) : Prop :=
  ∀ j : Fin (512 - firstU i),
    (makeCertificate (⟨i, j⟩ : Row)
      (approximation (⟨i, j⟩ : Row))).check = true

theorem joinChecked {m n : ℕ} (e : Fin (m + n) → Fin 186)
    (left : ∀ k : Fin m, StripChecked (e (Fin.castAdd n k)))
    (right : ∀ k : Fin n, StripChecked (e (Fin.natAdd m k))) :
    ∀ k : Fin (m + n), StripChecked (e k) :=
  Fin.addCases (motive := fun k => StripChecked (e k)) left right

/-- Proof-side embedding for original strips 326–341. -/
abbrev indexBlock00 (k : Fin 16) : Fin 186 :=
  (Fin.castAdd 90 (Fin.castAdd 48 (Fin.castAdd 32 k)))

/-- Proof-side embedding for original strips 342–357. -/
abbrev indexBlock01 (k : Fin 16) : Fin 186 :=
  (Fin.castAdd 90 (Fin.castAdd 48 (Fin.natAdd 16 (Fin.castAdd 16 k))))

/-- Proof-side embedding for original strips 358–373. -/
abbrev indexBlock02 (k : Fin 16) : Fin 186 :=
  (Fin.castAdd 90 (Fin.castAdd 48 (Fin.natAdd 16 (Fin.natAdd 16 k))))

/-- Proof-side embedding for original strips 374–389. -/
abbrev indexBlock03 (k : Fin 16) : Fin 186 :=
  (Fin.castAdd 90 (Fin.natAdd 48 (Fin.castAdd 32 k)))

/-- Proof-side embedding for original strips 390–405. -/
abbrev indexBlock04 (k : Fin 16) : Fin 186 :=
  (Fin.castAdd 90 (Fin.natAdd 48 (Fin.natAdd 16 (Fin.castAdd 16 k))))

/-- Proof-side embedding for original strips 406–421. -/
abbrev indexBlock05 (k : Fin 16) : Fin 186 :=
  (Fin.castAdd 90 (Fin.natAdd 48 (Fin.natAdd 16 (Fin.natAdd 16 k))))

/-- Proof-side embedding for original strips 422–437. -/
abbrev indexBlock06 (k : Fin 16) : Fin 186 :=
  (Fin.natAdd 96 (Fin.castAdd 42 (Fin.castAdd 32 k)))

/-- Proof-side embedding for original strips 438–453. -/
abbrev indexBlock07 (k : Fin 16) : Fin 186 :=
  (Fin.natAdd 96 (Fin.castAdd 42 (Fin.natAdd 16 (Fin.castAdd 16 k))))

/-- Proof-side embedding for original strips 454–469. -/
abbrev indexBlock08 (k : Fin 16) : Fin 186 :=
  (Fin.natAdd 96 (Fin.castAdd 42 (Fin.natAdd 16 (Fin.natAdd 16 k))))

/-- Proof-side embedding for original strips 470–485. -/
abbrev indexBlock09 (k : Fin 16) : Fin 186 :=
  (Fin.natAdd 96 (Fin.natAdd 48 (Fin.castAdd 26 k)))

/-- Proof-side embedding for original strips 486–501. -/
abbrev indexBlock10 (k : Fin 16) : Fin 186 :=
  (Fin.natAdd 96 (Fin.natAdd 48 (Fin.natAdd 16 (Fin.castAdd 10 k))))

/-- Proof-side embedding for original strips 502–511. -/
abbrev indexBlock11 (k : Fin 10) : Fin 186 :=
  (Fin.natAdd 96 (Fin.natAdd 48 (Fin.natAdd 16 (Fin.natAdd 16 k))))

end StripAssembly

end ImbalancedChen.Certificates.PairedV2.FullMask
