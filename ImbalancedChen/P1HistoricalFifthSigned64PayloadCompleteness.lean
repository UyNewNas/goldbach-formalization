import ImbalancedChen.P1HistoricalFifthSigned64Payload

/-!
Inverse and completeness of the pure original signed64 payload parser.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.
This proves source-code properties for arbitrary byte lists. It neither
parses NPY headers nor executes the authenticated292633-row payload.
The concrete historical parse/check witness remains UNEXECUTED_CANDIDATE.
-/

namespace ImbalancedChen.P1HistoricalFifthSigned64PayloadCompleteness
noncomputable section
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTableParser
open P1HistoricalFifthSigned64Arithmetic P1HistoricalFifthSigned64Payload

/-- Reverse scalar roundtrip on every unsigned64 word, including its
negative signed half. This preserves the original two's-complement bits. -/
theorem encodeSigned64_decodeSigned64 (word : ℕ) (hword : word < modulus64) :
    encodeSigned64 (decodeSigned64 word) = word := by
  have hnonneg : (0 : ℤ) ≤ word := by omega
  have hupper : (word : ℤ) < (modulus64 : ℤ) := by exact_mod_cast hword
  unfold decodeSigned64
  split_ifs with hhalf
  · unfold encodeSigned64
    rw [Int.emod_eq_of_lt hnonneg hupper]
    rfl
  · have hmod : ((word : ℤ) - (modulus64 : ℤ)) % (modulus64 : ℤ) = (word : ℤ) := by
      calc
        _ = (((word : ℤ) - (modulus64 : ℤ)) + (modulus64 : ℤ)) % (modulus64 : ℤ) :=
          (Int.add_emod_right _ _).symm
        _ = (word : ℤ) % (modulus64 : ℤ) := by congr 1; omega
        _ = (word : ℤ) := Int.emod_eq_of_lt hnonneg hupper
    unfold encodeSigned64
    rw [hmod]
    rfl

/-- Valid little-endian byte lists are reconstructed with their original
length and order. No high byte or leading zero is discarded. -/
theorem encodeNatLE_unsignedLE (bytes : List ℕ) (hbytes : ∀ b ∈ bytes, b < 256) :
    encodeNatLE bytes.length (unsignedLE bytes) = bytes := by
  revert hbytes
  induction bytes with
  | nil => intro hbytes; rfl
  | cons b tail ih =>
      intro hbytes
      have hb := hbytes b (by simp)
      have ht := ih (fun x hx => hbytes x (List.mem_cons_of_mem _ hx))
      simp only [List.length_cons, unsignedLE, encodeNatLE]
      have hmod : (b + 256 * unsignedLE tail) % 256 = b := by omega
      have hdiv : (b + 256 * unsignedLE tail) / 256 = unsignedLE tail := by omega
      rw [hmod, hdiv, ht]

/-- Reverse8-byte roundtrip for every successful scalar decode. -/
theorem encodeWord8_of_decodeWord8 (bytes : List ℕ) (z : ℤ)
    (h : decodeWord8 bytes = some z) : encodeWord8 z = bytes := by
  have hlen := decodeWord8_some_length bytes z h
  have hb := decodeWord8_some_bytes bytes z h
  have hw := unsignedLE_lt bytes hb
  have hw64 : unsignedLE bytes < modulus64 := by
    rw [hlen] at hw
    norm_num [modulus64] at hw ⊢
    exact hw
  have heq : decodeSigned64 (unsignedLE bytes) = z := by
    unfold decodeWord8 at h
    rw [if_pos hlen, if_pos hb] at h
    exact Option.some.inj h
  unfold encodeWord8
  rw [← heq, encodeSigned64_decodeSigned64 _ hw64]
  have hnat := encodeNatLE_unsignedLE bytes hb
  rw [hlen] at hnat
  exact hnat

/-- Any exactly8 legal bytes admit their signed scalar value. -/
theorem decodeWord8_exists (bytes : List ℕ) (hlen : bytes.length = 8)
    (hb : ∀ b ∈ bytes, b < 256) : ∃ z, decodeWord8 bytes = some z := by
  refine ⟨decodeSigned64 (unsignedLE bytes), ?_⟩
  simp only [decodeWord8, if_pos hlen, if_pos hb]

/-- Generic reverse chunk roundtrip. A successful parser keeps the
original complete byte stream, not merely its list of abstract values. -/
theorem encodeChunks_of_decodeChunks {α : Type*} (size : ℕ) (decode : List ℕ → Option α)
    (encode : α → List ℕ)
    (hinverse : ∀ bytes value, decode bytes = some value → encode value = bytes)
    (n : ℕ) (bytes : List ℕ) (values : List α)
    (h : decodeChunks size decode n bytes = some values) : encodeChunks encode values = bytes := by
  induction n generalizing bytes values with
  | zero =>
      by_cases hb : bytes = []
      · subst bytes
        simp only [decodeChunks, if_pos rfl, Option.some.injEq] at h
        subst values
        rfl
      · simp only [decodeChunks, if_neg hb] at h
        cases h
  | succ n ih =>
      simp only [decodeChunks] at h
      cases hd : decode (bytes.take size) with
      | none => simp only [hd] at h; cases h
      | some value =>
          cases ht : decodeChunks size decode n (bytes.drop size) with
          | none => simp only [hd, ht] at h; cases h
          | some tail =>
              simp only [hd, ht, Option.some.injEq] at h
              subst values
              change encode value ++ encodeChunks encode tail = bytes
              rw [hinverse _ _ hd, ih _ _ ht, List.take_append_drop]

/-- Generic completeness for legal fixed-size payloads, proved by actual
prefix/suffix decomposition. No concrete payload execution is required. -/
theorem decodeChunks_exists {α : Type*} (size : ℕ) (decode : List ℕ → Option α)
    (hcomplete : ∀ block : List ℕ, block.length = size →
      (∀ b ∈ block, b < 256) → ∃ value, decode block = some value)
    (n : ℕ) (bytes : List ℕ) (hlen : bytes.length = size * n)
    (hb : ∀ b ∈ bytes, b < 256) : ∃ values, decodeChunks size decode n bytes = some values := by
  induction n generalizing bytes with
  | zero =>
      have hnil : bytes = [] := List.length_eq_zero.mp (by simpa using hlen)
      subst bytes
      exact ⟨[], by simp [decodeChunks]⟩
  | succ n ih =>
      have hge : size ≤ bytes.length := by rw [hlen, Nat.mul_succ]; omega
      have htlen : (bytes.take size).length = size := by
        rw [List.length_take, Nat.min_eq_left hge]
      have hdlen : (bytes.drop size).length = size * n := by
        rw [List.length_drop, hlen, Nat.mul_succ]
        omega
      have hbtake : ∀ b ∈ bytes.take size, b < 256 := by
        intro b hm
        apply hb b
        rw [← List.take_append_drop size bytes]
        exact List.mem_append.mpr (Or.inl hm)
      have hbdrop : ∀ b ∈ bytes.drop size, b < 256 := by
        intro b hm
        apply hb b
        rw [← List.take_append_drop size bytes]
        exact List.mem_append.mpr (Or.inr hm)
      obtain ⟨value, hvalue⟩ := hcomplete _ htlen hbtake
      obtain ⟨tail, htail⟩ := ih _ hdlen hbdrop
      exact ⟨value :: tail, by simp only [decodeChunks, hvalue, htail]⟩

/-- A generic successful chunk parser retains a proved value property. -/
theorem decodeChunks_some_values {α : Type*} (size : ℕ) (decode : List ℕ → Option α)
    (P : α → Prop) (hvalue : ∀ bytes value, decode bytes = some value → P value)
    (n : ℕ) (bytes : List ℕ) (values : List α)
    (h : decodeChunks size decode n bytes = some values) : ∀ value ∈ values, P value := by
  induction n generalizing bytes values with
  | zero =>
      by_cases hb : bytes = []
      · subst bytes
        simp only [decodeChunks, if_pos rfl, Option.some.injEq] at h
        subst values
        simp
      · simp only [decodeChunks, if_neg hb] at h
        cases h
  | succ n ih =>
      simp only [decodeChunks] at h
      cases hd : decode (bytes.take size) with
      | none => simp only [hd] at h; cases h
      | some value =>
          cases ht : decodeChunks size decode n (bytes.drop size) with
          | none => simp only [hd, ht] at h; cases h
          | some tail =>
              simp only [hd, ht, Option.some.injEq] at h
              subst values
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hvalue _ _ hd
              · exact ih _ _ ht x hx

/-- Exactly ten list values reconstruct the same typed columns. -/
theorem ofFn_listColumns (values : List ℤ) (hlen : values.length = 10) :
    List.ofFn (listColumns values) = values := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi₁ hi₂
  rw [List.getElem_ofFn]
  exact (List.getElem_eq_getD (l := values) (i := i) (h := hi₂) 0).symm

/-- Reverse complete80-byte row roundtrip, including opaque statistics. -/
theorem encodeRow_of_decodeRow80 (bytes : List ℕ) (wire : FifthWireRow)
    (h : decodeRow80 bytes = some wire) : encodeRow wire = bytes := by
  unfold decodeRow80 at h
  cases hf : decodeFields 10 bytes with
  | none => simp only [hf, Option.map_none] at h; cases h
  | some fields =>
      have heq : wireOfColumns (listColumns fields) = wire := by
        simpa only [hf, Option.map_some] using h
      have hlen := (decodeChunks_some_lengths 8 decodeWord8 decodeWord8_some_length 10 bytes fields hf).1
      rw [← heq]
      unfold encodeRow
      rw [wireColumns_wireOfColumns, ofFn_listColumns fields hlen]
      exact encodeChunks_of_decodeChunks 8 decodeWord8 encodeWord8 encodeWord8_of_decodeWord8
        10 bytes fields hf

theorem decodeRow80_exists (bytes : List ℕ) (hlen : bytes.length = 80)
    (hb : ∀ b ∈ bytes, b < 256) : ∃ wire, decodeRow80 bytes = some wire := by
  obtain ⟨fields, hfields⟩ := decodeChunks_exists 8 decodeWord8 decodeWord8_exists
    10 bytes (by simpa using hlen) hb
  exact ⟨wireOfColumns (listColumns fields), by
    simp only [decodeRow80, decodeFields, hfields, Option.map_some]⟩

/-- Every decoded signed field is in the original signed64 interval. -/
theorem decodeRow80_some_signed_range (bytes : List ℕ) (wire : FifthWireRow)
    (h : decodeRow80 bytes = some wire) (column : Fin 10) :
    -(half64 : ℤ) ≤ wireColumns wire column ∧ wireColumns wire column < (half64 : ℤ) := by
  unfold decodeRow80 at h
  cases hf : decodeFields 10 bytes with
  | none => simp only [hf, Option.map_none] at h; cases h
  | some fields =>
      have heq : wireOfColumns (listColumns fields) = wire := by simpa only [hf, Option.map_some] using h
      have hfields := decodeChunks_some_values 8 decodeWord8
        (fun z => -(half64 : ℤ) ≤ z ∧ z < (half64 : ℤ)) decodeWord8_some_range 10 bytes fields hf
      have hget : ∀ (values : List ℤ),
          (∀ z ∈ values, -(half64 : ℤ) ≤ z ∧ z < (half64 : ℤ)) →
          ∀ i, -(half64 : ℤ) ≤ values.getD i 0 ∧ values.getD i 0 < (half64 : ℤ) := by
        intro values
        induction values with
        | nil => intro hv i; norm_num [half64]
        | cons z tail ih =>
            intro hv i
            cases i with
            | zero => simpa only [List.getD_cons_zero] using hv z (by simp)
            | succ i =>
                simpa only [List.getD_cons_succ] using
                  ih (fun y hy => hv y (List.mem_cons_of_mem _ hy)) i
      rw [← heq, wireColumns_wireOfColumns]
      exact hget fields hfields column.val

/-- ANY successfully decoded valid payload re-encodes to exactly the same
bytes, in original field and row order. No suffix or opaque bit is lost. -/
theorem encodeRows_of_decodeRows (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeRows bytes = some rows) : encodeRows rows = bytes := by
  unfold decodeRows at h
  split_ifs at h with hmod
  · exact encodeChunks_of_decodeChunks 80 decodeRow80 encodeRow encodeRow_of_decodeRow80
      (bytes.length / 80) bytes rows h
  · cases h

/-- Every legal byte-domain payload whose length is80*n is accepted. -/
theorem decodeRows_exists_of_length (bytes : List ℕ) (n : ℕ)
    (hlen : bytes.length = 80 * n) (hb : ∀ b ∈ bytes, b < 256) :
    ∃ rows, decodeRows bytes = some rows := by
  obtain ⟨rows, hrows⟩ := decodeChunks_exists 80 decodeRow80 decodeRow80_exists n bytes hlen hb
  refine ⟨rows, ?_⟩
  have hmod : bytes.length % 80 = 0 := by omega
  have hdiv : bytes.length / 80 = n := by omega
  simp only [decodeRows, if_pos hmod, hdiv, decodeRowsFuel]
  exact hrows

/-- Under the explicit valid-byte domain, acceptance is EXACTLY80-divisibility. -/
theorem decodeRows_exists_iff_length_dvd (bytes : List ℕ) (hb : ∀ b ∈ bytes, b < 256) :
    (∃ rows, decodeRows bytes = some rows) ↔ 80 ∣ bytes.length := by
  constructor
  · rintro ⟨rows, hrows⟩
    refine ⟨rows.length, ?_⟩
    have hlen := decodeRows_some_length bytes rows hrows
    omega
  · rintro ⟨n, hlen⟩
    exact decodeRows_exists_of_length bytes n hlen hb

/-- Complete parser-language characterization, including byte rejection. -/
theorem decodeRows_exists_iff (bytes : List ℕ) :
    (∃ rows, decodeRows bytes = some rows) ↔
      (∀ b ∈ bytes, b < 256) ∧ 80 ∣ bytes.length := by
  constructor
  · rintro ⟨rows, hrows⟩
    have hb := decodeRows_some_bytes bytes rows hrows
    exact ⟨hb, (decodeRows_exists_iff_length_dvd bytes hb).mp ⟨rows, hrows⟩⟩
  · rintro ⟨hb, hlen⟩
    exact (decodeRows_exists_iff_length_dvd bytes hb).mpr hlen

/-- Decoded fields retain the signed64 domain at every row index. -/
theorem decodeRows_some_signed_range (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeRows bytes = some rows) : ∀ wire ∈ rows, ∀ column : Fin 10,
      -(half64 : ℤ) ≤ wireColumns wire column ∧ wireColumns wire column < (half64 : ℤ) := by
  unfold decodeRows at h
  split_ifs at h with hmod
  · exact decodeChunks_some_values 80 decodeRow80
      (fun wire => ∀ column : Fin 10,
        -(half64 : ℤ) ≤ wireColumns wire column ∧ wireColumns wire column < (half64 : ℤ))
      decodeRow80_some_signed_range (bytes.length / 80) bytes rows h
  · cases h

end
end ImbalancedChen.P1HistoricalFifthSigned64PayloadCompleteness

