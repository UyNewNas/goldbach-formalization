New source candidate only: `partial-tail/P5SubdivisionStoredBlock071.lean`, SHA256 `41c5a10b4812e3193c0cc105ad64de4f607ef6c732728e3935b6e1632aef70b9`. It is uncompiled/unvalidated and was generated solely as source text under root's explicit partial-tail authorization.

The original124d09f source declares1817 rows and

`theorem source_index_at : ∀ j : Fin rows.size, (rows[j.val]).sourceIndex = 290816 + j.val`.

The prefix, including every original row field, imports, namespace and rows_size rfl declaration, is byte-identical. The public theorem header/type is exactly unchanged. No hypothesis, licence field, numeric floor, geometry assertion or resource option is added.

The new private pieces cover offsets0,64,…,1728 with Fin64, then offset1792 with Fin25. Each has the existing form

`∀ j : Fin width, (rows[offset+j.val]'(...rows_size...omega)).sourceIndex = 290816+(offset+j.val) := by decide +kernel`.

The public proof introduces j and hj : j.val <1817. The28 ordered tests are j.val<64,…,<1792. In each full branch, the same original omega step identifies `64*k+j.val%64=j.val`, then applies that Fin64 helper. In the final branch, previous tests imply j.val≥1792; together with hj, the residue is below25. The source explicitly proves `htail : j.val %64<25` by omega, applies the Fin25 helper and rewrites using the same index equality. This is the only new tail-specific proof structure.

The author did not evaluate any decide expression or run Lean/omega. Exact string-prefix/public-type checks and hashing establish source identity only. T10 should review the natural-number branch/residue reasoning and the exact generated source selection; remote compilation/kernel/type/axiom checks remain independent future gates.
