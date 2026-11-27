# Round 17 candidate for the 96-row ascending cell

Round 16 reached the original 96-row ascending cell 0. Four private identities ask for equality between a vector projected from that table and a vector already defined in `P4AOriginalAscendingCell0AfterSeed7`. For rows 14, 16, 17 and 58, the original and target expressions have exactly the same nine rational coefficients, including the operations and their order. The ordinary compiler reported a stuck rational equality decision at each of these four proofs.

The candidate replaces their coordinate-by-coordinate `decide` calls with four whole-vector `rfl` proofs. The original 96 labels and vectors, `sourceRows`, `sourceRows_core`, and every theorem statement remain byte-for-byte identical. The semantics continue to refer to the original full 96-row physical cell. The earlier accepted module is an unchanged dependency of this owner.

The receipt-bound runner protects the 360 valid normal modules and 52 accepted owned targets, checks the 17 affected modules, and preserves all 377 normal modules, 69 owned targets and nine postflight conditions. The candidate has no formal credit before its own published compilation and audit.
