# Split namespace object resolution

This is a build infrastructure repair. It changes no Lean source, theorem,
hypothesis, selected source manifest, or shared dependency file. It supplies no
P3.6 proof acceptance by itself.

## Observed failure

The six-core P3 run at `10598b667c4c3f70147e440ac9e5689cf2f2a1a1`
successfully compiled 189 local modules, including the scalar, log-collar, and
narrow-singleton owned cores under the strict warning policy. It then failed
at the first import of `ActualPrimeReciprocalMass`, before elaborating its
mathematics. The original error and read-only inventory are preserved beside
this note.

`MathlibNt.SieveTheory.Arithmetic.PrimeReciprocalLogScale` already had a cached
object in the exact pinned goldbach checkout. Its source SHA-256 is
`ee42f164aa3896e8ea2d89ede1292e80aa43153662614244b98c074ab7115065`;
its object SHA-256 is
`4841069b676021d3cf8ef388238981cb6c59332c8cf38003a42e0e069aae43ab`.
The new local Buchstab dependency objects had created a `MathlibNt` directory
earlier in `LEAN_PATH`.

Lean 4.33.0-rc1's `Lean.SearchPath.findWithExt`, in
`src/lean/Lean/Util/Path.lean` at compiler commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`, chooses the first root containing
the top-level namespace directory or namespace object. A missing submodule
inside that root does not cause a search of later roots. The earlier runner's
per-file search therefore described a different lookup than the compiler.

## Repair and evidence boundary

The proposed runner uses the pinned namespace lookup rule in preflight and
post-run resolution checks. For a namespace that contains locally built
modules, it copies only the needed cached dependency objects and their
existing `.private`/`.server` sidecars into its own output directory. Each copy
must equal the original bytes. Both original and copied paths are bound in
the run snapshots and recorded in the report; no shared path becomes a
writable output or symlink target.

The original external object hashes and recursively bound import signatures
remain the reuse identity. This avoids recompiling existing external theorems
and preserves already verified local dependency objects. The six owned
targets still undergo fresh strict compilation, exact bundled kernel replay,
and the complete declaration/type/axiom audit. A local mirror mismatch or
post-copy mutation is an error, not a reason to relax verification.

Twelve Python checks pass, including the observed missing-file namespace
shadow, unchanged shared object/sidecar bytes, removal of an obsolete local
sidecar, and rejection of a changed mirror. These checks validate the runner
repair only. The resumed remote Lean result remains a separate required
gate. The 444-entry mathematical source manifest remains unchanged.
