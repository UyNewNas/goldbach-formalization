# Attribution and scope

The replayFromImports function is copied verbatim from Lean 4.33.0-rc1 LeanChecker.lean. Original notice: Copyright (c) 2023 Kim Morrison. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE. Authors: Kim Morrison, Sebastian Ullrich. Lean source: https://github.com/leanprover/lean4/blob/v4.33.0-rc1/src/LeanChecker.lean .

This is an executable audit utility, not a mathematical proof module. Its unsafe IO entry is the same official kernel-replay implementation with an explicit single-target CLI. No object aliases are used, no target declarations are skipped, and imports are not claimed as fresh-replayed. Native binaries and generated C are not archived; build commands and their hashes are retained.
