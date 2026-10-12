#!/usr/bin/env python3
"""Read-only v2 ledger refresh; original snapshot outputs are never overwritten.

See LEDGER_REFRESH.md. This entrypoint never runs Lean, Lake, leanchecker or CI.
"""
from build_ledger_v2 import main

if __name__ == '__main__':
    main()
