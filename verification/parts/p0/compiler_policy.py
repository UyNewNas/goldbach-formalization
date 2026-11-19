"""One memory policy for P0's independent compiler entrypoints.

The default is 12 GiB. Set P0_LEAN_MEMORY_MB before bootstrap to request a
larger budget; old 4 GiB settings fail explicitly instead of returning silently.
This controls Lean's own -M limit, not physical memory or the native checker.
"""
import os
import re

DEFAULT_MEMORY_MB = 12288
MEMORY_ENV = 'P0_LEAN_MEMORY_MB'


def resolve_memory_mb(environ=None):
    environment = os.environ if environ is None else environ
    value = environment.get(MEMORY_ENV, str(DEFAULT_MEMORY_MB))
    if not isinstance(value, str) or re.fullmatch(r'[0-9]+', value) is None:
        raise ValueError(f'{MEMORY_ENV} must be an integer >= {DEFAULT_MEMORY_MB} MiB')
    memory_mb = int(value)
    if memory_mb < DEFAULT_MEMORY_MB:
        raise ValueError(f'{MEMORY_ENV} must be >= {DEFAULT_MEMORY_MB} MiB; got {memory_mb}')
    return memory_mb


def compiler_flags(memory_mb=None):
    if memory_mb is None:
        memory_mb = resolve_memory_mb()
    elif type(memory_mb) is not int or memory_mb < DEFAULT_MEMORY_MB:
        raise ValueError(f'{MEMORY_ENV} must be an integer >= {DEFAULT_MEMORY_MB} MiB')
    return ['-t0', '-j2', f'-M{memory_mb}']
