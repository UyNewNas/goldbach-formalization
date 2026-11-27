#!/usr/bin/env python3
"""Reuse the frozen same-lane validation helper for the new residual owner."""
import hashlib
import importlib.util
from pathlib import Path

helper = Path(__file__).with_name('validate.py')
assert hashlib.sha256(helper.read_bytes()).hexdigest() == '04e67f06c4232a6bbd10be8d6c5419287c51a6c14e4b56e39864f230115ce6f7'
spec = importlib.util.spec_from_file_location('frozen_partition_validation_helper', helper)
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
driver.MODULE = 'ImbalancedChen.P1OriginalHistoricalResidualCarrier'
driver.SOURCE = driver.WORK / 'ImbalancedChen/P1OriginalHistoricalResidualCarrier.lean'
driver.OUT = Path('/workspace/p1-complete-proof/20261127-p15-residual-carrier-v1/formal-00000')
driver.__file__ = __file__
driver.main()
