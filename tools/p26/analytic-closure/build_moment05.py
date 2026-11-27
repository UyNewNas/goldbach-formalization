"""Build the complete original Cell05 moment parse/decode candidate separately."""
import importlib.util
import json
from pathlib import Path

path = Path(__file__).with_name('build.py')
spec = importlib.util.spec_from_file_location('p26_diagnostic_builder', path)
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)
builder.STAGE = Path('/workspace/p26-moment05-20261128')
builder.TARGET = 'ImbalancedChen.P2OriginalSaving19Moment05Shape'

if __name__ == '__main__':
    raw = Path('/workspace/goldbach-research/eighth-third-moment-refinement-20261009-a23-low-05.witness.json')
    before = builder.pin(raw)
    assert before['bytes'] == 28973
    assert before['sha256'] == '9a85e92f79b24c2b2361717d3a29ecb6167059e5509211c2f3fb290b5284fe2c'
    builder.main()
    assert builder.pin(raw) == before
    receipt = builder.STAGE / 'RUN.json'
    run = json.loads(receipt.read_text())
    run['original_raw_input'] = before
    run['wrapper_source'] = builder.pin(Path(__file__))
    receipt.write_text(json.dumps(run, indent=2) + '\n')
