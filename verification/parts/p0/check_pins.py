"""Check exact declared pins; never update dependencies."""
from pathlib import Path
import json
import subprocess

root = Path(__file__).resolve().parents[3]
expected = {
    'goldbach': '09b97db5764ade1246bfb77206baa1b124760958',
    'mathlib': 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
    'LeanArchitect': '78dd66840d3efe8c824c699fc03381cec817c271',
    'plausible': 'b1c4a69a7e247ab7df20460212001673d74f08c0',
    'LeanSearchClient': '0498c7c070c143a3bf7379f4d99a2c63bb9d9715',
    'importGraph': '18a90119a5d316358fde6c86e0ca24e59212e32c',
    'proofwidgets': 'b1436dc749e722c9920036b52cdc43b3451d0b69',
    'aesop': '57d3325be72a842920813bcb40f96a6f7393c185',
    'Qq': 'ee41917ae11d38479fb8fb24745f7ca4bf0a784d',
    'batteries': '41bd267b3f6b7252f6676af46d4ffc6783b64de9',
    'Cli': 'da07ca808b6718cb2aed14dba154e5a08b8f8ecf',
}
assert (root / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0-rc1'
packages = json.loads((root / 'lake-manifest.json').read_text())['packages']
assert {p['name']: p['rev'] for p in packages} == expected, 'Manifest pins changed'
for name, revision in expected.items():
    package = root / '.lake/packages' / name
    if package.is_dir():
        actual = subprocess.check_output(['git', '-C', str(package), 'rev-parse', 'HEAD'], text=True).strip()
        assert actual == revision, f'{name}: checkout revision differs'
        status = subprocess.check_output(['git', '-C', str(package), 'status', '--porcelain', '--untracked-files=no'], text=True)
        assert not status, f'{name}: tracked dependency files changed'
print('All 11 declared dependency pins match the frozen baseline.')
