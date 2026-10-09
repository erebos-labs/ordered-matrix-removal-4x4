"""Verify frozen proof bytes and, when supplied, the complete release manifest."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
record = json.loads((ROOT / 'proof-source-manifest.json').read_text())
for name, item in record['files'].items():
    raw = (ROOT / name).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == item['sha256'], name
    assert len(raw) == item['size_bytes'], name
print(f"Matched {len(record['files'])} unchanged frozen proof/configuration/checker files.")
manifest = ROOT / 'FILE_MANIFEST.json'
if manifest.is_file():
    files = json.loads(manifest.read_text())['files']
    for name, item in files.items():
        raw = (ROOT / name).read_bytes()
        assert len(raw) == item['size_bytes'] and hashlib.sha256(raw).hexdigest() == item['sha256'], name
    print(f'Matched all {len(files)} release-manifest payload files.')
print('Hashes establish integrity; theorem correctness relies on the reported Lean checks.')
