"""Bounded implementation comparison only; this does not certify localization."""
import argparse
import hashlib
import json
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--exports', type=Path, default=PACKAGE / 'fixtures/lean-export')
parser.add_argument('--fixtures', type=Path, default=PACKAGE / 'fixtures/research')
parser.add_argument('--output', type=Path)
args = parser.parse_args()
ROOT = args.exports.resolve()
ARCHIVE = args.fixtures.resolve()

def expanded_tags(blocks, weights, h):
    out = []
    kinds = {'V+': 0, 'V-': 1}
    for tag, weight in zip(blocks, weights):
        for clone in range(weight):
            if tag[0] == 'A':
                _, level, kind, parity, group = tag
                k = kinds.get(kind)
                if k is None:
                    k = (2 if kind == 'W+' else 4) + parity
                out.append(f'A,{level},{k},{group},{clone}')
            elif tag[0] == 'D':
                out.append(f'D,{clone}')
            else:
                _, depth, node, sign = tag
                out.append(f'T,{depth},{int(sign in ("+", "L"))},{node},{clone}')
    return out

results = []
# Depth one archived expanded matrix: exact bytes, not a copy-count check.
expected1 = (ARCHIVE / 'host_h1.txt').read_bytes()
actual1 = (ROOT / 'lean-host-h1.txt').read_bytes()
assert expected1 == actual1
results.append({'check': 'h1_expanded_matrix_bytes', 'n': 32, 'cells': 1024,
                'sha256': hashlib.sha256(actual1).hexdigest(), 'passed': True})
# Depth two archived weighted axes and matrix, expanded without importing the generator.
a = json.loads((ARCHIVE / 'host_h2.json').read_text())
expanded = []
for row, weight in zip(a['matrix'], a['row_weights']):
    line = ''.join(str(bit) * w for bit, w in zip(row, a['column_weights']))
    expanded.extend([line] * weight)
actual2 = (ROOT / 'lean-host-h2.txt').read_text().splitlines()
assert expanded == actual2
assert len(actual2) == a['n'] == 120
results.append({'check': 'h2_expanded_matrix', 'n': 120, 'cells': 14400, 'passed': True})
for axis, key, weights in [('r', 'rows', 'row_weights'), ('c', 'columns', 'column_weights')]:
    actual = (ROOT / f'lean-axis-{axis}-h2.txt').read_text().splitlines()
    expected = expanded_tags(a[key], a[weights], 2)
    assert actual == expected
    assert len(set(actual)) == 120
    results.append({'check': f'h2_{axis}_tags_order_and_clones', 'positions': 120, 'passed': True})
if args.output is not None:
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({'coverage': 'finite h=1,2 only', 'results': results}, indent=2) + '\n')
print(json.dumps(results, indent=2))
