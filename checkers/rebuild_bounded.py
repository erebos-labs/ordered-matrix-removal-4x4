"""Re-elaborate every project module from source, one Lean process at a time."""
import os
import re
import subprocess
from pathlib import Path

root = Path.cwd()
compiler_bin = Path(os.environ.get('LEAN4_BIN', root / 'tooling/installed/lean-4.34.1-darwin_aarch64/bin'))
modules = {'.'.join(p.with_suffix('').parts): p for p in Path('OrderedMatrixRemoval4').glob('*.lean')}
modules['OrderedMatrixRemoval4'] = Path('OrderedMatrixRemoval4.lean')
visiting, completed, order = set(), set(), []

def visit(name):
    if name in completed:
        return
    assert name not in visiting, f'import cycle at {name}'
    visiting.add(name)
    for dependency in re.findall(r'^import\s+(\S+)', modules[name].read_text(), re.M):
        if dependency in modules:
            visit(dependency)
    visiting.remove(name)
    completed.add(name)
    order.append(name)

for name in sorted(modules):
    visit(name)
output = root / '.lake/build/lib/lean'
for name in order:
    target = output / (name.replace('.', '/') + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    print('Rechecking', name, flush=True)
    subprocess.run([str(compiler_bin / 'lake'), 'env', 'lean', '-j2', '-o', str(target), str(modules[name])], check=True)
subprocess.run([str(compiler_bin / 'lake'), 'env', 'lean', '-j2', 'checkers/CheckMilestones.lean'], check=True)
print(f'{len(order)} project modules and the quantified statement checker re-elaborated successfully.', flush=True)
