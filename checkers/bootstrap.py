"""Restore pinned official dependencies; no proof source or global configuration edits.

Python 3.12+, git, and an independently verified official Lean 4.34.1 toolchain
are required. Network access occurs only with --download. Dependencies and cache
outputs belong to the local package directory, never to the release archive.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
RECORD = json.loads((ROOT / 'DEPENDENCIES.json').read_text())


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def run(*args):
    return subprocess.check_output(list(args), text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--download', action='store_true', help='Allow downloads of the exact pinned sources.')
    args = parser.parse_args()
    compiler = Path(os.environ['LEAN4_BIN']).resolve()
    version = run(str(compiler / 'lean'), '--version')
    assert '4.34.1' in version and RECORD['compiler']['commit'] in version, version
    archive = os.environ.get('LEAN4_ARCHIVE')
    if archive:
        assert digest(Path(archive)) == RECORD['compiler']['archive_sha256']
        print('Official tested macOS-arm64 compiler archive digest matched.')
    else:
        print('Compiler version/commit matched; verify its platform-specific official archive digest as documented.')
    tooling = ROOT / 'tooling'
    tooling.mkdir(exist_ok=True)
    source_archive = tooling / 'mathlib4-pinned.tar.gz'
    mathlib = RECORD['mathlib']
    if not source_archive.is_file():
        if not args.download:
            raise SystemExit('Pinned mathlib archive missing; supply it or pass --download.')
        part = source_archive.with_suffix('.gz.partial')
        request = urllib.request.Request(mathlib['url'], headers={'User-Agent': 'ordered-H4-reproduction'})
        with urllib.request.urlopen(request, timeout=60) as response, part.open('wb') as output:
            shutil.copyfileobj(response, output)
        assert digest(part) == mathlib['archive_sha256'], 'mathlib archive digest mismatch'
        part.rename(source_archive)
    assert digest(source_archive) == mathlib['archive_sha256']
    source = tooling / 'mathlib4-pinned'
    if not source.exists():
        staging = tooling / 'mathlib-source-staging'
        if staging.exists():
            raise SystemExit('Existing extraction staging directory; inspect it before continuing.')
        staging.mkdir()
        with tarfile.open(source_archive, 'r:gz') as bundle:
            members = bundle.getmembers()
            names = [item.name for item in members]
            assert len(names) == len(set(names))
            for item in members:
                path = PurePosixPath(item.name)
                assert not path.is_absolute() and '..' not in path.parts
                assert item.isfile() or item.isdir() or item.issym() or item.islnk()
            bundle.extractall(staging, filter='data')
        roots = list(staging.iterdir())
        assert len(roots) == 1 and roots[0].is_dir()
        roots[0].rename(source)
        staging.rmdir()
    for relative, expected in mathlib['files'].items():
        assert digest(source / relative) == expected, relative
    packages = ROOT / '.lake/packages'
    packages.mkdir(parents=True, exist_ok=True)
    for dependency in RECORD['dependencies']:
        checkout = packages / dependency['name']
        if not checkout.exists():
            if not args.download:
                raise SystemExit(f"Missing {dependency['name']}; pass --download to restore its pinned repository.")
            subprocess.run(['git', '-c', 'core.hooksPath=/dev/null', 'clone', '--no-checkout',
                            dependency['url'], str(checkout)], check=True)
            subprocess.run(['git', '-C', str(checkout), '-c', 'core.hooksPath=/dev/null',
                            'checkout', '--detach', dependency['rev']], check=True)
        assert run('git', '-C', str(checkout), 'rev-parse', 'HEAD') == dependency['rev']
        for relative, expected in dependency['tracked_files'].items():
            assert digest(checkout / relative) == expected, (dependency['name'], relative)
    print(f"Matched {len(mathlib['files'])} mathlib source hashes and all eight pinned dependency trees.")


if __name__ == '__main__':
    main()
