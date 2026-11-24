#!/usr/bin/env python3
"""Create a source-only release, without requiring a Git checkout."""
from pathlib import Path
import argparse
import fnmatch
import hashlib
import json
import os
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SKIP_DIRS = {'.git', '.lake', '.release', '__pycache__', 'node_modules', '_opam'}
SKIP_NAMES = {'RocqMakefile', 'RocqMakefile.conf', '.RocqMakefile.d',
              'TextbookMakefile', 'TextbookMakefile.conf', '.TextbookMakefile.d'}
SKIP_GLOBS = ('*.vo', '*.vos', '*.vok', '*.glob', '*.aux', '*.cache', '*.olean',
              '*.ilean', '*.o', '*.cmi', '*.cmo', '*.cmx', '*.pyc', '*.zip',
              '*.tar.gz', '*.export', '*.log', '*.env', '.env', '*.pem', '*.key')


def source_files():
    for current, dirs, files in os.walk(ROOT, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS
                         and not (Path(current) / d).is_symlink())
        for name in sorted(files):
            path = Path(current) / name
            rel = path.relative_to(ROOT).as_posix()
            if path.is_symlink() or name in SKIP_NAMES:
                continue
            if rel.endswith('/.vscode/settings.json') or rel == '.vscode/settings.json':
                continue
            if any(fnmatch.fnmatch(name, pat) for pat in SKIP_GLOBS):
                continue
            yield path, rel


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=ROOT / '.release/filter-calculus-code.zip')
    args = parser.parse_args()
    output = args.output.resolve()
    if output.suffix != '.zip':
        parser.error('The output must be a .zip file')
    output.parent.mkdir(parents=True, exist_ok=True)
    manifest = []
    with zipfile.ZipFile(output, 'w', zipfile.ZIP_DEFLATED) as archive:
        for path, rel in source_files():
            if path.resolve() == output:
                continue
            data = path.read_bytes()
            if path.suffix.lower() in {'.lean', '.v', '.md', '.txt', '.sh', '.py', '.yml', '.yaml', '.json', '.toml', '.opam'} or path.name in {'Makefile', '_CoqProject', '_CoqProjectTextbook', 'lean-toolchain', 'LICENSE', '.gitignore', '.gitattributes'}:
                data = data.decode('utf-8-sig').replace('\r\n', '\n').encode('utf-8')
            manifest.append({'path': rel, 'size': len(data),
                             'sha256': hashlib.sha256(data).hexdigest()})
            archive.writestr('filter-calculus-code/' + rel, data)
        archive.writestr('filter-calculus-code/RELEASE-MANIFEST.json',
                         json.dumps({'format': 1, 'files': manifest},
                                    ensure_ascii=False, indent=2) + '\n')
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    output.with_suffix('.zip.sha256').write_text(digest + '  ' + output.name + '\n',
                                                encoding='ascii')
    print(f'{len(manifest)} source files: {output}')
    print(f'SHA256: {digest}')


if __name__ == '__main__':
    main()
