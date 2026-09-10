#!/usr/bin/env python3
"""Rebuild the distributed current Lean proof, then check its literal endpoint.

Exit zero certifies the deformed half-erasure information-capacity result, never the operational coding theorem or the whole paper.
The source manifest is a reviewed snapshot, not an automatically renewed proof.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = 'release/source-manifest.json'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
ENDPOINT = 'QIT.QubitActivation.deformed_superactivation_main'
CURRENT_TARGET = 'QIT'
ENDPOINT_MARKER = 'EXACT_ENDPOINT_WITHOUT_HYPOTHESES_PASS'


def current_target_sources(root, sources):
    """Resolve reviewed local imports; the compiled environment checks this again.

    This scan is for the import syntax used by this snapshot, not a general Lean
    parser. The kernel audit must independently report exactly the same closure.
    """
    pending = [CURRENT_TARGET]
    seen = set()
    selected = {}
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        name = module.replace('.', '/') + '.lean'
        if module != CURRENT_TARGET:
            if name not in sources:
                raise RuntimeError('Unreviewed current-target import: ' + module)
            selected[name] = sources[name]
        source = (root / name).read_text()
        imports = re.findall(r'(?m)^\s*(?:(?:public|private|meta)\s+)*import[ \t]+([^\n]+)', source)
        for line in imports:
            for imported in line.split('--', 1)[0].split():
                if imported == 'QIT' or imported.startswith('QIT.'):
                    pending.append(imported)
    return dict(sorted(selected.items()))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_sources(root=ROOT):
    manifest = json.loads((root / MANIFEST).read_text())
    review = json.loads((root / 'audit/source-review.json').read_text())
    expected = review['mathematical_sources']
    if expected != manifest['mathematical_sources']:
        raise RuntimeError('Release sources do not match the preserved source review')
    actual = {str(p.relative_to(root)): digest(p) for p in (root / 'QIT').rglob('*.lean')}
    if actual != expected:
        changed = sorted(k for k in actual.keys() | expected.keys()
                         if actual.get(k) != expected.get(k))
        raise RuntimeError('Mathematical source mismatch: ' + ', '.join(changed))
    for name, sha in manifest['support_files'].items():
        if digest(root / name) != sha:
            raise RuntimeError('Reviewed release support file changed: ' + name)
    lake = json.loads((root / 'lake-manifest.json').read_text())
    pins = {p['name']: p['rev'] for p in lake['packages']}
    if pins != review['third_party_revisions'] or pins != manifest['dependencies']:
        raise RuntimeError('Lake dependencies differ from the reviewed revisions')
    if manifest['current_target'] != CURRENT_TARGET:
        raise RuntimeError('Unexpected current proof target')
    if current_target_sources(root, expected) != manifest['current_target_sources']:
        raise RuntimeError('Current-target source closure differs from reviewed imports')
    if manifest['current_target_sources'] != expected:
        raise RuntimeError('Distributed sources include modules outside the proof closure')
    return manifest


def clean_environment():
    env = os.environ.copy()
    # Resolve the local package through Lake, not a caller's private QIT search path.
    for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT'):
        env.pop(key, None)
    return env


def command(args, *, root=ROOT):
    result = subprocess.run(args, cwd=root, env=clean_environment(), text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError('Command failed: ' + ' '.join(args) + '\n' + result.stdout)
    return result.stdout


def check_dependencies(root=ROOT):
    lake = json.loads((root / 'lake-manifest.json').read_text())
    revisions = {}
    for package in lake['packages']:
        folder = root / lake['packagesDir'] / package['name']
        head = command(['git', '-C', str(folder), 'rev-parse', 'HEAD'], root=root).strip()
        if head != package['rev']:
            raise RuntimeError('Dependency revision mismatch: ' + package['name'])
        if command(['git', '-C', str(folder), 'status', '--porcelain',
                    '--untracked-files=all'], root=root).strip():
            raise RuntimeError('Dirty dependency sources: ' + package['name'])
        revisions[package['name']] = head
    return revisions


def validate_axioms(output, manifest):
    if re.search(r': error(?:\(|:)', output):
        raise RuntimeError('Lean error in declaration audit output')
    loaded = set(re.findall(r'LOADED_QIT_MODULE (\S+)', output))
    expected = {name.removesuffix('.lean').replace('/', '.')
                for name in manifest['current_target_sources']}
    if loaded != expected:
        raise RuntimeError('Loaded QIT imports do not equal the current-target source closure')
    # Lean may pretty-print a long declaration's axiom list across several lines.
    records = re.findall(r'^AUDIT (\S+) : \[([^\[\]]*)\]$', output, re.MULTILINE)
    if len(records) != sum(line.startswith('AUDIT ') for line in output.splitlines()):
        raise RuntimeError('Malformed declaration audit record')
    axioms = {}
    for name, values in records:
        if name in axioms:
            raise RuntimeError('Duplicate declaration audit record: ' + name)
        axioms[name] = [v.strip() for v in values.split(',') if v.strip()]
    if ENDPOINT not in axioms or ENDPOINT_MARKER not in output:
        raise RuntimeError('Missing literal endpoint or declaration audit')
    if any(set(values) - STANDARD for values in axioms.values()):
        raise RuntimeError('Nonstandard axioms in the release proof')
    return axioms


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-sources-only', action='store_true',
                        help='Check snapshot identity only; does not certify a Lean proof')
    args = parser.parse_args()
    audit = ROOT / 'audit'
    audit.mkdir(exist_ok=True)
    result_file = audit / 'release-verification.json'
    if not args.check_sources_only:
        result_file.write_text('{"compiled": false, "current_endpoint_verified": false}\n')
    before = check_sources()
    if args.check_sources_only:
        print(f"PASS: {len(before['mathematical_sources'])} distributed mathematical source modules, "
              f"{len(before['current_target_sources'])} in the current proof; "
              'support hashes match; no manuscript is required (no build performed)')
        return 0
    version = command(['lake', 'env', 'lean', '--version']).strip()
    if 'version 4.30.0,' not in version:
        raise RuntimeError('Unexpected Lean toolchain: ' + version)
    deps = check_dependencies()
    inputs_file = audit / 'release-build-inputs.json'
    inputs_file.write_text(json.dumps(before, indent=2) + '\n')
    # A fresh root build excludes previous QIT artifacts. Only pinned third-party
    # dependency artifacts, obtained separately with `lake exe cache get`, are reused.
    build_dir = ROOT / '.lake/build'
    if build_dir.is_symlink():
        raise RuntimeError('Refusing to clean a symlinked local build directory')
    if build_dir.exists():
        shutil.rmtree(build_dir)
    log_file = audit / 'release-build.log'
    print(f'Rebuilding {CURRENT_TARGET} and its complete QIT dependency closure; '
          'follow audit/release-build.log', flush=True)
    with log_file.open('w') as log:
        result = subprocess.run(['lake', 'build', CURRENT_TARGET], cwd=ROOT,
                                env=clean_environment(), stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError('Lake build failed; see audit/release-build.log')
    checked = command(['lake', 'env', 'lean', '-DautoImplicit=false', 'Check.lean'])
    (audit / 'release-axioms.log').write_text(checked)
    axioms = validate_axioms(checked, before)
    if check_sources() != before or check_dependencies() != deps:
        raise RuntimeError('Sources or dependencies changed during verification')
    if json.loads(inputs_file.read_text()) != before:
        raise RuntimeError('Build input record changed during verification')
    result = {
        'compiled': True, 'current_endpoint_verified': True,
        'full_paper_formalized': False,
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'lean_version': version, 'dependencies': deps,
        'source_manifest_sha256': digest(ROOT / MANIFEST),
        'source_review_sha256': digest(ROOT / 'audit/source-review.json'),
        'current_target': CURRENT_TARGET,
        'source_modules_rebuilt': len(before['current_target_sources']),
        'all_current_target_sources_rebuilt': True,
        'all_qit_sources_rebuilt': len(before['current_target_sources']) == len(before['mathematical_sources']),
        'loaded_qit_closure_matches': True,
        'endpoint': ENDPOINT, 'literal_endpoint_checked': True, 'endpoint_marker': ENDPOINT_MARKER,
        'scope': before['scope'],
        'audited_declaration_count': len(axioms), 'main_axioms': axioms[ENDPOINT],
        'nonstandard_axioms': [], 'unsafe_overlay_declarations': [],
        'build_log_sha256': digest(log_file),
        'build_inputs_sha256': digest(inputs_file),
        'axiom_log_sha256': digest(audit / 'release-axioms.log'),
        'trusted_build_inputs': 'Lean toolchain and pinned third-party Lake artifacts; '
                                'all distributed QIT sources rebuilt locally',
    }
    result_file.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (RuntimeError, OSError, ValueError, KeyError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
