#!/usr/bin/env python3
"""Isolated orchestration tests; mocked subprocesses do not verify Lean proofs.

Inputs are a source tree with the frozen article/proofs, an English index, and
verify_release.py. Synthetic review records are explicitly test fixtures, never
publication approvals. No source-tree file is written. Run with Python -O.
"""
from pathlib import Path
import argparse
from collections import Counter
import contextlib
import hashlib
import importlib.util
import io
import json
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from unittest.mock import patch


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-root', type=Path, required=True)
    ap.add_argument('--verifier', type=Path, required=True)
    ap.add_argument('--claims', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    require(sys.flags.optimize >= 1, 'Run these tests with Python -O')
    base = Path(tempfile.mkdtemp(prefix='release-verifier-tests-'))
    seed = base / 'seed'
    f = seed / 'formalization'
    shutil.copytree(args.source_root / 'formalization/LinearStochastic', f / 'LinearStochastic')
    shutil.copytree(args.source_root / 'formalization/licenses', f / 'licenses')
    for name in ['LinearStochastic.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']:
        shutil.copy2(args.source_root / 'formalization' / name, f / name)
    for name in ['main.tex', 'main.pdf', 'references.bib', 'autart.cls']:
        shutil.copy2(args.source_root / name, seed / name)
    (f / 'scripts').mkdir(); (f / 'audit').mkdir()
    shutil.copy2(args.verifier, f / 'scripts/verify_release.py')
    shutil.copy2(args.claims, f / 'audit/claims.en.json')
    index = json.loads(args.claims.read_text())
    write_json(f / 'audit/translation-review.json', {
        'scope': 'SYNTHETIC TEST FIXTURE, NOT AN ACTUAL REVIEW', 'independent_approval': True,
        'verdict': 'pass', 'reviewer': 'fixture reviewer', 'translator': 'fixture translator',
        'blocking_findings': [], 'claims_sha256': sha(args.claims),
        'source_sha256': index['source']['sha256'],
        'proof_inventory_sha256': 'a197fbdec236da5e9e272436caa27fb3e1d6431d31f41b04863c8a69e225c38c',
        'mapping_sha256': '20a8ab4f170a4e2c2a5c5c270b1e7c1c5125bfc201f054011b0db7fe133100ee'})
    write_json(f / 'audit/verifier-review.json', {
        'scope': 'SYNTHETIC TEST FIXTURE, NOT AN ACTUAL REVIEW', 'independent_approval': True,
        'verdict': 'pass', 'reviewer': 'fixture reviewer', 'author': 'fixture author',
        'blocking_findings': [], 'verifier_sha256': sha(args.verifier)})
    def rebind(root):
        files = {str(p.relative_to(root)): sha(p) for p in root.rglob('*') if p.is_file() and
                 p.name != 'release-manifest.json' and '/verification/' not in str(p)}
        write_json(root / 'formalization/audit/release-manifest.json', {'schema_version': 1, 'files': files})
    rebind(seed)
    cases = []
    for case in ['metadata_valid', 'full_valid', 'source_change', 'proof_change_rebound',
                 'pins_change_rebound', 'aggregate_extra', 'mapping_rebound', 'anchor_stale',
                 'duplicate_claim', 'translation_unapproved', 'translation_self_review',
                 'verifier_review_stale', 'build_failure', 'dependency_failure',
                 'toolchain_mismatch', 'child_failure', 'wrong_marker', 'swapped_markers',
                 'missing_marker', 'duplicate_marker', 'axiom_sorry', 'axiom_missing',
                 'axiom_duplicate', 'freshness_mutation']:
        root = base / case
        shutil.copytree(seed, root)
        audit = root / 'formalization/audit'
        def edit_json(name, edit):
            p = audit / name; j = json.loads(p.read_text()); edit(j); write_json(p, j)
        if case == 'source_change': (root / 'main.tex').write_text((root / 'main.tex').read_text() + '\n')
        if case == 'proof_change_rebound':
            p = next((root / 'formalization/LinearStochastic').glob('*.lean')); p.write_text(p.read_text() + '\n')
        if case == 'pins_change_rebound': (root / 'formalization/lean-toolchain').write_text('leanprover/lean4:v0.0.0\n')
        if case == 'aggregate_extra':
            p = root / 'formalization/LinearStochastic.lean';p.write_text(p.read_text() + 'theorem extra : True := True.intro\n')
        if case == 'mapping_rebound':edit_json('claims.en.json', lambda j: j['claims'][0]['declarations'].pop())
        if case == 'anchor_stale':edit_json('claims.en.json', lambda j: j['claims'][0]['source_ranges'][0].update(line=1))
        if case == 'duplicate_claim':edit_json('claims.en.json', lambda j: j['claims'].__setitem__(1, j['claims'][0]))
        if case == 'translation_unapproved':edit_json('translation-review.json', lambda j: j.update(independent_approval=False))
        if case == 'translation_self_review':edit_json('translation-review.json', lambda j: j.update(reviewer=j['translator']))
        if case == 'verifier_review_stale':edit_json('verifier-review.json', lambda j: j.update(verifier_sha256='0'*64))
        if case not in ['source_change']: rebind(root)
        spec = importlib.util.spec_from_file_location('test_'+case, root / 'formalization/scripts/verify_release.py')
        mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
        names = [d for p in sorted((mod.ROOT/'LinearStochastic').rglob('*.lean')) for d in mod.declarations(p)]
        targets = [mod.module_name(p) for p in sorted((mod.ROOT/'LinearStochastic').rglob('*.lean'))]
        lock = threading.Lock(); state = {'active': 0, 'peak': 0, 'calls': []}
        def mock_run(command, **kwargs):
            require(kwargs['cwd'] == mod.ROOT, 'Command escaped fixture')
            if 'leanchecker' in command:
                require(command[1:4] == ['env','leanchecker','--verbose'] and len(command) == 5, 'Changed checker command')
                target = command[-1]
                with lock:
                    state['calls'].append(target); state['active'] += 1; state['peak'] = max(state['peak'], state['active'])
                try:
                    time.sleep(0.001)
                    output = 'replaying '+target+'\n'; code = 0
                    if target == targets[0]:
                        if case == 'child_failure': code = 1
                        if case == 'wrong_marker': output = 'replaying Wrong.Module\n'
                        if case == 'missing_marker': output = ''
                        if case == 'duplicate_marker': output += output
                        if case == 'swapped_markers': output = 'replaying '+targets[1]+'\n'
                    if target == targets[1] and case == 'swapped_markers':output = 'replaying '+targets[0]+'\n'
                    return subprocess.CompletedProcess(command, code, output)
                finally:
                    with lock:state['active'] -= 1
            if command[1:] == ['env','lean','--version']:
                return subprocess.CompletedProcess(command, 0, 'Lean (version '+('0.0.0' if case == 'toolchain_mismatch' else '4.33.0-rc1')+', test fixture)\n')
            if command[1:] == ['build']:
                return subprocess.CompletedProcess(command, 1 if case == 'build_failure' else 0, 'synthetic build\n')
            if command[1:] == ['env','lean','verification/check.lean']:
                output = ''.join("'"+d['name']+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for d in names)
                if case == 'axiom_sorry':output = output.replace('propext','sorryAx',1)
                if case == 'axiom_missing':output = output.split('\n',1)[1]
                if case == 'axiom_duplicate':output += output.splitlines()[0]+'\n'
                if case == 'freshness_mutation':
                    p = root/'references.bib';p.write_text(p.read_text()+'\n')
                return subprocess.CompletedProcess(command, 0, output)
            raise RuntimeError('Unexpected subprocess command')
        def pins():
            if case == 'dependency_failure':raise ValueError('Injected dirty dependency')
            return [{'name':'synthetic pinned dependency','revision':'0'*40,'clean':True}]
        stdout = io.StringIO()
        cli = ['verify_release.py','--kernel-jobs','4'] + (['--metadata-only'] if case == 'metadata_valid' else [])
        with patch.object(mod.subprocess,'run',mock_run), patch.object(mod,'dependency_pins',pins), patch.object(mod.shutil,'which',lambda _: 'mock-lake'), patch.object(mod.sys,'argv',cli), contextlib.redirect_stdout(stdout):
            exit_code = mod.main()
        result = json.loads((mod.OUTPUT/'verification.json').read_text())
        valid = case in ['metadata_valid','full_valid']
        require(exit_code == (0 if valid else 1), 'Wrong exit: '+case)
        require(result['fullPaperPassed'] is (case == 'full_valid'), 'Incorrect full pass: '+case)
        if case == 'metadata_valid':require(not state['calls'] and not result['kernelSubsetPassed'], 'Metadata mode ran or claimed proof checks')
        if state['calls']:
            require(Counter(state['calls']) == Counter(targets), 'Skipped/duplicate targets: '+case)
            require(1 <= state['peak'] <= 4 and state['active'] == 0, 'Invalid concurrency')
        cases.append({'case': case, 'passed': True, 'exit_code': exit_code, 'fullPaperPassed': result['fullPaperPassed'],
                      'kernel_calls': len(state['calls']), 'peak_concurrency': state['peak'], 'errors':result['errors']})
    record = {'scope':'Author-run isolated Python -O orchestration tests, not independent review or actual Lean proof verification.',
              'verifier_sha256':sha(args.verifier),'test_source_sha256':sha(Path(__file__)),
              'case_count':len(cases),'all_passed':True,'production_modified':False,'cases':cases}
    args.output.parent.mkdir(parents=True,exist_ok=True);write_json(args.output,record)
    print(json.dumps({'case_count':len(cases),'all_passed':True,'verifier_sha256':record['verifier_sha256']}))


if __name__ == '__main__': main()
