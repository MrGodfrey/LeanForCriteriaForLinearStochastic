#!/usr/bin/env python3
"""Test publication-report freshness and escaping using synthetic gate fixtures.

The fixtures originate from test_verify_release.py and contain mocked proof
results. This test never turns them into real verification evidence.
"""
from pathlib import Path
import argparse
import copy
import importlib.util
import json
import tempfile
from unittest.mock import patch


def require(ok, message):
    if not ok: raise ValueError(message)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--renderer',type=Path,required=True)
    ap.add_argument('--fixture',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args()
    spec=importlib.util.spec_from_file_location('report_tests',a.renderer)
    renderer=importlib.util.module_from_spec(spec);spec.loader.exec_module(renderer)
    root=a.fixture/'formalization'
    expected=json.loads((root/'verification/verification.json').read_text())
    require(expected['fullPaperPassed'] is True,'Use a synthetic full_valid fixture')
    # Only dependency inspection is mocked; every source/hash/review/log check is real.
    import subprocess
    def git(command,**kwargs):
        if command[-2:]==['rev-parse','HEAD']:
            package=Path(command[2]).name
            manifest=json.loads((root/'lake-manifest.json').read_text())
            return next(x['rev'] for x in manifest['packages'] if x['name']==package)+'\n'
        if 'status' in command or 'ls-files' in command:return ''
        raise ValueError('Unexpected git command')
    actual_dependencies=[]
    for p in json.loads((root/'lake-manifest.json').read_text())['packages']:
        actual_dependencies.append({'name':p['name'],'revision':p['rev'],'url':p['url'],'clean':True})
    saved=(root/'verification/verification.json').read_bytes()
    record=copy.deepcopy(expected);record['dependencies']=actual_dependencies
    result_path=root/'verification/verification.json'
    def write(r):result_path.write_text(json.dumps(r,indent=2)+'\n')
    cases=[]
    try:
        write(record)
        with patch.object(subprocess,'check_output',git):
            claims,v,h=renderer.load_evidence(root)
            html=renderer.render(claims,v,h)
        require('Full verification passed' in html and html.count('<article class="claim"')==80,'Wrong positive presentation')
        require('http://' not in html and 'https://' not in html,'Unexpected network URL')
        cases.append({'case':'valid','passed':True})
        changes={
            'stale_input':lambda r:r['input_sha256'].update({'main.tex':'0'*64}),
            'wrong_verifier':lambda r:r.update(verifier_sha256='0'*64),
            'contradictory_metadata_mode':lambda r:r.update(mode='metadata-only'),
            'failed_kernel_flag':lambda r:r.update(kernelSubsetPassed=False),
            'failed_build':lambda r:r.update(build_exit_code=1),
            'missing_replay':lambda r:r['kernel_replay_runs'].pop(),
            'wrong_marker':lambda r:r['kernel_replay_runs'][0].update(replayed_modules=['Wrong.Module']),
            'sorry_axiom':lambda r:r['declarations'][0].update(axioms=['sorryAx']),
            'missing_coverage':lambda r:r['coverage'].pop(),
            'unknown_declaration':lambda r:r['declarations'][0].update(name='Wrong.theorem'),
        }
        for name,change in changes.items():
            r=copy.deepcopy(record);change(r);write(r)
            try:
                with patch.object(subprocess,'check_output',git):renderer.load_evidence(root)
            except ValueError:cases.append({'case':name,'passed':True})
            else:raise ValueError('Invalid evidence accepted: '+name)
        pending=copy.deepcopy(record);pending.update(fullPaperPassed=False,mode='metadata-only',kernelSubsetPassed=False,allAxiomsAllowed=False)
        write(pending)
        with patch.object(subprocess,'check_output',git):claims,v,h=renderer.load_evidence(root)
        html=renderer.render(claims,v,h)
        require('Not fully verified' in html and 'Full verification passed' not in html,'Pending status incorrectly promoted')
        cases.append({'case':'pending_not_promoted','passed':True})
        malicious=copy.deepcopy(claims);malicious['claims'][0]['summary']='<script>alert(1)</script>'
        html=renderer.render(malicious,v,h)
        require('<script>alert(1)</script>' not in html and '&lt;script&gt;alert(1)&lt;/script&gt;' in html,'Unescaped source text')
        cases.append({'case':'html_escaping','passed':True})
    finally:result_path.write_bytes(saved)
    import hashlib
    a.output.write_text(json.dumps({'scope':'Author-run presentation tests against synthetic mocked proof evidence; not actual formal verification.','renderer_sha256':hashlib.sha256(a.renderer.read_bytes()).hexdigest(),'case_count':len(cases),'all_passed':True,'cases':cases},indent=2)+'\n')
    print(json.dumps({'cases':len(cases),'all_passed':True}))


if __name__=='__main__':main()
