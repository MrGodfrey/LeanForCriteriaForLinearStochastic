#!/usr/bin/env python3
"""Render an offline English report from fresh publication verification evidence.

This script does not run Lean or upgrade a verification result. It refuses stale
or internally inconsistent evidence. Run after verify_release.py in the same
release package. No external scripts, fonts, or network requests are used.
"""
from __future__ import annotations

from collections import Counter
import hashlib
from html import escape
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load_evidence(root):
    script = root / 'scripts/verify_release.py'
    spec = importlib.util.spec_from_file_location('publication_verifier', script)
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    files, declarations, claims, snapshot, named, ranges = verifier.check_metadata()
    path = root / 'verification/verification.json'
    result = json.loads(path.read_text())
    require(result.get('input_sha256') == snapshot, 'Verification inputs are stale or incomplete')
    require(result.get('verifier_sha256') == verifier.sha(script), 'Verification used a different verifier')
    require(result.get('manuscript_sha256') == claims['source']['sha256'], 'Manuscript hash differs')
    require(result.get('proof_inventory_sha256') == verifier.ORIGINAL_PROOFS and
            result.get('mapping_sha256') == verifier.ORIGINAL_MAPPING, 'Proof/mapping digest differs')
    require(result.get('named_manuscript_claims') == named and result.get('source_anchor_count') == ranges,
            'Named statements or exact source anchors differ')
    require(result.get('metadataPassed') is True, 'Publication bindings have not passed')
    raw_declarations = [{k: d.get(k) for k in ('name', 'kind', 'file', 'line')}
                        for d in result.get('declarations', [])]
    require(raw_declarations == declarations, 'Recorded declaration inventory differs from current sources')
    full = result.get('fullPaperPassed') is True
    if full:
        require(result.get('mode') == 'full' and result.get('kernelSubsetPassed') is True and
                result.get('allAxiomsAllowed') is True and result.get('errors') == [],
                'Full-pass flag contradicts verification status')
        require(result.get('build_exit_code') == 0 and result.get('audit_exit_code') == 0,
                'Full-pass flag lacks successful build/type inspection')
        modules = [verifier.module_name(p) for p in files]
        records = result.get('kernel_replay_runs', [])
        require([r.get('module') for r in records] == modules and result.get('replayed_modules') == modules,
                'Replay inventory differs from current modules')
        require(all(r.get('exit_code') == 0 and r.get('exact_target_replayed') is True and
                    r.get('replayed_modules') == [r['module']] for r in records),
                'A module replay failed or did not identify exactly its target')
        require(all(d.get('axioms_allowed') is True and isinstance(d.get('axioms'), list) and
                    set(d['axioms']) <= verifier.ALLOW for d in result['declarations']),
                'Missing or unapproved axiom closure')
        expected_coverage = [{'id': c['id'], 'status': 'full', 'declarations': c['declarations']}
                             for c in claims['claims']]
        require(result.get('coverage') == expected_coverage, 'Full coverage differs from reviewed English index')
        require(result.get('dependencies') == verifier.dependency_pins(), 'Dependency sources changed')
        replay_log = (root / 'verification/kernel-replay.log').read_text()
        require(Counter(re.findall(r'^replaying (\S+)$', replay_log, re.M)) == Counter(modules),
                'Replay log differs from recorded exact targets')
        axiom_log = (root / 'verification/axioms.log').read_text()
        entries = [(m[1], sorted(x.strip() for x in (m[2] or '').split(',') if x.strip()))
                   for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", axiom_log)]
        require(Counter(n for n, _ in entries) == Counter(d['name'] for d in declarations),
                'Axiom log declaration count differs')
        closures = dict(entries)
        require(all(closures[d['name']] == d['axioms'] for d in result['declarations']),
                'Axiom log differs from recorded closures')
    return claims, result, hashlib.sha256(path.read_bytes()).hexdigest()


def render(claims, result, evidence_hash):
    full = result.get('fullPaperPassed') is True
    state = 'Full verification passed' if full else 'Not fully verified'
    state_class = 'passed' if full else 'pending'
    counts = claims['expected_counts']
    by_name = {d['name']: d for d in result['declarations']}
    cards = []
    for c in claims['claims']:
        title = c.get('title') or c['id']
        search = ' '.join([c['id'], title, c['summary'], c['reason'], *c['declarations']]).lower()
        theorem_links = []
        for name in c['declarations']:
            d = by_name[name]
            theorem_links.append('<li><a href="'+escape(d['file'], quote=True)+'#L'+str(d['line'])+'"><code>'+escape(name)+'</code></a></li>')
        source = []
        for r in c['source_ranges']:
            source.append('<p><a href="../main.tex#L'+str(r['line'])+'">Manuscript lines '+str(r['line'])+'–'+str(r['end_line'])+'</a></p><pre>'+escape(r['source_excerpt'])+'</pre>')
        badge = 'Verified' if full else 'Awaiting full verification'
        boundary = '<p class="boundary"><strong>Scope:</strong> '+escape(c['semantic_boundary'])+'</p>' if c.get('semantic_boundary') else ''
        cards.append('<article class="claim" data-search="'+escape(search, quote=True)+'"><div class="claim-top"><span class="tag">'+escape(c.get('coverage_unit', c['type']).replace('_',' '))+'</span><span class="badge '+state_class+'">'+badge+'</span></div><h3>'+escape(title)+'</h3><p class="claim-id">'+escape(c['id'])+'</p><p>'+escape(c['summary'])+'</p><details><summary>Proof correspondence and source</summary><p>'+escape(c['reason'])+'</p>'+boundary+'<h4>Formal declarations</h4><ul class="theorems">'+''.join(theorem_links)+'</ul><h4>Exact manuscript excerpts</h4>'+''.join(source)+'</details></article>')
    statistics = ''.join('<div class="stat"><strong>'+str(n)+'</strong><span>'+label+'</span></div>' for n,label in
                         [(counts['claims'],'reviewed mathematical claims'),(counts['named'],'named statements'),
                          (counts['modules'],'Lean proof modules'),(counts['declarations'],'inspected declarations')])
    errors = ''
    if result.get('errors'):
        errors = '<section class="error"><h2>Verification errors</h2><ul>'+''.join('<li>'+escape(str(x))+'</li>' for x in result['errors'])+'</ul></section>'
    intro = ('The frozen manuscript and all 80 items in its independently reviewed mathematical inventory passed the publication gate.'
             if full else 'The publication gate has not established full completion. The reviewed mappings below do not replace a successful proof run.')
    template = r'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Formal verification · Linear stochastic controllability</title>
<style>
:root{font-family:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;color:#172536;background:#f4f6fa;line-height:1.6;font-size:16px}*{box-sizing:border-box}body{margin:0}main{max-width:1180px;margin:auto;padding:48px 24px 72px}a{color:#145ea8;text-decoration-thickness:1px;text-underline-offset:3px}h1,h2,h3{line-height:1.2;color:#132942}h1{font-size:clamp(2rem,4.5vw,3.5rem);letter-spacing:-.035em;max-width:920px;margin:18px 0}h2{font-size:1.6rem}h3{font-size:1.15rem;margin:12px 0 4px}h4{margin-bottom:8px}.eyebrow{text-transform:uppercase;letter-spacing:.14em;font-size:.76rem;font-weight:700;color:#50677b}.lead{font-size:1.1rem;max-width:880px;color:#40556b}.status{display:inline-block;padding:8px 14px;border-radius:24px;font-weight:650}.passed{background:#e1f4e9;color:#176442}.pending{background:#fff0cd;color:#795005}.links{display:flex;gap:20px;flex-wrap:wrap;margin:24px 0}.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:14px;margin:32px 0}.stat{background:white;border:1px solid #dce4ed;border-radius:12px;padding:22px}.stat strong{font-size:2.2rem;display:block;line-height:1.2}.stat span{font-size:.9rem;color:#566a7d}.note{background:#eaf0f7;border-left:4px solid #587c9d;padding:18px 22px;border-radius:4px}.toolbar{position:sticky;top:0;background:#f4f6faf5;backdrop-filter:blur(8px);padding:16px 0;z-index:1;display:flex;align-items:center;gap:16px}.toolbar input{flex:1;min-width:0;border:1px solid #b8c8d8;border-radius:8px;padding:13px;font:inherit}.toolbar span{white-space:nowrap;color:#50677b;font-size:.9rem}.claims{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:18px}.claim{background:white;border:1px solid #dce4ed;border-radius:12px;padding:22px;overflow:hidden}.claim-top{display:flex;justify-content:space-between;gap:12px;align-items:start}.tag{font-size:.72rem;text-transform:uppercase;letter-spacing:.06em;color:#5e7184}.badge{font-size:.75rem;border-radius:12px;padding:2px 8px;white-space:nowrap}.claim-id{font: .8rem ui-monospace,monospace;color:#617387;margin-top:0}.claim p{font-size:.93rem}details{border-top:1px solid #e3e9ef;padding-top:12px}summary{cursor:pointer;font-weight:600;color:#215b89}.theorems{padding-left:20px;overflow-wrap:anywhere}.theorems li{margin:7px 0}code{font-size:.77rem}pre{white-space:pre-wrap;overflow-wrap:anywhere;background:#f4f6fa;padding:14px;border-radius:6px;font-size:.75rem;line-height:1.6}.boundary{background:#f8fafc;padding:12px}.trust{margin-top:40px;background:white;border:1px solid #dce4ed;border-radius:12px;padding:26px}.trust li{margin:8px 0}.evidence{margin-top:24px;font-size:.8rem;color:#52677a;overflow-wrap:anywhere}.error{background:#fff0f0;padding:20px;border:1px solid #e8b6b6}footer{margin-top:30px;font-size:.82rem;color:#607286}[hidden]{display:none!important}@media(max-width:760px){main{padding:28px 16px 50px}.stats{grid-template-columns:repeat(2,1fr)}.claims{grid-template-columns:1fr}.toolbar{gap:8px}.stat{padding:16px}.claim-top{flex-wrap:wrap}}
</style></head><body><main>
<p class="eyebrow">Article companion · reproducible formal mathematics</p>
<h1>Controllability of linear stochastic systems</h1>
<p class="status @@STATE_CLASS@@">@@STATE@@</p><p class="lead">@@INTRO@@</p>
<div class="links"><a href="../main.pdf">Read the article</a><a href="../README.md">Reproduce the verification</a><a href="verification/verification.json">Machine-readable result</a><a href="../docs/FORMALIZATION.md">Scope, revisions, and limitations</a></div>
<div class="stats">@@STATS@@</div>
<p class="note">The correspondence uses <strong>87 exact manuscript excerpts</strong>. The gate checks every local module and every explicit named declaration. Its result is tied to the source hashes below; changing the article, proofs, dependency pins, or reviews requires a new verification run.</p>
@@ERRORS@@
<h2>Mathematical coverage</h2><div class="toolbar"><input id="search" type="search" aria-label="Search claims and declarations" placeholder="Search a claim, topic, or Lean declaration"><span id="count">80 of 80 claims</span></div>
<div class="claims">@@CARDS@@</div><p id="empty" hidden>No matching claims.</p>
<section class="trust"><h2>What this result establishes</h2><ul>
<li>The checked public proof closures use only <code>propext</code>, <code>Classical.choice</code>, and <code>Quot.sound</code>. Local placeholders, custom axioms, and unsafe/native proof shortcuts are rejected.</li>
<li>The pinned upstream source-import closure contains eight unused placeholder sites. Their presence is disclosed separately from the checked local declarations, whose proof dependencies must contain no <code>sorryAx</code>.</li>
<li>Kernel replay uses Lean's own kernel. It is not an independently implemented kernel and does not freshly replay every imported mathlib proof. The pinned toolchain, build infrastructure, and ordinary computational trust assumptions remain relevant.</li>
<li>Natural-language correspondence and English translation received independent AI-assisted review. Hashes preserve the reviewed artifacts; they are not signatures, institutional certification, or a guarantee about statements outside the explicit inventory.</li>
<li>Five manuscript clarifications or proof-route revisions are disclosed in the <a href="../docs/FORMALIZATION.md">formalization notes</a>. Exact mathematical QR/SVD results do not certify floating-point software, roundoff, or operation counts.</li>
</ul></section>
<div class="evidence"><strong>Frozen manuscript SHA-256</strong><br>@@SOURCE_HASH@@<br><strong>Verification result SHA-256</strong><br>@@EVIDENCE_HASH@@<br><strong>Checked at</strong> @@CHECKED_AT@@</div>
<footer>Offline report generated from the current publication verification evidence. Expand each entry to inspect its exact source excerpts and formal declarations.</footer>
</main><script>
const input=document.getElementById('search'),cards=[...document.querySelectorAll('.claim')];
input.addEventListener('input',()=>{const words=input.value.toLowerCase().trim().split(/\s+/).filter(Boolean);let shown=0;for(const card of cards){const hit=words.every(w=>card.dataset.search.includes(w));card.hidden=!hit;if(hit)shown++;}document.getElementById('count').textContent=`${shown} of ${cards.length} claims`;document.getElementById('empty').hidden=shown!==0;});
</script></body></html>
'''
    values = {'STATE_CLASS':state_class,'STATE':escape(state),'INTRO':escape(intro),'STATS':statistics,
              'ERRORS':errors,'CARDS':''.join(cards),'SOURCE_HASH':escape(claims['source']['sha256']),
              'EVIDENCE_HASH':escape(evidence_hash),'CHECKED_AT':escape(result.get('checked_at','not recorded'))}
    for key,value in values.items():template=template.replace('@@'+key+'@@',value)
    return template


def main():
    claims, result, digest = load_evidence(ROOT)
    (ROOT / 'report.html').write_text(render(claims,result,digest),encoding='utf-8')
    print('formalization/report.html')


if __name__ == '__main__': main()
