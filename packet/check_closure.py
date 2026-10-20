"""Verify filesystem closure and SHA-256 inventory, not mathematical correctness."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shlex
from urllib.parse import unquote, urlsplit

ROOT=Path(__file__).resolve().parent

def local(name, relative_to=ROOT):
    p=Path(unquote(name))
    assert name and not p.is_absolute(),('absolute or empty reference',name)
    assert '..' not in p.parts,('parent traversal',name)
    q=relative_to/p
    assert q.resolve().is_relative_to(ROOT),('outside packet',name)
    assert q.exists(),('missing reference',name)
    return q

def main():
    expected={}
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1)
        assert name not in expected
        p=local(name)
        assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==digest,('hash',name)
        expected[name]=digest
    actual=set()
    for p in ROOT.rglob('*'):
        assert not p.is_symlink(),('symlink',str(p))
        assert not any(x in p.relative_to(ROOT).parts for x in ('.git','.lake','__pycache__','mailbox','wiki')),p
        if p.is_file(): actual.add(p.relative_to(ROOT).as_posix())
    assert actual==set(expected)|{'SHA256SUMS'},('inventory',actual-set(expected),set(expected)-actual)
    links=0
    for p in ROOT.glob('*.md'):
        s=p.read_text()
        targets=re.findall(r'\[[^\]\n]*\]\(([^)\n]+)\)',s)
        targets+=re.findall(r'(?m)^\s*\[[^]\n]+\]:\s*(\S+)',s)
        for target in targets:
            target=target.strip('<>')
            u=urlsplit(target)
            if u.scheme:
                assert u.scheme in ('https','http','mailto'),('unexpected URI',target)
                continue # bibliographic URLs, never opened
            if u.path: local(u.path,p.parent);links+=1
    keys={'path','file','certificate_path','audit_path'}
    references=0
    def visit(a):
        nonlocal references
        if isinstance(a,list):
            for v in a: visit(v)
        elif isinstance(a,dict):
            for k,v in a.items():
                if k in keys and isinstance(v,str): local(v);references+=1
                else: visit(v)
    for p in ROOT.rglob('*.json'):
        # Certificates contain graph data, no external input references.
        visit(json.loads(p.read_text()))
    for row in map(json.loads,(ROOT/'data/negative-index.jsonl').read_text().splitlines()): visit(row)
    for label,path in json.loads((ROOT/'record-index.json').read_text()).items(): local(path)
    lean=json.loads((ROOT/'lean-records.json').read_text())
    for path in lean['sources']: local(path)
    for path in lean['logs'].values(): local(path)
    for p in (ROOT/'formal').rglob('*.lean'):
        for m in re.findall(r'^import (Formal(?:\.[A-Za-z0-9_]+)*)$',p.read_text(),re.M):
            local('formal/'+m.replace('.','/')+'.lean')
    manifest=json.loads((ROOT/'formal/lake-manifest.json').read_text())
    assert manifest['packages']
    for pkg in manifest['packages']:
        assert pkg['type']=='git' and re.fullmatch('[a-f0-9]{40}',pkg['rev']),pkg
    commands=json.loads((ROOT/'commands.json').read_text())
    advertised=[]
    for block in re.findall(r'```sh\n(.*?)```',(ROOT/'AGENTS.md').read_text(),re.S):
        advertised += [shlex.split(line) for line in block.splitlines() if line.strip()]
    assert advertised==[r['argv'] for r in commands],('advertised commands',advertised)
    for row in commands:
        assert row['argv'][:2]==['python3','-B'] and len(row['argv'])==3
        local(row['argv'][2])
        for p in row['inputs']: local(p)
    for p in ROOT.rglob('*'):
        if p.suffix in ('.md','.txt','.json','.jsonl','.csv') and p.is_file():
            s=p.read_text()
            assert not re.search(r'/(?:Users|Volumes)/',s),('machine path',p.name)
    # Explicit regressions for the four second-reader packaging findings.
    repairs=json.loads((ROOT/'packet-repairs.json').read_text())
    assert repairs['packet_version']=='1.0.5'
    def fingerprint(r):
        b=local(r['path']).read_bytes()
        assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],('repair fingerprint',r['path'])
    for r in [repairs['certificate_module'],repairs['historical_check_script'],repairs['original_check_script'],repairs['t0929_input'],*repairs['historical_check_inputs']]:
        fingerprint(r)
    cert=ast.parse(local('code/certificates.py').read_text())
    assert not any(isinstance(n,ast.If) and '__name__' in ast.unparse(n.test) for n in cert.body), 'unused certificate CLI'
    citing=(ROOT/'CITING.md').read_text()
    targets=re.findall(r'\]\(([^)]+)\)',citing)
    assert 'paper-A3-v8.1-en.pdf' in targets and 'CITATION.cff' in targets, 'direct citation links'
    assert all('ARCHIVAL' not in t for t in targets), 'archived citation target'
    p006=(ROOT/'P006-corrections.md').read_text()
    row=next(s for s in p006.splitlines() if s.startswith('| P006-09 '))
    assert repairs['historical_claims_version'] in row and repairs['historical_claims_sha256'] in row, 'P006-09 claims identity'
    records=json.loads((ROOT/'record-index.json').read_text())
    assert records['77-check-script']==repairs['historical_check_script']['path']
    trial=json.loads(local(records['T0929']).read_text())
    assert len(trial['inputs'])==1 and trial['inputs'][0]['path']==repairs['t0929_input']['path'], 'T0929 actual input'
    assert trial['inputs'][0]['sha256']==repairs['t0929_input']['sha256'], 'T0929 input hash'
    def arithmetic(s):
        t=ast.parse(s)
        t.body=[n for n in t.body if not (isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in {'here','root','tex','csvp'})]
        return ast.dump(t)
    portable=local(repairs['historical_check_script']['path']).read_text()
    original=local(repairs['original_check_script']['path']).read_text()
    assert arithmetic(portable)==arithmetic(original), 'historical check arithmetic changed'
    assert "root = here.parent.parent" in portable and "root / 'historical-paper-A3-v5-en.tex'" in portable and "root / 'historical-counts-v3.csv'" in portable, 'historical check local inputs'
    from check_publication import check_publication
    publication=check_publication()
    assert publication['repository_url']==local('REPOSITORY-URL.txt').read_text().strip()
    print(json.dumps(dict(status='PASS',scope=__doc__,files=len(actual),markdown_links=links,
                         structured_references=references,commands=len(commands),symlinks=0,repair_regressions=4)))

if __name__=='__main__': main()
