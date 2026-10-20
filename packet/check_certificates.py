"""Check the supplied finite certificates, not generator completeness or the A3 theorem."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
from certificates import check_certificate
from verify_fullerenes import canonical_form, validate_dual

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--limit',type=int);args=ap.parse_args()
    start=time.monotonic()
    rows=list(map(json.loads,(ROOT/'data/negative-index.jsonl').read_text().splitlines()))
    counts=list(csv.DictReader((ROOT/'data/counts.csv').open()))
    assert len(rows)==816 and len(counts)==71
    assert [int(r['carbon']) for r in counts]==list(range(60,201,2))
    assert sum(int(r['count_per_generator']) for r in counts)==120622224
    assert sum(int(r['negative']) for r in counts)==816
    assert len({r['canonical_sha256'] for r in rows})==816
    assert sum(r['certificate_bytes'] for r in rows)==60758514
    for r in counts:
        assert int(r['negative'])==sum(int(r[x]) for x in ('GC2','GC3','non_GC'))
        assert int(r['negative'])==sum(s['carbon']==int(r['carbon']) for s in rows)
    if args.limit is not None:assert 1<=args.limit<=816
    chosen=rows[:args.limit] if args.limit is not None else rows
    forms=set();starts=0;vertices=0
    for r in chosen:
        b=(ROOT/r['certificate_path']).read_bytes()
        assert len(b)==r['certificate_bytes'] and hashlib.sha256(b).hexdigest()==r['certificate_sha256']
        cert=json.loads(b);assert cert['schema']==1 and cert['predicate']=='literal_definition1'
        adj=tuple(map(tuple,cert['adjacency']))
        assert validate_dual(adj)['carbon_vertices']==r['carbon']
        assert not any(len(adj[v])==5 for a in adj if len(a)==5 for v in a)
        form=canonical_form(adj)
        assert hashlib.sha256(form).hexdigest()==r['canonical_sha256'] and form not in forms
        forms.add(form);result=check_certificate(cert);assert result['starts']==120
        starts+=result['starts'];vertices+=result['path_vertices']
    print(json.dumps(dict(status='PASS',scope=__doc__,certificates_checked=len(chosen),starts_checked=starts,
        full_canonical_codes_unique=len(forms),path_vertices_checked=vertices,seconds=time.monotonic()-start,native_rerun=False)))
if __name__=='__main__':main()
