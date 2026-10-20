"""Check bundled claim/schema/label/types/recorded-axiom correspondence; no Git or Lean run."""
import hashlib
import json
from pathlib import Path
import re
from schema_validator import validate
from check_review_state import check_review_state
from check_formalization import check_formalization

ROOT=Path(__file__).resolve().parent

def main():
    a=json.loads((ROOT/'claims.json').read_text());schema=json.loads((ROOT/'claims.schema.json').read_text())
    validate(a,schema,schema); files=set()
    def check(r):
        p=ROOT/r['path'];b=p.read_bytes()
        assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],r['path']
        files.add(r['path'])
    check(a['paper']);tex=(ROOT/a['paper']['path']).read_text()
    ids=[r['id'] for r in a['claims']]
    labels=re.findall(r'\\label\{([^}]+)\}',tex);displayed=re.findall(r'\\claimid\{([^}]+)\}',tex)
    assert len(ids)==len(set(ids))==57 and set(ids)==set(displayed) and len(displayed)==57
    assert len(labels)==len(set(labels)) and set(ids)<=set(labels)
    by_id={r['id']:r for r in a['claims']};done=set();active=set()
    def visit(i):
        assert i not in active
        if i in done:return
        active.add(i)
        for j in by_id[i]['depends_on']: assert j in by_id;visit(j)
        active.remove(i);done.add(i)
    lean_records=json.loads((ROOT/'lean-records.json').read_text())
    for r in a['claims']:
        visit(r['id']);assert r['id']==r['paper_label']
        for e in r['evidence']+[r['review_history']]:check(e)
        review=(ROOT/r['review_history']['path']).read_text()
        for id in r['review_history']['row_ids']:assert len(re.findall(r'^\| '+re.escape(id)+r' ',review,re.M))==1
        lean=r['lean']
        if r['status']=='lean-proved':
            assert lean
            b=(ROOT/lean['file']).read_bytes()
            assert re.search(re.escape(lean['type_signature'])+r'\s*:=', b.decode()), lean['declaration']
            record=lean_records['sources'][lean['file']]
            assert record['sha256']==hashlib.sha256(b).hexdigest() and record['commit']==lean['commit']
            log=(ROOT/lean_records['logs'][lean['accepted_trial']]).read_text()
            m=re.search(re.escape("'"+lean['declaration']+"'")+r' depends on axioms: \[([^]]*)\]',log)
            assert m,lean['declaration']
            assert [x.strip() for x in m[1].split(',') if x.strip()]==lean['axioms']
        elif r['id']=='cor:rays':
            assert r['status']=='open' and lean, 'missing ray existence declarations'
            assert lean['scope']=='existence-only' and lean['effective_algorithm_certified'] is False
            records=[lean,*lean['additional_declarations']]
            assert [x['declaration'] for x in records]==['ClaudeCor.criterion_ray','R002.A3Release.path_ray']
            for x in records:
                b=(ROOT/x['file']).read_bytes()
                assert re.search(re.escape(x['type_signature'])+r'\s*:=',b.decode()),x['declaration']
                sr=lean_records['sources'][x['file']]
                assert sr['sha256']==hashlib.sha256(b).hexdigest() and sr['commit']==x['commit']
                assert x['accepted_trial']=='T1192' and x['build_not_rerun'] is True
                log=(ROOT/lean_records['logs'][x['accepted_trial']]).read_text()
                m=re.search(re.escape("'"+x['declaration']+"'")+r' depends on axioms: \[([^]]*)\]',log)
                assert m and [z.strip() for z in m[1].split(',') if z.strip()]==x['axioms']
        else:assert lean is None
        if r['kind'] in ('theorem','corollary'):
            pat=r'\\begin\{'+r['kind']+r'\}(?:\[[^]]*\])?\\label\{'+re.escape(r['id'])+r'\}(.*?)\\end\{'+r['kind']+r'\}'
            assert re.search(pat,tex,re.S)[1].strip()==r['statement_latex']
    for kind in ('theorem','corollary'):
        assert set(re.findall(r'\\begin\{'+kind+r'\}(?:\[[^]]*\])?\\label\{([^}]+)\}',tex))=={r['id'] for r in a['claims'] if r['kind']==kind}
    assert sum(r['kind']=='formal-lemma' for r in a['claims'])==45
    check_review_state(ROOT,a)
    check_formalization(ROOT,a)
    print(json.dumps(dict(status='PASS',scope=__doc__,claims=57,formal_lemmas=45,hashed_files=len(files),lean_rerun=False,semantic_equivalence_proved=False)))
if __name__=='__main__':main()
