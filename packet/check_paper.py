"""Static editorial/math preservation and saved PDF review; no Lean or new proof."""
from pathlib import Path
import csv,hashlib,json,re
from editorial_next97 import preservation,lexical,syntax
ROOT=Path(__file__).resolve().parent
load=lambda n:json.loads((ROOT/n).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    old=(ROOT/'paper-A3-v8.1-en.tex').read_text();new=(ROOT/'paper-A3-v9.0-en.tex').read_text()
    syntax(new);protected=preservation(old,new,True);scan=lexical(new,True)
    assert new.isascii()
    rows=list(csv.DictReader((ROOT/'data/counts.csv').open()))
    expected=[(int(r['carbon']),int(r['count_per_generator']),int(r['negative'])) for r in rows]
    table=new.split('% BEGIN GENERATED COUNTS:',1)[1].split('% END GENERATED COUNTS',1)[0]
    actual=[tuple(int(x.replace(',','')) for x in m) for m in re.findall(r'^(\d+) & ([\d,]+) & (\d+) \\\\',table,re.M)]
    assert actual==expected and len(actual)==71,'census table changed'
    edits=load('editorial-edit-map.json');record=(ROOT/'VERIFICATION-RECORD.md').read_text()
    assert sha(ROOT/'paper-A3-v8.1-en.tex')==edits['predecessor_sha256']
    assert sha(ROOT/'paper-A3-v9.0-en.tex')==edits['target_sha256']
    for e in edits['edits']:assert e['before'].rstrip() in record,('moved paragraph missing',e['number'])
    claims=load('claims.json')
    assert all(c['id'] in record for c in claims['claims'])
    for token in ['R004','Comparator','same','not a blind','main_full','minimum_at','criterion_ray','process isolation','T1202','unread']:
        assert token in record,('verification scope missing',token)
    pdf=load(load('release-metadata.json')['pdf_validation_file'])
    assert sha(ROOT/'paper-A3-v9.0-en.tex')==pdf['source_sha256']
    assert sha(ROOT/pdf['pdf_path'])==pdf['pdf_sha256']
    assert pdf['pages']==22 and len(pdf['page_render_hashes'])==22 and pdf['visual_review']['all_pages_viewed']
    assert protected==load('editorial-audit.json')['protected_blocks']
    print(json.dumps(dict(status='PASS',counts_rows=71,claims=57,protected_blocks=protected,lexical=scan,pages=22,
        scope=__doc__)))
if __name__=='__main__':main()
