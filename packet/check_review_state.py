"""Check the new receipt/metadata contract; this does not verify prose mathematics."""
import hashlib
import json
import re

def strip_link_targets(s):
    return re.sub(r'(\[[^\]\n]*\])\([^)\n]+\)', r'\1(<destination>)', s)

def check_review_state(root, claims):
    m=json.loads((root/'independent-proofs.json').read_text())
    assert m['packet_version']=='1.0.5'
    assert m['coverage']==dict(nonprimitive=True,primitive_negative=True,primitive_positive=True)
    assert m['coordinator_reviewers']==1 and not m['human_review'] and not m['full_formalization'] and not m['blind']
    assert len(m['receipts'])==13
    def check(r):
        b=(root/r['path']).read_bytes()
        assert hashlib.sha256(b).hexdigest()==r['sha256'] and len(b)==r['bytes'],r['path']
        return b
    for r in m['receipts']:
        original=check(r['original']);portable=check(r['portable'])
        assert r['source_sha256']==r['original']['sha256']
        assert re.fullmatch('[a-f0-9]{40}',r['source_commit'])
        assert strip_link_targets(original.decode())==strip_link_targets(portable.decode()),('non-link modification',r['portable']['path'])
    by={r['id']:r for r in claims['claims']}
    required={r['portable']['path'] for r in m['receipts']}
    for id in ['thm:classification','sec:positive','sec:negative']:
        r=by[id]
        assert r['human_review'] is False
        assert 'P006-13' in r['review_history']['row_ids'] and 'P006-14' in r['review_history']['row_ids']
        assert required <= {e['path'] for e in r['evidence']}
        for text in ['all nonprimitive','all primitive negative','all primitive positive','not blind','One AI coordinator']:
            assert text in r['independent_verification'],('stale classification receipt',id,text)
    assert all(r['human_review'] is False for r in claims['claims'])
    h=by['thm:classification']['statement_human_check']
    assert h['status']=='confirmed' and h['reviewer']=='owner' and h['checked_on']=='2026-10-19'
    assert h['scope']=='challenge-statement-meaning-only' and h['basis']=='owner-self-report-recorded-by-coordinator'
    assert h['declaration']=='ClaudeChallenge.main' and not h['proof_peer_review'] and not h['novelty_review']
    for r in [h['challenge'],h['guide'],h['receipt']]:check(r)
    assert 'P006-15' in by['thm:classification']['review_history']['row_ids']
    assert all('statement_human_check' not in r for r in claims['claims'] if r['id']!='thm:classification')

    for id,decl in [('thm:classification','ClaudeMain.main_full'),('cor:minimum','ClaudeCor.minimum_at')]:
        r=by[id];assert r['status']=='lean-proved' and r['lean']['declaration']==decl
        remaining=' '.join(r['remaining_obligations']).lower()
        assert 'novelty' in remaining and 'human peer review' in remaining
    assert by['cor:rays']['status']=='open' and by['cor:rays']['lean'], 'missing ray existence declarations'
    assert 'computing' in ' '.join(by['cor:rays']['remaining_obligations'])
    assert by['cor:density']['formalization_plan']['target'] is False
    assert sum(r['status']=='lean-proved' for r in claims['claims'])==47
    assert claims['version']=='1.0.5'
    p006=(root/'P006-corrections.md').read_text()
    assert len(re.findall(r'^\| P006-\d+ ',p006,re.M))==19
    remaining=' '.join(by['thm:classification']['remaining_obligations'])
    for text in ['two-residue','signatures differ','remain unread','short derivation']:
        assert text in remaining,('novelty scope',text)
    assert 'P006-16' in by['thm:classification']['review_history']['row_ids']
    assert p006.startswith('# P006:') and 'Nineteen rows' in p006.split('| ID /')[0]
    for id in ['app:B','app:C']:
        assert 'current English v8.1' in by[id]['status_scope'] and '1.0.5' in by[id]['status_scope']
    for id in ['thm:classification','sec:positive','sec:negative']:
        assert 'not Lean' in by[id]['status_scope'] and 'not admitted hypotheses' in by[id]['status_scope']
    assert by['sec:positive']['status']==by['sec:negative']['status']=='open'
    census=by['app:census']
    assert 'C186 only' in census['status_scope'] and 'main-team-only' in census['status_scope']
    for token in ['C186 only','64 sizes','43,636,843','346 negatives','C188-C200','main-team-only']:
        assert token in census['independent_verification'], 'stale independent census boundary'
        assert token in (root/'INDEPENDENT-PROOFS.md').read_text(), 'stale independent census guide'
    assert 'C182' not in census['independent_verification'] and 'pending' not in census['independent_verification']
    comparison=json.loads((root/'owner-copy-comparison.json').read_text())
    for field in ['owner_copy','current_copy','diff']:check(comparison[field])
    def body(s):return re.sub(r'^import .*\n|^-- Definition-only receipt:.*\n','',s,flags=re.M)
    assert body((root/comparison['owner_copy']['path']).read_text())==body((root/comparison['current_copy']['path']).read_text())
    assert 'target column identifies the affected version' in p006
    assert 'P006-17' in census['review_history']['row_ids']
    return dict(receipts=13,coverage=m['coverage'],human_review=False,independent_prose_formalized=False,classification_lean_proved=True)
