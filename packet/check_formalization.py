"""Saved formalization metadata and exact gate/receipt bytes; no Lean execution."""
import hashlib
import json
import re
def check_formalization(root,claims):
    f=json.loads((root/'formalization.json').read_text())
    assert f['packet_version']=='1.0.5'
    assert f['classification']=='ClaudeMain.main_full' and f['minimum']=='ClaudeCor.minimum_at'
    assert f['ray_existence']=='R002.A3Release.path_ray'
    assert not f['ray_effective_algorithm'] and not f['density_formalized']
    assert not f['human_review'] and not f['novelty_established']
    assert f['independent_prose_derivations']==2
    assert 'specification_human_review' not in f
    h=next(r for r in claims['claims'] if r['id']=='thm:classification')['statement_human_check']
    assert f['statement_human_check']==h and not f['proof_human_peer_review']
    assert not f['all_prose_formula_semantics_reviewed']

    c=f['comparator']
    assert c['scope']=='full-classification-only' and c['same_proof']
    assert not c['os_sandbox'] and not c['fresh_run_in_v7'] and not c['minimum_and_rays_checked']
    assert c['kernels']==['Lean standard','Lean paranoid','lean4lean','nanoda','con-leche','con-ron']
    assert f['permitted_axioms']==['propext','Classical.choice','Quot.sound']
    def fp(r):
        b=(root/r['path']).read_bytes()
        assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],r['path']
    for r in [f['gate'],*f['sources'],*f['pinned_dependencies'],*f['gate_logs'],*f['fixed_receipts']]:fp(r)
    assert f['gate_logs']
    logs='\n'.join((root/r['path']).read_text() for r in f['gate_logs'])
    for decl in ['ClaudeMain.main_full','ClaudeMain.main_primitive','ClaudePos.criterion_sufficient','R002.GCClosed.criterion_necessary','R002.GCClosed.challenge_nonprimitive_no_literal','ClaudeCor.minimum_negative','ClaudeCor.minimum_below','ClaudeCor.minimum_at','ClaudeCor.minimum_data','ClaudeCor.criterion_ray','ClaudeCor.path_ray_primitive','ClaudeCor.path_ray_of_primitive','R002.A3Release.path_ray']:
        assert 'standard-axiom gate PASS: '+decl+' (' in logs,('missing successful gate',decl)
    assert 'forbidden axiom' not in logs and 'sorryAx' not in logs
    for r in claims['claims']:
        if r['lean']:
            for x in [r['lean'],*r['lean'].get('additional_declarations',[])]:
                assert set(x['axioms'])<=set(f['permitted_axioms'])
    raw=(root/'comparator-main-paranoid-2026-10-19.txt.original.log').read_text()
    assert 'Your solution is okay!' in raw
    assert 'sorryAx' not in (root/'formal/Formal/A3ReleaseCheck.lean').read_text()
    assert not (root/'formal/.lake').exists()
    control=f['rejection_control']
    assert control['trial_id']=='T1202' and control['fresh_run_this_revision'] is False
    for k in ['log','trial_record','execution_receipt','source_inventory','driver']:fp(control[k])
    trial=json.loads((root/control['trial_record']['path']).read_text())
    assert trial['trial_id']=='T1202' and trial['status']=='ok'
    assert trial['artifacts'][0]['sha256']==control['log']['sha256']
    receipt=json.loads((root/control['execution_receipt']['path']).read_text())
    assert receipt['status']=='PASS' and receipt['custom_axiom_rejected'] and receipt['reused_build_cache'] and receipt['reused_package_cache']
    assert receipt['packet_inventory_sha256']==control['source_inventory']['sha256']
    inventory={n:h for h,n in (line.split('  ',1) for line in (root/control['source_inventory']['path']).read_text().splitlines())}
    for r in [*f['sources'],*f['pinned_dependencies'],control['driver']]:
        assert inventory[r['path']]==r['sha256'],('control source mismatch',r['path'])
    rawcontrol=(root/control['log']['path']).read_text()
    assert 'forbidden axiom packet_forbidden' in rawcontrol
    records=[json.loads(line) for line in rawcontrol.splitlines() if line.startswith('{')]
    assert any(r.get('returncode')==1 and 'RejectCustomAxiom.lean' in ' '.join(r.get('command',[])) for r in records)
    assert any(r.get('status')=='PASS' and r.get('rejection_control') is True for r in records)
    return f
