"""Serial optional Lean gate: use a separate copy and already installed pinned dependencies."""
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent
F=ROOT/'formal'

def main():
    manifest=json.loads((F/'lake-manifest.json').read_text())
    for pkg in manifest['packages']:
        p=F/'.lake/packages'/pkg['name']
        assert p.is_dir(),f"Missing pinned dependency {pkg['name']}; choose an explicit setup step first. No download performed."
        actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()
        assert actual==pkg['rev'],f"Pinned revision mismatch: {pkg['name']}"
    assert '4.35.0' in (F/'lean-toolchain').read_text()
    env=dict(os.environ,LEAN_NUM_THREADS='1');deadline=time.monotonic()+900
    def run(argv,expected=0):
        def rows():
            result=[]
            for line in subprocess.check_output(['ps','-axo','pid=,ppid=,rss=,comm='],text=True).splitlines():
                a=line.split(maxsplit=3)
                if len(a)==4:result.append((int(a[0]),int(a[1]),int(a[2])/1024,a[3]))
            return result
        before=[rss for _,_,rss,comm in rows() if comm=='lean' or comm.endswith('/lean')]
        assert sum(before)<3800 and all(x<4096 for x in before),'Insufficient Lean headroom; wait for other work.'
        p=subprocess.Popen(argv,cwd=F,env=env,start_new_session=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        # Drain continuously while measuring, so long compiler output cannot fill the pipe.
        import threading
        output=[]
        def drain():
            for line in p.stdout:output.append(line);print(line,end='',flush=True)
        thread=threading.Thread(target=drain);thread.start()
        peak=0;aggregate=0;reason=None
        while p.poll() is None:
            allrows=rows();owned={p.pid}
            for _ in range(8):owned|={pid for pid,ppid,_,_ in allrows if ppid in owned}
            peak=max([peak]+[rss for pid,_,rss,_ in allrows if pid in owned])
            aggregate=max(aggregate,sum(rss for _,_,rss,c in allrows if c=='lean' or c.endswith('/lean')))
            if peak>3686 or aggregate>7500:reason='preventive RSS stop'
            if time.monotonic()>deadline:reason='900 second execution bound'
            if reason:os.killpg(p.pid,signal.SIGTERM);break
            time.sleep(.15)
        try:p.wait(timeout=10)
        except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
        thread.join()
        print(json.dumps(dict(command=argv,returncode=p.returncode,peak_process_mib=peak,peak_all_lean_mib=aggregate,stopped=reason)),flush=True)
        assert not reason and ((p.returncode==0) if expected==0 else (p.returncode!=0)), 'Unexpected gate result'
        return ''.join(output)
    run(['lake','--no-cache','build','+Formal:olean'])
    log=run(['lake','env','lean','-j1','-M4096','Formal/A3ReleaseCheck.lean'])
    assert 'standard-axiom gate PASS: ClaudeMain.main_full' in log
    for name,axs in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log):
        assert set(x.strip() for x in axs.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},name
    controls=F/'.gate-controls';controls.mkdir(exist_ok=True)
    control=controls/'RejectCustomAxiom.lean'
    assert not control.exists(),'Use a new working copy; previous control record retained.'
    control.write_text('import Formal.StandardAxiomGate\naxiom packet_forbidden : False\nstandard_axioms packet_forbidden\n')
    rejected=run(['lake','env','lean','-j1','-M4096',str(control)],expected=1)
    assert 'forbidden axiom packet_forbidden' in rejected
    print(json.dumps(dict(status='PASS',fresh_allowlist=True,rejection_control=True,installed_dependencies=False,external_kernels_rerun=False,os_sandbox=False)))

if __name__=='__main__':main()
