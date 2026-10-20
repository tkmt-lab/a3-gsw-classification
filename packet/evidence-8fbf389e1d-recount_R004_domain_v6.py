"""Recount saved-review parameter domains; does not construct or classify graphs."""
import argparse
import json
from math import gcd,isqrt
from pathlib import Path

ap=argparse.ArgumentParser()
ap.add_argument('--out',type=Path,required=True)
args=ap.parse_args()
interior=[(k,l) for k in range(1,isqrt(700)+1) for l in range(1,k) if k*k+k*l+l*l<=700]
primitive=[p for p in interior if gcd(*p)==1]
nonprimitive=[p for p in interior if gcd(*p)>1]
axis=[(k,0) for k in range(2,isqrt(700)+1)]
diagonal=[(k,k) for k in range(2,isqrt(700//3)+1)]
assert (len(interior),len(primitive),len(nonprimitive),len(axis),len(diagonal))==(191,127,64,25,14)
result=dict(status='PASS',theorem_domain=191,primitive_interior=127,nonprimitive_interior=64,
            nonprimitive_axis=25,nonprimitive_diagonal=14,boundary_nonprimitive=39,
            noncontrol_total=230,controls=2,stored_records=232,
            scope=__doc__,graph_checks_rerun=False)
with args.out.open('x') as f: json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(result))
