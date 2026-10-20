"""Static source checks, not TeX compilation or a mathematical proof checker."""
import argparse
import csv
import hashlib
import json
import re
from pathlib import Path

BASE = Path(__file__).resolve().parent


def check():
    p = BASE / 'paper-A3-v8.1-en.tex'
    s = p.read_text()
    assert s.isascii(), 'Source should compile without Unicode-specific engines'
    assert '% COUNTS_TABLE' not in s
    stack = []
    for match in re.finditer(r'\\(begin|end)\{([^}]+)\}', s):
        op, env = match.groups()
        if op == 'begin':
            stack.append(env)
        else:
            assert stack and stack.pop() == env, (op, env)
    assert not stack
    # Ignore comments and escaped braces. This is deliberately only lexical.
    stripped = re.sub(r'(?<!\\)%[^\n]*', '', s)
    depth = 0
    for match in re.finditer(r'(?<!\\)[{}]', stripped):
        depth += 1 if match.group() == '{' else -1
        assert depth >= 0
    assert depth == 0
    labels = re.findall(r'\\label\{([^}]+)\}', s)
    assert len(labels) == len(set(labels)), 'duplicate labels'
    for ref in re.findall(r'\\(?:ref|eqref)\{([^}]+)\}', s):
        assert ref in labels, ref
    bib = set(re.findall(r'\\bibitem\{([^}]+)\}', s))
    for refs in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}', s):
        assert set(refs.split(',')) <= bib
    assert re.findall(r'\\tag\{([^}]+)\}', s) == [*map(str, range(1, 13)), 'B1', 'B2', 'C1']
    assert len(re.findall(r'\\begin\{theorem\}', s)) == 1
    assert len(re.findall(r'\\begin\{corollary\}', s)) == 3
    before, after = s.split('\\appendix', 1)
    assert len(re.findall(r'\\section\{', before)) == 11
    assert len(re.findall(r'\\section\{', after)) == 3
    rows = list(csv.DictReader((BASE / 'data/counts.csv').open()))
    expected = [(int(r['carbon']), int(r['count_per_generator']), int(r['negative'])) for r in rows]
    table = s.split('% BEGIN GENERATED COUNTS:', 1)[1].split('% END GENERATED COUNTS', 1)[0]
    actual = [tuple(int(x.replace(',', '')) for x in m) for m in re.findall(r'^(\d+) & ([\d,]+) & (\d+) \\\\', table, re.M)]
    assert actual == expected and len(actual) == 71
    return {'status': 'PASS', 'scope': __doc__, 'counts_rows': 71,
            'totals': [sum(x[i] for x in actual) for i in (1, 2)],
            'numbered_statements': 4, 'equation_tags': 15,
            'tex_compiled': False, 'rendered_review': False,
            'source_sha256': hashlib.sha256(p.read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    result = check()
    if args.out:
        with args.out.open('x') as handle:
            json.dump(result, handle, indent=2)
            handle.write('\n')
    print(json.dumps(result))
