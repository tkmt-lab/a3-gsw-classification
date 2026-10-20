# Public redacted record correspondence

See [REDACTION-POLICY.md](REDACTION-POLICY.md) for the fixed rules and original/derivative distinction. The original bytes are not bundled; only their hashes and sizes are supplied. Every listed file is a public derivative even when its name retains `.original.log`.

| Public file | Original SHA-256 | Public SHA-256 | Original bytes | Public bytes | Rules |
|---|---|---|---:|---:|---|
| T1202-detached-formal-gate.original.log | c2876b0293e561851bf79798b85ffa7768adfcfcdd789cc930a99d755e9ad9b7 | 4159460a4501e24dab9ff10d14b4a46620fcdb76a3640593662b84629318ccde | 848657 | 848416 | R02-tempdir |
| T1202-execution-receipt.json.original.log | 71544819aaaf2430655edcc0423f0daa19f9804d0c747bb870580f48b1778975 | 576b3d71d3ab8fc560a5cd26c938ba6732aa637240bed8e5c2e4d1566b567e29 | 685 | 610 | R02-tempdir |
| T1202-trial.json.original.log | 8fda80139db676b8c8b7eb22b5c95789d26eab63d1f1df77a464fe9fc3d064be | cb2e9e68d3098a4fb8022fc7572c76ddec1f7dcef3925cb3ad9df62026be86bf | 4101 | 4052 | R01-workdir, R05-derived-fingerprint |
| verify_detached.py.original.log | 08279e67914b68e267daa4b6eac068733a7b8efe24af8a97ed865e8846a808c1 | d55592a7c3d15968eb34cdc8b800fd7480d46a35edbaa677450a296e5fee1847 | 2141 | 2142 | R03-temp-prefix |

This edition also removes the old individual-identifier scanner vocabulary. Private-name checks were performed internally; the public scanner contains generic patterns only. Existing historical record transformations in the table above are unchanged.
