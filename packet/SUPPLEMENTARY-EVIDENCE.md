# Current packet and retained historical checks

The current manuscript is [English v8.1](paper-A3-v8.1-en.tex), in packet **1.0.5**. The historical repairs below were introduced when the manuscript was English v6.2 and the packet was 0.6.3-draft; those were the versions at that time. This packaging repair does not promote any theorem or review status.

## Coordinator's 77 checks

- [Runnable script](code/check_en_v5_formulas.py), received from coordinator commit `0242e451270df0029d5acf63b35fd3dda6766bc9`.
- [Original source as inert text](historical-check-en-v5-original.py.txt). Original and portable hashes are bound by [PROVENANCE](PROVENANCE.json) and [repair metadata](packet-repairs.json).
- Exact historical inputs: [v5 TeX](historical-paper-A3-v5-en.tex) and [v3 CSV](historical-counts-v3.csv). The CSV is opened for its column names; the final two tests sum rows parsed from TeX, and do not compare every CSV row. Other checks are polynomial identities, finite samples and counts calculated from the proposed rule, not graph decisions.

Only the four input-location assignments (`here`, `root`, `tex`, `csvp`) differ in the runnable copy. It always reads these supplied files. The original arithmetic, checks, optional `--big` branch and known incorrect expectation are unchanged; the builder compares their ASTs.

Optional historical reproduction, from this directory: `python3 -B code/check_en_v5_formulas.py --big`. Use one process, a 60-second bound, existing standard-library Python; no network, installation or paid computation. This is separate from the four acceptance commands. With `--big`, expect **76/77 PASS**, with exactly one failed line: `R004 T<=700: 127 primitive (120/7), 103 nonprimitive`. Without `--big`, the two large-count checks are omitted. The script reports its check results on stdout and does not use a failing exit code for a false check; inspect that output. Do not change 103 to 64 to make the historical evidence green. P006-09 records the later correction: 64 interior nonprimitive pairs and 39 boundary pairs. The separate typesetting issue was outside these 77 checks.

## T0929 input

[Original input receipt](T0929-input-claude-en-v5-review.txt), SHA-256 `3e0792539d4060ad0f06ad57e4f5cbc591a950835b9b46be6b74a3eda8e21c48`, is byte-identical to the input recorded by T0929. The [record index](record-index.json) links T0929, its saved code and output, and this input. The portable trial's `inputs[0].path` now resolves to the supplied file and its original digest.

The receipt provided context for the recount. The saved recount code does not open it: it enumerates the explicit parameter ranges in its own source. Thus this is evidence closure, not a claim of a hidden computational dependency. Old paths inside this receipt, the inert original script and historical CSV fields are literal historical records; no current command follows them.

## P006-09's claims target

The historical target was `A3-v6-machine/claims.json`, version **0.6.0-draft**, SHA-256 `187b0756e1ad8e3fb3fe33e2eb439c30d9565d0251e7d93f4c4151bdec431f83`. This identity is verified against the frozen source during the build. It is not the current [1.0.5 claims metadata](claims.json). The historical claims file is identified rather than redistributed; all current direct claim evidence is supplied.

## Certificate and citation repairs

`code/certificates.py` retains every imported function unchanged and removes only its unused repository CLI. Run `check_certificates.py` through the entry point. [CITING](CITING.md) links directly to the actual [PDF](paper-A3-v8.1-en.pdf) and [CFF](CITATION.cff). At the time of the 0.6.3 repairs the paper remained 0.6.2-draft. The current paper is English v8.1 and this artifact packet is 1.0.5. Authorship is Tatsuhiko Takimoto, Independent researcher; approved licenses and current release authorization are recorded in LICENSING.md and publication-authorization.json. These current records supersede the historical draft/authorship metadata.
