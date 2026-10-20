# A two-stage classification of linear generalized Stone–Wales paths in Goldberg–Coxeter images of the dodecahedron

**Tatsuhiko Takimoto** (independent researcher)

This repository contains a paper, a Lean 4 formalization, and the verification data for one result:

> **Theorem (two-stage classification).** Let $k>l>0$. The dual of the fullerene $\mathrm{GC}(k,l)[C_{20}]$ has a literal linear generalized Stone–Wales path (Bille–Buchstaber–Spodarev, Definition 1(a)) if and only if $\gcd(k,l)=1$ and, with $m=\min(l,k-l)$,
>
> - $m=1$, or
> - $\lfloor k/m\rfloor\ge 3$ and $k\equiv\pm1 \pmod m$, or
> - $\lfloor k/m\rfloor=2$ and, with $r=k-2m$, $r=1$ or $m\equiv\pm1\pmod r$.

Consequences: the smallest primitive negative example is $\mathrm{GC}(17,5)[C_{20}]=C_{7980}$, and path existence is eventually periodic along every integer affine ray in $(k,l)$ that eventually stays in the domain $0<l<k$.

- Archived on Zenodo: [doi:10.5281/zenodo.23491202](https://doi.org/10.5281/zenodo.23491202) (all versions; this release v1.0.5 is [doi:10.5281/zenodo.23491203](https://doi.org/10.5281/zenodo.23491203)).
- Paper: [`paper/paper-A3-en.pdf`](paper/paper-A3-en.pdf) (LaTeX source alongside).
- Second paper (affine families of fullerenes): [tkmt-lab/gsw-ray-periodicity](https://github.com/tkmt-lab/gsw-ray-periodicity).
- Everything else (Lean sources, certificates, claim records, review records): [`packet/`](packet/). Start with [`packet/AGENTS.md`](packet/AGENTS.md).

## What has been checked, and how

| Item | Status |
|---|---|
| Classification (the theorem above) | **Proved in Lean 4** (`ClaudeMain.main_full`), using only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. Comparator checked it against an independently written statement ([`ComparatorChallengeMain.lean`](packet/formal/Formal/ComparatorChallengeMain.lean), ~130 lines, mathlib only; the definitions alone are in [`ClaudeChallengeSpec.lean`](packet/formal/Formal/ClaudeChallengeSpec.lean)); six kernels accepted the proof. |
| Smallest negative example $(17,5)$ | Proved in Lean (`ClaudeCor.minimum_at`). |
| Eventual periodicity on affine rays (that eventually stay in $0<l<k$) | Existence of a threshold and a period is proved in Lean (`R002.A3Release.path_ray`). A certified algorithm that computes them is not provided. |
| Density of negative parameters → 1 | Prose proof draft; the general counting argument has not had a complete independent review; not formalized. |
| Prose proofs | Two general proofs: the research team's, and one by a separate verification team that did not read the research team's proof, construction or code. The statement was known to it, so this is an independent derivation, not a blind test (see [`packet/INDEPENDENT-PROOFS.md`](packet/INDEPENDENT-PROOFS.md)). |
| Human review | The author checked that the formal statement means the classification above. **The proofs have not had human peer review.** |
| Novelty | Not settled. Some related literature has not yet been read; see Section 11.2 of the paper and [`packet/NOVELTY-SCOPE.md`](packet/NOVELTY-SCOPE.md). |
| Appendix: IPR census $C_{60}$–$C_{200}$ | Two generators, 120,622,224 graphs each, 816 negative classes. A separately built comparison agrees through $C_{186}$. |

The checks are kept apart on purpose: finite computations, AI reviews of the prose, formal proofs, and independent constructions are labelled separately throughout. Corrections are listed in [`packet/P006-corrections.md`](packet/P006-corrections.md).

## How this work was done

The research was carried out with AI systems (OpenAI Codex and Anthropic Claude Code) working as separate teams: exploration and proof drafting, an independent verification team that did not see the main team's proofs or code, literature search, and formalization. The author directed the work, made the decisions recorded in the packet, and is responsible for this release, its provenance and the stated limits of verification. AI systems are not listed as authors.

## Re-checking the Lean proof

Requirements: [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.35.0) and mathlib revision are pinned in [`packet/formal`](packet/formal).

```bash
cd packet/formal
lake exe cache get          # download the prebuilt mathlib
lake build                  # build the formalization
lake env lean Formal/A3ReleaseCheck.lean   # print axioms; fails on any non-standard axiom
```

The same steps run automatically on every push (see [`.github/workflows/lean.yml`](.github/workflows/lean.yml)).

The standard-library Python checks in `packet/` (`check_claims.py`, `check_closure.py`, `check_paper.py`, `check_certificates.py`) inspect the saved records; they do not run Lean.

## Acknowledgements

This work studies the linear generalized Stone–Wales paths defined by A. Bille, V. Buchstaber and E. Spodarev in their list of open problems on fullerenes. It works on the Goldberg–Coxeter construction, named after M. Goldberg and H. S. M. Coxeter and developed for plane graphs, together with the theory of zigzags, by M. Dutour Sikirić and M. Deza. Their work made this one possible. The author is grateful to them, and hopes this work adds something new to the field they opened. Full citations are in the paper.

## Licence

Text, figures and data: CC BY 4.0. Code and Lean sources: Apache-2.0. Details in [LICENSING.md](LICENSING.md).

## Citation

See [`CITATION.cff`](CITATION.cff).

## Contact

Please open an issue in this repository.
