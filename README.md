# Lean formalization of stochastic controllability criteria

This repository is the Lean 4 companion to **A Unified Kalman-Type Classification of Controllability for Linear Stochastic Systems**, by **Qi Lü and Yu Wang**.

It contains the manuscript and formal proofs of its mathematical claims, including the stochastic analysis, finite-dimensional algebra, semialgebraic arguments, feedback construction, and elimination algorithm needed for the main results.

**Read the [paper](main.pdf), explore the [English verification report](formalization/report.html), browse the [Lean sources](formalization/LinearStochastic), or start with the [formalization guide](docs/FORMALIZATION.md).**

## Main result

For the constant-coefficient system

$$
\mathrm{d}y=(Ay+Bu)\mathrm{d}t+\sum_{j=1}^{m}(C_jy+D_ju)\mathrm{d}W^j,
$$

the paper constructs a decreasing sequence of subspaces whose terminal value is the obstruction $V_\ast=V_n$. On every positive time horizon,

$$
\mathrm{AC}\iff\mathrm{ANC}\iff\mathrm{ENC}\iff V_\ast=\lbrace 0\rbrace,
$$

and

$$
\mathrm{EC}\iff V_\ast=\lbrace 0\rbrace\quad\text{and}\quad\mathrm{rank}(\mathcal D)=mn,
\qquad
\mathcal D=(D_1^{\mathsf T},\ldots,D_m^{\mathsf T})^{\mathsf T}.
$$

Here AC and ANC mean approximate controllability and approximate null controllability; EC and ENC are their exact counterparts. The formal statements use ordinary progressively measurable finite-energy controls, the original Brownian motion with its usual augmented natural filtration, and actual continuous square-integrable solution paths. Terminal targets range over all corresponding square-integrable random variables.

The central entry point is [`LinearStochastic.RawCompleteClassification.classification`](formalization/LinearStochastic/RawCompleteClassification.lean). Further results provide explicit rank tests, deterministic time-dependent null feedback with polynomial small-time energy cost, and an equivalent orthogonal elimination procedure.

## Verification status

The table below records the reference release at
[`6a7eebe7311a`](https://github.com/MrGodfrey/LeanForCriteriaForLinearStochastic/tree/6a7eebe7311a0bd52c1e59c0b1b7150c7bee6137),
checked with Lean `v4.33.0-rc1`. Its frozen reports do not certify a later
migration or a Palomar registration. See the [Palomar preparation record](docs/PALOMAR.md)
for the current toolchain, independent statement interface, and preflight status.

The current Palomar candidate, commit
[`c088eb9943197e88c4b046223239d4c4f0180513`](https://github.com/MrGodfrey/LeanForCriteriaForLinearStochastic/tree/c088eb9943197e88c4b046223239d4c4f0180513),
passed the [complete official mechanical preflight](https://github.com/MrGodfrey/LeanForCriteriaForLinearStochastic/actions/runs/39017801590)
on 2026-10-17: exact Comparator correspondence and acceptance by Lean, NanoDa,
and con-ron. The [saved report](formalization/palomar/mechanical-report.json)
is bound to that SHA. This preflight does not constitute Palomar registration.

The reference verification of the accompanying revised manuscript passed:

| Check | Result |
|---|---:|
| Inventoried mathematical claims | 80 / 80 covered |
| Named manuscript statements | 18 / 18 covered |
| Project modules built and individually replayed through Lean's kernel | 384 / 384 |
| Explicitly named declarations checked | 2,559 |
| Of these, theorems and lemmas | 2,015 |
| Unapproved axioms in their transitive dependencies | 0 |

Coverage is determined by a claim-by-claim comparison with the manuscript, not by the number of Lean declarations. The reference project proof sources contain no `sorry`, `admit`, or project-defined axioms. Their audited declaration dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.

The [English claim-to-proof index](formalization/audit/claims.en.json) preserves the exact manuscript excerpts and proof bindings. The [release verification result](formalization/verification/verification.json) records the checks for that reference release; the [HTML report](formalization/report.html) presents that release evidence.

The reference imported upstream source closure contains **eight unused proof placeholders**. None occurs in the transitive axiom dependencies of the reference audited named project declarations. The Palomar `Challenge.lean` separately contains the two intentional theorem holes that `Solution.lean` must discharge; these are statement specifications, not completed proofs. The [trust-boundary discussion](docs/FORMALIZATION.md#trust-boundary-and-ai-assisted-review) explains this distinction, the role of AI-assisted review, and what the kernel check guarantees.

The verified manuscript incorporates [five disclosed revisions](docs/FORMALIZATION.md#manuscript-revisions). The coverage claim concerns this revised text, not the superseded proof passages.

## Build and check

Install Lean's `elan` toolchain manager, Git, and Python 3.11 or later. From the repository root:

```sh
cd formalization
lake exe cache get
lake build
```

The project selects its pinned Lean toolchain automatically. The [Palomar guide](docs/PALOMAR.md#reproduce-the-checks) gives the source checks and official Linux preflight; `lake build` alone does not certify a Palomar submission. The frozen `verify_release.py` and [reference release instructions](docs/FORMALIZATION.md#reproducing-the-checks) apply only to commit `6a7eebe7311a0bd52c1e59c0b1b7150c7bee6137`. Run them in a separate checkout of that commit to reproduce historical evidence.

| Dependency | Pinned version |
|---|---|
| Lean | `leanprover/lean4:v4.35.0-rc2` |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Stochastic dependencies | 92 compatibility modules with [fixed upstream provenance](formalization/vendor/stochastic/provenance.json) |

The complete dependency graph is recorded in [`lake-manifest.json`](formalization/lake-manifest.json).

## Repository contents

- [`main.pdf`](main.pdf) and [`main.tex`](main.tex): the accompanying manuscript.
- [`references.bib`](references.bib) and [`autart.cls`](autart.cls): bibliography and manuscript class.
- [`formalization/LinearStochastic/`](formalization/LinearStochastic): Lean proof modules.
- [`formalization/Challenge.lean`](formalization/Challenge.lean) and [`Solution.lean`](formalization/Solution.lean): independent Palomar statement and its proof.
- [`formalization/LinearStochastic.lean`](formalization/LinearStochastic.lean): aggregate import of all project modules.
- [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md): theorem entry points, module map, conventions, and verification scope.

The public companion presents reproducible proofs and release evidence. Internal development snapshots and machine-specific review paths are not part of the public layout.

Original software is licensed under [Apache-2.0](LICENSE); see [NOTICE](NOTICE) for scope and attribution. Dependencies and redistributed third-party material retain their respective licenses and notices. In particular, MathFin's Apache 2.0 terms and attribution notices remain applicable to reused or adapted MathFin material; this documentation does not relicense the manuscript, journal class, or dependencies.
