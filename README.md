# Lean formalization of stochastic controllability criteria

This repository is the Lean 4 companion to **A Unified Kalman-Type Classification of Controllability for Linear Stochastic Systems**, by **Qi Lü and Yu Wang**.

It contains the manuscript and formal proofs of its mathematical claims, including the stochastic analysis, finite-dimensional algebra, semialgebraic arguments, feedback construction, and elimination algorithm needed for the main results.

**Read the [paper](main.pdf), explore the [English verification report](formalization/report.html), browse the [Lean sources](formalization/LinearStochastic), or start with the [formalization guide](docs/FORMALIZATION.md).**

## Main result

For the constant-coefficient system

$$
dy=(Ay+Bu)\,dt+\sum_{j=1}^{m}(C_jy+D_ju)\,dW^j,
$$

the paper constructs a decreasing sequence of subspaces whose terminal value is the obstruction $V_\ast=V_n$. On every positive time horizon,

$$
\mathrm{AC}\iff\mathrm{ANC}\iff\mathrm{ENC}\iff V_\ast=\{0\},
$$

and

$$
\mathrm{EC}\iff V_\ast=\{0\}\ \text{and}\ \operatorname{rank}\mathcal D=mn,
\qquad
\mathcal D=\begin{bmatrix}D_1\\\vdots\\D_m\end{bmatrix}.
$$

Here AC and ANC mean approximate controllability and approximate null controllability; EC and ENC are their exact counterparts. The formal statements use ordinary progressively measurable finite-energy controls, the original Brownian motion with its usual augmented natural filtration, and actual continuous square-integrable solution paths. Terminal targets range over all corresponding square-integrable random variables.

The central entry point is [`LinearStochastic.RawCompleteClassification.classification`](formalization/LinearStochastic/RawCompleteClassification.lean). Further results provide explicit rank tests, deterministic time-dependent null feedback with polynomial small-time energy cost, and an equivalent orthogonal elimination procedure.

## Verification status

The reference verification of the accompanying revised manuscript passed:

| Check | Result |
|---|---:|
| Inventoried mathematical claims | 80 / 80 covered |
| Named manuscript statements | 18 / 18 covered |
| Project modules built and individually replayed through Lean's kernel | 384 / 384 |
| Explicitly named declarations checked | 2,559 |
| Of these, theorems and lemmas | 2,015 |
| Unapproved axioms in their transitive dependencies | 0 |

Coverage is determined by a claim-by-claim comparison with the manuscript, not by the number of Lean declarations. The proof sources contain no `sorry`, `admit`, or project-defined axioms. The audited declaration dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.

The [English claim-to-proof index](formalization/audit/claims.en.json) preserves the exact manuscript excerpts and proof bindings. The [release verification result](formalization/verification/verification.json) records the checks for the public checkout; the [HTML report](formalization/report.html) presents that release evidence.

The full imported upstream source closure does contain **eight unused proof placeholders**. None occurs in the transitive axiom dependencies of the audited named project declarations. The [trust-boundary discussion](docs/FORMALIZATION.md#trust-boundary-and-ai-assisted-review) explains this distinction, the role of AI-assisted review, and what the kernel check guarantees.

The verified manuscript incorporates [five disclosed revisions](docs/FORMALIZATION.md#manuscript-revisions). The coverage claim concerns this revised text, not the superseded proof passages.

## Build and check

Install Lean's `elan` toolchain manager, Git, and Python 3.11 or later. From the repository root:

```sh
cd formalization
lake exe cache get
lake build
cd ..
python3 formalization/scripts/verify_release.py --kernel-jobs 4
```

The toolchain and all Lake dependencies are pinned. The release verifier performs the checks described in the [formalization guide](docs/FORMALIZATION.md#reproducing-the-checks); `lake build` alone is not the complete release check. Use `--kernel-jobs 1` or `2` if memory is limited. Each worker loads a substantial dependency environment.

| Dependency | Pinned version |
|---|---|
| Lean | `leanprover/lean4:v4.33.0-rc1` |
| Mathlib | `0434c03386d3e7f7fd3ed95754543eabe4ab251b` |
| MathFin | `99b836298731c432a6242fdb6cb51c1c97f37902` |

The complete dependency graph is recorded in [`lake-manifest.json`](formalization/lake-manifest.json).

## Repository contents

- [`main.pdf`](main.pdf) and [`main.tex`](main.tex): the accompanying manuscript.
- [`references.bib`](references.bib) and [`autart.cls`](autart.cls): bibliography and manuscript class.
- [`formalization/LinearStochastic/`](formalization/LinearStochastic): Lean proof modules.
- [`formalization/LinearStochastic.lean`](formalization/LinearStochastic.lean): aggregate import of all project modules.
- [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md): theorem entry points, module map, conventions, and verification scope.

The public companion presents reproducible proofs and release evidence. Internal development snapshots and machine-specific review paths are not part of the public layout.

Dependencies and redistributed third-party material retain their respective licenses and notices. In particular, MathFin's Apache 2.0 terms and attribution notices remain applicable to reused or adapted MathFin material; this documentation does not relicense the manuscript, journal class, or dependencies.
