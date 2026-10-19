# Lean formalization of stochastic controllability criteria

Lean 4 companion to **A Unified Kalman-Type Classification of Controllability for Linear Stochastic Systems**, by **Qi Lü and Yu Wang**.

Alongside the manuscript and its controllability proofs, this repository provides reusable Lean components for stochastic integration, linear SDEs and BSDEs, finite-dimensional linear algebra, semialgebraic geometry, and feedback control.

**[Paper](main.pdf) · [Reuse guide for researchers and AI agents](docs/REUSE.md) · [Theorem map](docs/FORMALIZATION.md#principal-theorem-entry-points) · [Palomar registration](https://palomar-registry.org/entry?id=PALOMAR-2026-10-19-000002&version=1) · [Verification details](docs/PALOMAR.md)**

## What you can reuse

The Lake project is in [`formalization/`](formalization), and project declarations generally live in the `LinearStochastic` namespace. Start with a specific module below; inspect its theorem signatures before reconstructing a result from scratch. These are proof-library components, with hypotheses to satisfy, rather than a general-purpose numerical SDE solver.

| If you need… | Start here | Available building blocks |
| --- | --- | --- |
| Itô integration and process measurability | [CommonItoCLM](formalization/LinearStochastic/CommonItoCLM.lean), [CommonItoMultichannel](formalization/LinearStochastic/CommonItoMultichannel.lean), [ProgressivePredictable](formalization/LinearStochastic/ProgressivePredictable.lean) | Scalar L² integral maps, multichannel isometry, predictable representatives of progressive processes. |
| Brownian representation and linear SDE/BSDE solutions | [JointUsualRepresentation](formalization/LinearStochastic/JointUsualRepresentation.lean), [JointUsualBrownianGlobal](formalization/LinearStochastic/JointUsualBrownianGlobal.lean), [RawBSDEUniqueness](formalization/LinearStochastic/RawBSDEUniqueness.lean) | Representation on the usual Brownian filtration; finite-dimensional, constant-coefficient forward/backward existence and uniqueness. |
| Energy estimates and stochastic duality | [HilbertS2Energy](formalization/LinearStochastic/HilbertS2Energy.lean), [BrownianRawDuality](formalization/LinearStochastic/BrownianRawDuality.lean) | Full-path S² estimates and forward/backward pairing identities. |
| Invariant subspaces and algebraic rank tests | [AlgebraFlag](formalization/LinearStochastic/AlgebraFlag.lean), [AlgebraCoordinates](formalization/LinearStochastic/AlgebraCoordinates.lean), [AlgebraSurjective](formalization/LinearStochastic/AlgebraSurjective.lean) | Decreasing subspace flags, finite stabilization, rank/codimension identities, and surjective-diffusion reduction. |
| Semialgebraic projection and growth | [RealQEFiniteProjection](formalization/LinearStochastic/RealQEFiniteProjection.lean), [SemialgebraicCoordinates](formalization/LinearStochastic/SemialgebraicCoordinates.lean) | Finite real quantifier elimination and polynomial growth bounds for continuous semialgebraic functions on a ray. |
| Feedback, LMI feasibility, and elimination | [NullFeedbackTheorem](formalization/LinearStochastic/NullFeedbackTheorem.lean), [LMIMatrixCoordinates](formalization/LinearStochastic/LMIMatrixCoordinates.lean), [StaircaseFirstStop](formalization/LinearStochastic/StaircaseFirstStop.lean) | Null controls on positive horizons, strict matrix LMI feasibility, and finite staircase termination. |

The [reuse guide](docs/REUSE.md) gives exact declaration names, import examples, representation conventions, and integration constraints. Many constructions are `noncomputable`; exact QR/SVD and rank results do not certify floating-point implementations. A Hilbert-space module name alone does not imply an infinite-dimensional or SPDE theorem.

## Build and inspect

Install Lean's `elan` toolchain manager and Git. From the repository root:

```sh
cd formalization
lake exe cache get
lake build
```

The project selects **Lean `v4.35.0-rc2`** and pins Mathlib to `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Keep the [Lake manifest](formalization/lake-manifest.json) and the [vendored stochastic dependencies](formalization/vendor/stochastic/README.md) together. The latter contain 92 compatibility modules with recorded upstream provenance, not complete copies of their upstream libraries.

For example, save this as `formalization/Inspect.lean` and run `lake env lean Inspect.lean` from `formalization/`:

```lean
module
import LinearStochastic.AlgebraFlag
import LinearStochastic.SemialgebraicCoordinates

#check @LinearStochastic.AdjointCoefficients.matrix_flag_lemma
#check @LinearStochastic.SemialgebraicCoordinates.continuous_semialgebraic_growth
#print axioms LinearStochastic.AdjointCoefficients.matrix_flag_lemma
```

For proof reuse, import the relevant `LinearStochastic.*` module. `Challenge.lean` is an isolated submission specification with intentional theorem holes; it is not a proved library entry point. See the [reuse guide](docs/REUSE.md#imports-and-project-layout) for the separate role of `Solution.lean`.

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

## Verification and registration

- **Current port:** all 384 core modules build, and the 2,559 reference declarations plus the two Palomar entries passed the [local axiom check](formalization/palomar/local-check.json), using only `propext`, `Classical.choice`, and `Quot.sound`. Evidence is tied to the source hashes in each report.
- **Palomar registration:** registered on **2026-10-19** as [**PALOMAR-2026-10-19-000002, version 1**](https://palomar-registry.org/entry?id=PALOMAR-2026-10-19-000002&version=1). The entry covers `LinearStochastic.Palomar.classification` and `LinearStochastic.Palomar.ito_unique` at commit [`c088eb9943197e88c4b046223239d4c4f0180513`](https://github.com/MrGodfrey/LeanForCriteriaForLinearStochastic/tree/c088eb9943197e88c4b046223239d4c4f0180513), with [passed official mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39019880717). Registration and verification apply to that fixed source snapshot. [Verification details](docs/PALOMAR.md).
- **Manuscript coverage:** the [reference report](formalization/report.html) and [claim-to-proof index](formalization/audit/claims.en.json) record 80/80 claims at [`6a7eebe7311a`](https://github.com/MrGodfrey/LeanForCriteriaForLinearStochastic/tree/6a7eebe7311a0bd52c1e59c0b1b7150c7bee6137). They are historical evidence, not a new audit of every later commit.

Eight inherited dependency proof placeholders remain disclosed and are absent from the inspected declarations' transitive axiom closures. The two deliberate Challenge holes are separate specifications discharged by Solution. See [verification procedures](docs/PALOMAR.md#reproduce-the-checks) and [trust boundaries](docs/FORMALIZATION.md#trust-boundary-and-ai-assisted-review) for the scope of these checks.

## AI use disclosure

**AI agents generated and iteratively revised this project's Lean formalization and proof scripts under Yu Wang's direction**, working from the manuscript and existing mathematical libraries. AI agents also performed statement-correspondence reviews. OpenAI Codex was used for the toolchain migration, the Palomar statement/solution interface, repository preparation, and documentation.

This disclosure concerns the project's formalization work; it does not attribute the manuscript or upstream Lean, Mathlib, MathFin, BrownianMotion, and KolmogorovExtension4 contributions to these agents. Original and adapted third-party code retains its authorship and notices. The formalization process also led to [five disclosed manuscript revisions](docs/FORMALIZATION.md#manuscript-revisions).

Proof acceptance comes from the recorded kernel checks. AI generation and AI review do not by themselves establish that a formal statement captures the intended mathematics, and are not independent human peer review. Yu Wang is the responsible maintainer. Historical model identities, costs, and complete prompt logs are not reconstructed; the available disclosures are in [formalization.yaml](formalization/formalization.yaml) and the [formalization guide](docs/FORMALIZATION.md#trust-boundary-and-ai-assisted-review).

## License and attribution

Original software is licensed under [Apache-2.0](LICENSE). Preserve the attribution and license notices in [NOTICE](NOTICE), including those for adapted MathFin material. The manuscript, journal class, and third-party materials retain their respective rights. When reusing a theorem, cite its declaration name and the exact repository commit, and retain the upstream provenance where applicable.
