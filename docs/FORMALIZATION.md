# Formalization guide

The release counts and reproduction commands in this guide describe reference
commit `6a7eebe7311a0bd52c1e59c0b1b7150c7bee6137` (Lean `v4.33.0-rc1`).
For the Lean `v4.35.0-rc2` port and independent submission interface, use the
[Palomar preparation guide](PALOMAR.md). Historical reports are retained as
evidence of the reference release, not reissued for the port.

This guide connects the manuscript's statements to their Lean proofs and explains how to interpret the verification results. The main mathematical setting is a finite-dimensional, constant-coefficient linear stochastic system driven by multidimensional Brownian motion, with controls in both drift and diffusion.

The reference verification covers **80 inventoried mathematical claims**, including **18 named statements**, across **384 project modules**. It checks **2,559 explicitly named declarations**, of which **2,015 are theorems or lemmas**. These counts describe one checked snapshot; they are not a substitute for the individual statement correspondence.

## Mathematical scope

The final controllability theorems use the original finite real matrices $A,B,C_j,D_j$, a complete probability space, and the usual augmentation of the joint Brownian natural filtration. The paper assumes positive state, input, and noise dimensions and a positive horizon. Some algebraic or stochastic helper results allow additional zero-dimensional cases.

The definitions quantify over ordinary progressively measurable controls with finite expected squared energy. Reachability is stated using actual continuous $S^2$ solution paths. Approximation uses mean-square terminal error, and exact controllability quantifies over every square-integrable terminal target measurable at the final time.

These interfaces are connected by proofs to the predictable $H^2$ classes used internally to construct stochastic integrals. The final classification does not assume a martingale representation theorem, a BSDE existence theorem, exact null controllability, or a small-time contraction condition as an unproved input. The necessary constructions and bridges are supplied by preceding modules. Intermediate lemmas often expose such hypotheses to separate their mathematical roles; use the final entry points below when comparing the result with the paper.

## Principal theorem entry points

All declaration names in this table have the prefix `LinearStochastic.`. Manuscript labels are used instead of page-dependent theorem numbers.

| Manuscript statement | Lean entry point | Source |
|---|---|---|
| `lem:flag`: obstruction flag and maximal invariant subspace | `AdjointCoefficients.matrix_flag_lemma` | [AlgebraFlag](../formalization/LinearStochastic/AlgebraFlag.lean) |
| `thm:geometry`: all four controllability properties | `RawCompleteClassification.classification` | [RawCompleteClassification](../formalization/LinearStochastic/RawCompleteClassification.lean) |
| `thm:null-feedback`: null feedback on every positive horizon | `UsualNullFeedbackTheorem.paper_theorem` | [NullFeedbackTheorem](../formalization/LinearStochastic/NullFeedbackTheorem.lean) |
| `thm:rank`: explicit block rank and flag codimension | `Coordinates.finitePair_rank_codimension` | [AlgebraCoordinates](../formalization/LinearStochastic/AlgebraCoordinates.lean) |
| `cor:rank-control`: rank criteria for controllability | `RawRankCriteria.null_rank`, `RawRankCriteria.exact_rank` | [RawRankCriteria](../formalization/LinearStochastic/RawRankCriteria.lean) |
| `prop:exact-rank`: finite word-matrix criterion | `RawRankCriteria.exact_word_rank` | [RawRankCriteria](../formalization/LinearStochastic/RawRankCriteria.lean) |
| `lem:approximate`: approximate controllability and the obstruction | `RawBrownianClassification.matrix_classification` | [RawBrownianClassification](../formalization/LinearStochastic/RawBrownianClassification.lean) |
| `lem:arbitrary-rate`: strict LMI feasibility | `LMIMatrixCoordinates.arbitrary_rate_positive_matrix_feasible` | [LMIMatrixCoordinates](../formalization/LinearStochastic/LMIMatrixCoordinates.lean) |
| `lem:tarski-seidenberg`: finite real projection | `RealQEFiniteProjection.exists_finite`, `RealQEFiniteProjection.forall_finite` | [RealQEFiniteProjection](../formalization/LinearStochastic/RealQEFiniteProjection.lean) |
| `lem:semialgebraic-growth`: polynomial growth | `SemialgebraicCoordinates.continuous_semialgebraic_growth` | [SemialgebraicCoordinates](../formalization/LinearStochastic/SemialgebraicCoordinates.lean) |
| `lem:growth`: polynomial feedback bounds | `PolynomialFeedbackGrowth.zero_flag_polynomial_feedback` | [PolynomialFeedbackGrowth](../formalization/LinearStochastic/PolynomialFeedbackGrowth.lean) |
| `prop:staircase`: termination and actual controllability output | `StaircaseFirstStop.matrix_first_stop` | [StaircaseFirstStop](../formalization/LinearStochastic/StaircaseFirstStop.lean) |

The examples and remarks have separate proofs rather than being inferred from a coverage count:

| Topic | Useful modules |
|---|---|
| Singular diffusion example and the nonrobust family | [AlgebraExamples](../formalization/LinearStochastic/AlgebraExamples.lean), [StochasticExamples](../formalization/LinearStochastic/StochasticExamples.lean), [StochasticExactExamples](../formalization/LinearStochastic/StochasticExactExamples.lean) |
| Exact terminal controllability and deterministic initial values | [RawExactProperties](../formalization/LinearStochastic/RawExactProperties.lean), [BrownianInitialTrivial](../formalization/LinearStochastic/BrownianInitialTrivial.lean), [MatrixExactTerminal](../formalization/LinearStochastic/MatrixExactTerminal.lean) |
| Deterministic reduction, classical ODE controls, and delayed targets | [StochasticDeterministicReduction](../formalization/LinearStochastic/StochasticDeterministicReduction.lean), [DeterministicODEBridge](../formalization/LinearStochastic/DeterministicODEBridge.lean), [BrownianGramianApproximation](../formalization/LinearStochastic/BrownianGramianApproximation.lean) |
| An approximating control family whose energies diverge | [BrownianDelayedEnergy](../formalization/LinearStochastic/BrownianDelayedEnergy.lean) |
| The drift image of the diffusion kernel and the input-dimension bound | [InputStructure](../formalization/LinearStochastic/InputStructure.lean), [StochasticInputStructure](../formalization/LinearStochastic/StochasticInputStructure.lean) |
| Canonical diffusion right inverse and kernel projection | [AlgebraSurjective](../formalization/LinearStochastic/AlgebraSurjective.lean), [InputStructure](../formalization/LinearStochastic/InputStructure.lean) |

## Module map

The source imports are the authoritative dependency graph. The following groups provide a reading route through it.

| Layer | Main modules or families | What is proved |
|---|---|---|
| Linear algebra | `AlgebraFlag`, `AlgebraRank`, `AlgebraBlocks`, `AlgebraCoordinates`, `AlgebraFlagTransport` | Subspace recursion, linear selectors, finite stabilization, rank identities, literal matrix coordinates, and change of coordinates. |
| Finite words and elimination | `AlgebraWords`, `AlgebraWordMatrices`, `AlgebraSurjective`, `AlgebraSurjectiveMatrices`, `AlgebraStaircase`, `StaircaseFirstStop` | Invariant word spans, canonical surjective-diffusion reduction, orthogonal frame updates, and the first return within the stated iteration bound. |
| Polynomial and spectral structure | `BlockPolynomial`, `SpectralNullspace`, `TallQRElimination`, `SquareSVD`, `SVDResidual`, `NumericalRank` | Polynomial entries of the block recursion, exact QR/SVD constructions, retained and removed subspaces, and the specified numerical-rank convention. |
| Real algebra and LMI growth | `RealQE*`, `Semialgebraic*`, `PrincipalMinors`, `Minimum*`, `LMICoefficients`, `LMIMatrixCoordinates`, `PolynomialFeedbackGrowth` | Real quantifier elimination, semialgebraic closure and growth, genuine matrix feasibility and optimization, and polynomial bounds for feedback. |
| Stochastic integration | `CommonIto*`, `CommonVector*`, `ProgressivePredictable`, `InitialExpectedProduct`, `SectionSolution*` | Common-filtration stochastic integrals, independent channels, continuous versions, energy identities, and measurable process-class bridges. |
| Forward and backward equations | `CommonGlobal*`, `HilbertBrownian*`, `JointUsualRepresentation`, `JointUsualShiftRepresentation`, `BSDE*`, `RawBSDE*` | Actual all-horizon SDE/BSDE solutions, representation on the usual filtration, global uniqueness, and vector-coordinate equivalence. |
| Full-path estimates and duality | `HilbertFullS2Bound`, `HilbertS2Energy`, `BrownianRawDuality`, `GlobalObservationDuality`, `ProjectedNoiseEnergy` | Quantitative $S^2$ bounds, actual forward/backward pairings, and the zero-observation implication for the obstruction. |
| Feedback and final classification | `Switching*`, `RawSwitchingUniqueness`, `NullFeedbackTheorem`, `RawCompleteClassification`, `RawRankCriteria`, `StaircaseControlClassification` | A genuine admissible feedback control, endpoint zero, polynomial energy cost, and all four original controllability properties. |

For foundational entry points, see `JointUsualBrownianGlobal.exists_global_progressive_control`, `RawBSDEUniqueness.exists_and_unique`, `HilbertS2Energy.full_energy_bound`, and `BrownianRawDuality.usual_raw_duality`.

### Representation conventions

- Matrices are finite real matrices. `AdjointCoefficients.fromMatrices` inserts the actual transposes needed by the adjoint formulation.
- State and control energies use Euclidean norms and the corresponding $L^2$ norms. Coordinate changes are proved; a generic product norm is not silently substituted for the physical energy.
- The recursive index `k` in `AlgebraBlocks` corresponds to the manuscript's block index `k + 1`. The finite coordinate modules prove the row and column sizes and the rank correspondence.
- Empty rows and columns in intermediate matrices use the ordinary finite-dimensional rank convention. They do not remove the paper's positive system-dimension assumptions.
- Exact QR/SVD statements are mathematical factorization results. The numerical-rank module defines the stated singular-value threshold and proves its properties; it does not certify a floating-point implementation, LAPACK, rounding error, or equality between a tolerance-based classification and the exact classification.
- Some constructions, including the existence proof for quantifier elimination, are `noncomputable`. This is a classical existence formalization, not a claim that every theorem has been extracted into an executable numerical algorithm.

## Reproducing the checks

The repository pins Lean in [`lean-toolchain`](../formalization/lean-toolchain), direct dependencies in [`lakefile.toml`](../formalization/lakefile.toml), and every direct and transitive Lake package in [`lake-manifest.json`](../formalization/lake-manifest.json). Use these versions when reproducing the release.

With Lean's `elan` toolchain manager, Git, and Python 3.11 or later installed, run from the repository root:

```sh
cd formalization
lake exe cache get
lake build
cd ..
python3 formalization/scripts/verify_release.py --kernel-jobs 4
```

The first command obtains available compiled dependency caches. Building still checks the project against the pinned toolchain. The release verifier then checks the source/evidence correspondence, builds the whole project, replays every project module, and inspects the named declarations and their transitive axiom dependencies. Successful compilation alone does not establish manuscript coverage.

Kernel replay uses the unchanged command

```sh
lake env leanchecker --verbose LinearStochastic.RawCompleteClassification
```

with each exact project module name in turn. The release verifier bounds the number of simultaneous processes; `--kernel-jobs 4` changes scheduling, not the proof checker. Use fewer workers on a machine with limited memory. A successful release check requires a zero exit status and the correct replay marker for each module, complete module coverage, and no unapproved axiom dependencies.

To inspect a main theorem in a Lean editor, use:

```lean
import LinearStochastic.RawCompleteClassification

#check @LinearStochastic.RawCompleteClassification.classification
#print axioms LinearStochastic.RawCompleteClassification.classification
```

The leading `@` exposes implicit arguments, which is useful when reviewing the hypotheses. To check another entry point, import its source module and replace the declaration name.

The manuscript uses pdfLaTeX and BibTeX. From the repository root, a standard build sequence is:

```sh
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

The manuscript build and the Lean check have different purposes: the former produces the PDF; the latter checks the formal mathematics and its recorded correspondence with the source.

## Manuscript revisions

The formalization process led to five disclosed revisions of the accompanying manuscript. Its mathematical coverage is tied to the revised source. Superseded proof passages are not presented as formally verified.

1. **Arbitrary-rate LMI feasibility.** The proof was replaced by a finite-dimensional cone-separation argument, a positive dual certificate, and the contradiction between a nonzero certificate and the vanishing obstruction.
2. **Positive system dimensions.** The formulation now explicitly assumes positive integers $n,r,m$. Empty row and column conventions apply to intermediate matrices. This is a scope clarification, and the verification does not claim that the final stochastic classification covers excluded degenerate system dimensions.
3. **Necessity of full joint diffusion rank for EC.** The proof now uses actual small-time Picard estimates and a terminal-spike contradiction, connected to the genuine bounded terminal operator and the open mapping argument.
4. **Closed-loop mean-square decay.** The proof now uses an expected product identity for actual solutions followed by an exponential comparison. The older pathwise differential/localization passage is not part of the coverage claim.
5. **Projected diffusion energy.** The zero-energy step now follows from a directly proved zero-coefficient statement. The accompanying general pathwise quadratic-variation identification was removed rather than being treated as implicitly formalized.

The reference checked manuscript has SHA-256

```text
8ccc417fa3629e23e0b9dba2cd499916ccc9369201a9bec28f1538d298cb39ea
```

A later source revision needs a new source binding and any mathematical review required by its changes. A matching title, a previous successful build, or an edited status field does not transfer the verification result to a new manuscript.

## Trust boundary and AI-assisted review

There are two different questions: whether Lean accepts a proof of a precise formal proposition, and whether that proposition faithfully expresses the intended manuscript claim.

**Proof checking.** The project forbids `sorry`, `admit`, project-defined axioms, unsafe proof shortcuts, and native-evaluation proof bypasses. The audited named declaration closures allow only `propext`, `Classical.choice`, and `Quot.sound`. Lean's kernel checks the proof terms relative to this logical foundation and the imported environment.

All 384 project modules were additionally replayed using the pinned toolchain's `leanchecker`. This includes generated constructors, projections, recursors, anonymous instances, and private helpers, beyond the explicit declaration inventory. `leanchecker` uses Lean's own kernel; it is not a second independently implemented proof checker. The procedure replays each project's declarations against its imports and does not claim a replay of all of Mathlib from an empty environment.

**Statement correspondence.** AI agents developed proofs and separately reviewed their types, assumptions, and correspondence with the manuscript. Authors did not approve their own contributions. The claim mapping covers mathematical assertions in definitions, algorithms, examples, remarks, and supporting arguments as well as named theorems. AI reviews are fallible judgments; they are not added logical axioms, an independent kernel, or a guarantee against every translation mistake. Readers can inspect the actual theorem types through the entry points above.

**Upstream placeholders.** The pinned full source-import closure contains eight unused `sorry` sites:

| Upstream module | Sites |
|---|---:|
| `BrownianMotion.StochasticIntegral.DoobLp` | 2 |
| `BrownianMotion.StochasticIntegral.LocalMartingale` | 1 |
| `BrownianMotion.StochasticIntegral.OptionalSampling` | 1 |
| `BrownianMotion.StochasticIntegral.UniformIntegrable` | 4 |

This is an import-source fact, distinct from proof dependency. None of the 2,559 audited named project declarations has `sorryAx` in its transitive axiom dependencies. The imported source closure is therefore not globally placeholder-free, while the audited project results do not rely on those placeholders. A new dependency on `sorryAx` must fail the axiom check.

The guarantee remains conditional on the correctness of Lean's kernel and the software and hardware that execute it, together with the stated logical foundation. It concerns the formal mathematical propositions and their reviewed correspondence. It does not certify historical attribution, bibliography, acknowledgments, commented-out manuscript passages, or numerical software implementations.

MathFin and the other dependencies retain their existing licenses. Preserve applicable copyright notices, Apache 2.0 notices for reused MathFin material, and the separate terms of the manuscript class. No blanket relicensing is asserted here.
