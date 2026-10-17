# Reusing the Lean development

This guide is a search and integration map for researchers and AI coding agents.
The theorem types in the source are authoritative. Start with an existing
result, inspect its hypotheses, and import its module before developing a new
proof of the same fact.

## Declaration index

Every declaration below has the prefix `LinearStochastic.`. Module names in the
first column are imported as `LinearStochastic.<module>`.

| Module | Declaration suffix | Reuse and scope |
| --- | --- | --- |
| [CommonItoCLM](../formalization/LinearStochastic/CommonItoCLM.lean) | `CommonItoCLM.itoIntegralCLM_T` | Scalar L² Itô integral as a continuous linear map for a specified filtration. |
| [CommonItoMultichannel](../formalization/LinearStochastic/CommonItoMultichannel.lean) | `CommonItoMultichannel.sumIntegral_norm_sq` | Multichannel integral isometry under the stated independence hypotheses. |
| [CommonItoContinuousVersion](../formalization/LinearStochastic/CommonItoContinuousVersion.lean) | `CommonItoContinuousVersion.exists_continuous_martingale_modification` | Continuous martingale modification of the integral process. |
| [ProgressivePredictable](../formalization/LinearStochastic/ProgressivePredictable.lean) | `ProgressivePredictable.exists_predictable_Lp_of_progressive` | Predictable Lp representative of a progressive process on a finite horizon. |
| [JointUsualRepresentation](../formalization/LinearStochastic/JointUsualRepresentation.lean) | `JointUsualRepresentation.represented` | Brownian representation on the usual joint natural filtration; this entry assumes every sample path is continuous. |
| [JointUsualBrownianGlobal](../formalization/LinearStochastic/JointUsualBrownianGlobal.lean) | `JointUsualBrownianGlobal.exists_global_progressive_control`, `JointUsualBrownianGlobal.global_unique` | Constant-matrix controlled SDE existence and uniqueness on arbitrary finite horizons, with original almost surely continuous Brownian drivers. |
| [RawBSDEUniqueness](../formalization/LinearStochastic/RawBSDEUniqueness.lean) | `RawBSDEUniqueness.exists_and_unique` | Linear BSDE solutions with terminal L² data; the Hilbert space is equipped with a finite orthonormal basis. |
| [HilbertS2Energy](../formalization/LinearStochastic/HilbertS2Energy.lean) | `HilbertS2Energy.full_energy_bound` | Full-path energy estimate for the stated controlled system. |
| [BrownianRawDuality](../formalization/LinearStochastic/BrownianRawDuality.lean) | `BrownianRawDuality.usual_raw_duality` | Actual forward/backward SDE pairing on the usual Brownian filtration. |
| [AlgebraFlag](../formalization/LinearStochastic/AlgebraFlag.lean) | `AdjointCoefficients.flag_stable_at_finrank`, `AdjointCoefficients.flag_greatest_fixed_point`, `AdjointCoefficients.matrix_flag_lemma` | Finite stabilization, greatest fixed subspace, and the original-matrix formulation. |
| [AlgebraCoordinates](../formalization/LinearStochastic/AlgebraCoordinates.lean) | `Coordinates.finitePair_rank_codimension` | Explicit finite block-matrix rank difference equals the flag codimension. |
| [AlgebraSurjective](../formalization/LinearStochastic/AlgebraSurjective.lean) | `SurjectiveReduction.canonical_flag_bot_iff` | Surjective-diffusion reduction to the full word-span condition. |
| [RealQEFiniteProjection](../formalization/LinearStochastic/RealQEFiniteProjection.lean) | `RealQEFiniteProjection.exists_finite`, `RealQEFiniteProjection.forall_finite` | Existential and universal elimination of a finite block of real coordinates. |
| [SemialgebraicCoordinates](../formalization/LinearStochastic/SemialgebraicCoordinates.lean) | `SemialgebraicCoordinates.continuous_semialgebraic_growth` | Polynomial bound on `[1, ∞)` for a continuous function with semialgebraic graph. |
| [LMIMatrixCoordinates](../formalization/LinearStochastic/LMIMatrixCoordinates.lean) | `LMIMatrixCoordinates.arbitrary_rate_positive_matrix_feasible` | Strict matrix LMI feasibility under the zero-obstruction assumptions. |
| [PolynomialFeedbackGrowth](../formalization/LinearStochastic/PolynomialFeedbackGrowth.lean) | `PolynomialFeedbackGrowth.zero_flag_polynomial_feedback` | Polynomial bounds for the feedback family when the obstruction vanishes. |
| [NullFeedbackTheorem](../formalization/LinearStochastic/NullFeedbackTheorem.lean) | `UsualNullFeedbackTheorem.paper_theorem` | Null feedback on every positive time horizon for the original stochastic system. |
| [SquareSVD](../formalization/LinearStochastic/SquareSVD.lean) | `SquareSVD.decomposition` | Exact SVD expansion for equal-dimensional finite real inner-product spaces. |
| [TallQRElimination](../formalization/LinearStochastic/TallQRElimination.lean) | `TallQRElimination.qr_factorization` | Exact tall QR factorization with explicit dimension constraints. |
| [StaircaseFirstStop](../formalization/LinearStochastic/StaircaseFirstStop.lean) | `StaircaseFirstStop.matrix_first_stop` | First stopping step of the matrix staircase within the finite dimension bound. |
| [RawCompleteClassification](../formalization/LinearStochastic/RawCompleteClassification.lean) | `RawCompleteClassification.classification` | All four controllability properties in the original matrix/process formulation. |

For a wider map, including examples, deterministic reductions, and coordinate
transport, see the [formalization guide](FORMALIZATION.md#module-map).

## Imports and project layout

The repository root contains the manuscript; **the Lake package root is
`formalization/`**. Run Lean commands there with the pinned toolchain and
manifest. The simplest way to inspect or extend a theorem is to build this
checkout and add a small Lean file inside that project.

```lean
module
import LinearStochastic.RawBSDEUniqueness
import LinearStochastic.RealQEFiniteProjection

#check @LinearStochastic.RawBSDEUniqueness.exists_and_unique
#check @LinearStochastic.RealQEFiniteProjection.exists_finite
#print axioms LinearStochastic.RawBSDEUniqueness.exists_and_unique
```

Use `lake env lean YourFile.lean` to check such a file. The `@` exposes implicit
arguments, including typeclass and dimension assumptions. Use `#print` on a
referenced definition when the statement hides the object you need to compare.
Prefer the narrow source import; `import LinearStochastic` is the aggregate of
all 384 core modules and is useful for broad exploration.

For a downstream Lake project, pin an exact repository commit, select the
`formalization` subdirectory as its package root, and align Lean and Mathlib
with this project's pins. Preserve `vendor/stochastic` and the contained path
dependency declared in `lakefile.toml`; copying one source file is not a
standalone installation. Check the downstream build after integration: local
project checks do not certify every consumer's dependency graph. The vendor
package is a compatibility subset, not the complete upstream MathFin or
BrownianMotion library. Its [provenance](../formalization/vendor/stochastic/provenance.json)
identifies the original source of each adapted module.

`Challenge` and `Solution` are separate Palomar environments with corresponding
declaration names. **Do not import `Challenge` into a proof consumer, or combine
it with `Solution` / `PalomarDefinitions`.** Challenge intentionally contains
theorem holes and repeats the independent definitions. For the proved Palomar
interface, import `Solution` and inspect
`LinearStochastic.Palomar.classification` or
`LinearStochastic.Palomar.ito_unique`. For ordinary reuse, the core modules in
the table are usually the more direct interfaces.

## Match the mathematical setting

- Common-filtration integration uses
  `CommonItoIsometry.ForwardIndependent`, which asserts adaptedness and
  independence of the whole future increment process. Brownian marginal laws
  alone do not supply this instance for an arbitrary enlarged filtration.
  `JointUsualBrownianGlobal.coordinateForward` constructs it in the usual
  joint Brownian setting.
- Stochastic time is usually `ℝ≥0`. Predictable integrands use L² classes for a
  trimmed time/probability measure on `(0,T]`; raw controlled solutions also
  retain actual progressive processes and almost surely continuous paths.
  Use the proved representative/coordinate bridges when moving between them.
- Distinguish almost-sure equality at each fixed time from equality on one
  probability-one event at every time. Some intermediate representation
  results require everywhere-continuous versions; the raw Brownian solution
  modules supply the corresponding version transport.
- The final control results concern finite-dimensional, constant-coefficient
  linear systems. Their general-looking helper types do not establish
  nonlinear SDE, arbitrary-filtration, infinite-dimensional, or SPDE results.
  Check finite-basis, completeness, integrability, independence, and positive
  horizon assumptions in the exact theorem you use.
- The algebraic layers often have more general scalar/vector-space hypotheses
  than the final real-matrix theorem. Inspect their signatures rather than
  adding the stochastic assumptions to an algebra-only argument.
- Semialgebraicity is defined by `SemialgebraicCoordinates.IsSemialgebraic`.
  Establish correspondence before substituting another library's predicate.
  Quantifier elimination and exact QR/SVD include classical, noncomputable
  constructions; they are not verified floating-point solvers.

## Check and credit the reused result

After adapting an argument, compile the consumer and inspect the new theorem's
transitive axioms with `#print axioms`. The project's inspected closures use
only `propext`, `Classical.choice`, and `Quot.sound`; eight inherited vendor
placeholders are outside those closures. A new import or theorem can have a
different closure, so the existing report is not a blanket certificate for a
new result. Follow the [current checking guide](PALOMAR.md#reproduce-the-checks)
for broader checks. The frozen reference release verifier belongs to its
recorded historical commit.

Retain the [license and attribution notices](../NOTICE). Cite the exact commit,
module, and declaration you reuse, and preserve the recorded upstream credits.
The [AI use disclosure](../README.md#ai-use-disclosure) applies to this project's
formalization; kernel acceptance and correspondence to an intended mathematical
claim remain distinct questions.
