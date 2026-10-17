# Palomar submission and verification

This work targets the **full stochastic controllability classification** in
manuscript Theorem `thm:geometry`. The reference release is commit
`6a7eebe7311a0bd52c1e59c0b1b7150c7bee6137`. Its release report does not certify a
later toolchain migration, a new statement interface, or Palomar registration.

The migration is installed in the normal source tree. Lean `v4.35.0-rc2`
builds all 384 core modules and the independent Challenge, bridge, and Solution.
The frozen reference evidence remains separate from the new local checks and
Linux preflight. The preparation branch was merged into `main` through
[PR #1](https://github.com/MrGodfrey/LeanForCriteriaForLinearStochastic/pull/1).

The verified candidate was **submitted to Palomar on 2026-10-17**, as submission
`bag3afqazkiq`. Palomar accepted the repository-write proof and started its
[official verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39019880717).
The [public submission record](../formalization/palomar/submission.json) records
the exact source and paths without access credentials. Verification and review
are in progress; submission is not registration. The private status link is
stored only in local Git metadata and must not be committed or published.

The complete sandboxed mechanical preflight **passed** for the public candidate
[`c088eb9943197e88c4b046223239d4c4f0180513`](https://github.com/MrGodfrey/LeanForCriteriaForLinearStochastic/tree/c088eb9943197e88c4b046223239d4c4f0180513).
The [successful workflow](https://github.com/MrGodfrey/LeanForCriteriaForLinearStochastic/actions/runs/39017801590)
uses Palomar's pinned official verifier in this repository. Its unmodified
[mechanical report](../formalization/palomar/mechanical-report.json) records
`status: pass`, `stage: complete`, and no errors or warnings. Comparator accepted
the exact statement correspondence, and con-ron, NanoDa, and Lean's default
kernel each accepted the solution. Challenge provenance has trust level `high`
with no untrusted sources. This is an advisory preflight, not Palomar editorial
acceptance or registration. The report is bound to the candidate SHA above;
later documentation or evidence commits do not change that binding.

## Requirements and evidence

The requirements were checked on 2026-10-17 against the
[official submission rules](https://palomar-registry.org/how-to-submit),
[binding policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
and official verifier at
[`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`](https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44).
The verifier source is authoritative when explanatory pages lag behind it.

| Requirement | Preparation evidence |
| --- | --- |
| Supported Lean | `v4.35.0-rc2` installed locally and selected by the project; old toolchain retained |
| Exactly matching canonical Mathlib | Migration pins `065356127b1dc0016f66b7283ce0ce2c4055aa55`, whose toolchain is `v4.35.0-rc2` |
| Fixed dependencies | Canonical Mathlib closure locked; 92 required stochastic modules vendored with original commits, licenses, file hashes and a complete patch |
| Module headers and file limits | All 485 Lean source files use the module system; no file exceeds 10,000 lines |
| Local build and axiom inspection | Passed: 9,415 build tasks; all 2,559 reference declarations and both advertised entries use only `propext`, `Quot.sound`, and `Classical.choice`; [report](../formalization/palomar/local-check.json) |
| Independent Challenge | Imports only `Mathlib`; 211 lines / 11,459 bytes; compilation passed |
| Proved Solution and exact comparison | Passed the official sandboxed Comparator for both advertised declarations |
| Root SPDX licence | Apache-2.0 `LICENSE`, with scope and third-party notices in `NOTICE`; independently detected as Apache-2.0 by the official workflow |
| Structured provenance | `formalization/formalization.yaml` passed the official metadata parser |
| Full mechanical preflight | Passed for `c088eb9943197e88c4b046223239d4c4f0180513`: exact comparison and con-ron, NanoDa, and Lean kernel acceptance |
| Public immutable snapshot | Preparation merged into `main`; the submitted candidate SHA is recorded above and in the mechanical report |
| Official submission | Accepted as `bag3afqazkiq` on 2026-10-17; official verification and review in progress |
| Registration | Not yet registered; the eventual review and registration decision are separate from submission |

The manuscript, `autart.cls`, and third-party material retain their existing
rights. The software licence does not relicense those materials.

## Independent mathematical interface

The statement specifies the original matrices, a complete probability space,
independent real Brownian coordinates, their usual augmented joint natural
filtration, ordinary progressive controls of finite energy, and continuous
states with square-integrable path suprema. It quantifies over all
square-integrable terminal targets measurable at the terminal time.

The scalar Itô integral is described as a continuous linear map on predictable
L² integrands agreeing with the explicit Brownian increment sum on every
bounded step process. Existence is part of the advertised classification;
a second advertised theorem asserts uniqueness. No opaque controllability
predicate or unconstrained integral definition hole is used. The solution
proves that this interface agrees with the existing raw SDE predicates before
applying `RawCompleteClassification.classification`.

The two intended Comparator declarations are
`LinearStochastic.Palomar.classification` and
`LinearStochastic.Palomar.ito_unique`. No replacement of the main stochastic
result by a supporting algebraic lemma is intended. Both statements and the
solution have passed Lean compilation, exact export comparison, and the three
kernel checks in the Linux workflow. Supplementary macOS replay results are
recorded separately in [native-kernel-check.json](../formalization/palomar/native-kernel-check.json).

## Port scope and remaining review

The 384 original core modules now use `module`, public imports, and explicit
public declaration visibility. Proof ports update Mathlib's `MemLp`,
uniform-integrability, measurability, and càdlàg APIs. The general helpers
`product_ae_of_horizon_indistinguishable`, `progressive_spacetime_measurable`,
and `energy_iff_memLp` now state an `SFinite` measure assumption required by
the new product-measure API. All their probability-space callers satisfy it;
the main classification's hypotheses are unchanged.

The algebraic criterion is an explicit recursion of sets of state vectors,
with no structure-proof fields in the Challenge. `flag_eq_original` and
`flag_zero_iff` prove that it is precisely the carrier and vanishing criterion
of the original submodule flag. The remaining independently stated definitions
are connected by proved equivalences in `PalomarBridge.lean`. This is an agent-prepared interface and remains open
to mathematical and editorial review. The local check is evidence about
specified source hashes, not a renewed claim-by-claim review of all 80 paper
claims. The two Challenge holes are intentional specifications. The eight
inherited dependency holes are disclosed; none occurs in the inspected
2,561 declarations' transitive axiom closures.

## Reproduce the checks

The local structural checker uses the official parser and scanner, not a
second independently invented policy. From the repository root, obtain the
pinned checker in a disposable directory:

```sh
git clone https://github.com/PalomarRegistry/PalomarSubmission.git .lake/PalomarSubmission
git -C .lake/PalomarSubmission checkout d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44
python3 -m venv .lake/palomar-checker-env
.lake/palomar-checker-env/bin/python -m pip install --require-hashes -r .lake/PalomarSubmission/requirements.txt
.lake/palomar-checker-env/bin/python formalization/scripts/check_palomar.py --pipeline .lake/PalomarSubmission
```

A successful structural check is not a proof check. It deliberately lists
unchecked requirements and does not report the repository as submission-ready.

The new toolchain can be installed alongside the reference toolchain:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
```

Build with `lake exe cache get` and `lake build` in `formalization/`.
From the repository root, `python3 formalization/scripts/check_port.py`
rebuilds and checks the transitive axioms of the 2,559 reference declarations
and the two advertised Palomar declarations. Its new report is
`formalization/palomar/local-check.json`; build and inspection logs are in
`formalization/.lake/palomar-checks/`. It rejects incomplete output, forbidden
axioms, changed inputs, and modified pinned Git dependencies. This check does
not replace Comparator or independent kernel replay.
Do not edit old audit hashes or pass flags to turn historical evidence into a
new verification result. The frozen `verify_release.py` belongs to the
reference release and enforces that release's exact source and dependency
bindings.

The official complete check uses Linux and `bubblewrap`, together with the
toolchain's Comparator, Lean kernel, NanoDa, and con-ron. The macOS build alone
does not reproduce that sandboxed workflow. Once the candidate is committed
and pushed, the **Palomar mechanical preflight** GitHub Actions workflow checks
that exact commit using the approved `palomar-standard-v1` GitHub-hosted
execution profile. The catalogue default uses Palomar's private Namespace
runner infrastructure and is not appropriate for this repository. The
workflow can also be dispatched manually once available on the default branch.
This predictive check does not create a Palomar submission or register a result.

## Submission fields

The official submission uses the following **verified immutable candidate**
and repository-relative paths. Later documentation commits on `main` do not
alter the submitted source snapshot:

| Field | Value |
| --- | --- |
| Submission ID | `bag3afqazkiq` |
| Repository | `https://github.com/MrGodfrey/LeanForCriteriaForLinearStochastic` |
| Verified commit | `c088eb9943197e88c4b046223239d4c4f0180513` |
| Project directory | `formalization` |
| Comparator configuration | `formalization/comparator.json` |
| Formalization metadata | `formalization/formalization.yaml` |

The responsible maintainer is Yu Wang. Submission and eventual registration
are separate actions; an advisory CI pass is neither an editorial decision nor
a registered result.
