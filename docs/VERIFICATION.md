# Public verification evidence

The public package does not need the private development history. It needs the
frozen proof sources, dependency pins, complete manuscript-to-proof index, and
honestly attributed publication reviews. The verification result is regenerated
from those inputs; a historical `PASS` flag is not copied into the new result.

## Required files

At the release root: `main.tex`, `main.pdf`, `references.bib`, and the unchanged
`autart.cls`, plus the bibliography style and any other actual TeX dependencies
needed to reproduce the PDF. Under `formalization/`:

- All 384 `LinearStochastic/*.lean` modules, byte-identical to the verified sources.
- The exact import-only `LinearStochastic.lean` aggregate.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`, byte-identical to the
  previously verified environment. The script fixes their original hashes.
- `scripts/verify_release.py` and optionally the isolated orchestration tests.
- `audit/claims.en.json`, with all 80 claims, 18 named statements, 87 exact source
  excerpts, mapped declaration names, and all 384 proof-source hashes.
- `audit/translation-review.json` and `audit/verifier-review.json`.
- `audit/release-manifest.json`, created last, binding all core inputs by their
  release-root-relative path and SHA-256, including the PDF and both reviews.
- `licenses/NOTICE.md` and `licenses/MathFin-APACHE-2.0.txt`, preserving upstream
  attribution; the adapted Lean source copyright/license headers remain intact.

The manifest excludes itself, `.lake/`, and generated `verification/` outputs.
The manifest is still hashed in every verification result and checked again at
the end of the run. Do not package symlinks to a developer's dependency checkout.
Dependency caches may be reused locally to test a staging tree but are not part
of the public distribution.

## Review schemas

`translation-review.json` requires these fields:

```json
{
  "independent_approval": true,
  "verdict": "pass",
  "reviewer": "actual independent reviewer",
  "translator": "actual translator",
  "blocking_findings": [],
  "claims_sha256": "SHA-256 of claims.en.json",
  "source_sha256": "SHA-256 of main.tex",
  "proof_inventory_sha256": "canonical digest below",
  "mapping_sha256": "canonical digest below"
}
```

`verifier-review.json` requires `independent_approval`, `verdict`, `reviewer`,
`author`, `blocking_findings`, and `verifier_sha256`. The author and reviewer must
be different. Extra English fields should describe actual review methods and
limitations. These records are transparent review assertions, not cryptographic
signatures, institutional endorsements, or independent formal proof certificates.
Never fill an approval field before the named review actually occurred.

The proof-inventory digest hashes the `reviewed_files` dictionary, whose paths
are relative to `formalization/`. The mathematical-mapping digest hashes the
claims sorted by ID, retaining exactly `id`, `dependencies`, `source_ranges`,
`declarations`, and `verdict`. Inner list order is retained. Both use UTF-8 JSON
with `sort_keys=True`, `separators=(',', ':')`, and `ensure_ascii=False`.
English summaries, titles, and explanatory reasons are reviewed separately and
are excluded from this invariant digest so translation cannot change the scope.
The script checks both digests against the original verified mathematical bundle.

## Running the gate

Run `python3 formalization/scripts/verify_release.py --kernel-jobs 4` from the
release root after installing Lean/Lake and the pinned dependencies. The default
is a full build, exact-module kernel replay, and type/transitive-axiom inspection
for all 2559 explicit named declarations. `--metadata-only` checks bindings and
source anchors but always leaves the formal verification flags false.

Output goes only to `formalization/verification/`. Existing success evidence is
invalidated at the start of a new attempt. A result reports full completion only
when the source bindings, independent publication reviews, build, all exact
module replays, every axiom closure, and final freshness checks pass. Git pins
and clean dependency source checkouts are checked before and after proof checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in the inspected
transitive axiom closures. Local placeholders, custom axioms, and unsafe/native
proof shortcuts are rejected by the retained local source-hygiene policy.

The checker invokes the pinned `lake env leanchecker`. It uses Lean's own kernel,
not an independently implemented proof checker, and does not freshly replay all
of mathlib. Lake/build infrastructure and the selected Lean runtime remain part
of the computational trust boundary. Eight unused upstream source placeholders
must remain disclosed separately from the zero-placeholder public proof closures.
Logs and result paths are relative or redact local home/temporary paths.

## Independent tests to retain

Reviewers should inspect the full script and run the isolated Python `-O` tests.
Tests should reject changed manuscript/proof/pin bytes even if the manifest is
rewritten; reduced mappings; stale or nonunique anchors; missing independent
review; impure aggregate; failed builds; dirty dependencies; mismatched toolchain;
nonzero replay exits; absent, duplicated, or swapped per-process markers; missing,
duplicate, or forbidden axiom closures; and changes during verification. Test
fixtures mock the proof subprocesses and must never be described as real kernel
verification. The final publication gate must be run on the actual release tree.
