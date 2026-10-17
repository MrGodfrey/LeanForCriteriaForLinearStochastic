# Stochastic-analysis compatibility sources

This package contains the **92 Lean modules in the import closure used by
LinearStochastic**, extracted from MathFin, BrownianMotion, and
KolmogorovExtension4. It is not a redistribution of those projects' full
libraries or verification reports.

`provenance.json` records each original repository, immutable commit, source
path, original SHA-256, and ported SHA-256. `compatibility.patch` contains the
complete source changes; per-file notices identify this compatibility port. Original copyright and author notices are retained. The
sources are Apache-2.0; see `LICENSE`, this repository's root `NOTICE`, and
`formalization/licenses/NOTICE.md`.

The local compatibility changes target Lean `v4.35.0-rc2` and canonical Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. They remove declarations newly
provided by Mathlib, adapt the new `MemLp` and uniform-integrability APIs, and
make type annotations and measurability arguments explicit. No new proof
placeholders or axioms are permitted in the compatibility changes.

The three umbrella modules are generated lists of this package's source
modules. External dependencies remain pinned in the committed Lake manifests.
Build this package through the enclosing `formalization` project. Its manifest
uses the enclosing project's package directory to share the same canonical
Mathlib closure.

Upstream proof placeholders are not silently erased or promoted to proofs.
The submission's advertised declarations must have their transitive axiom
closure checked separately. A successful source build does not establish that
condition or certify agreement with the accompanying paper.
