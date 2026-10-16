#!/usr/bin/env python3
"""Verify the frozen article companion, without internal development audit files.

Python 3.11+ and the pinned Lean/Lake toolchain are required. Run this script
from any directory. Results are written under formalization/verification/.
--metadata-only checks the frozen publication inputs but never reports proof
completion. The default run builds and replays every local proof module.

The declaration parser and local hygiene policy are retained from the reviewed
internal verifier. Hashes bind artifacts; they are not digital signatures or
independent endorsements of a natural-language mathematical interpretation.
"""
from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
RELEASE_ROOT = ROOT.parent
OUTPUT = ROOT / "verification"
ALLOW = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_COUNTS = {"modules": 384, "declarations": 2559, "claims": 80,
                   "named": 18, "anchors": 87}
ORIGINAL_SOURCE = "8ccc417fa3629e23e0b9dba2cd499916ccc9369201a9bec28f1538d298cb39ea"
ORIGINAL_PROOFS = "a197fbdec236da5e9e272436caa27fb3e1d6431d31f41b04863c8a69e225c38c"
ORIGINAL_MAPPING = "20a8ab4f170a4e2c2a5c5c270b1e7c1c5125bfc201f054011b0db7fe133100ee"
ORIGINAL_VERIFICATION = "41e437b3f15c2b3cda77874ad2ff0e9e189ff54ee55d8419934889ab68f7b950"
ORIGINAL_BUILD_INPUTS = {'lakefile.toml': 'aaefef94ebde9cecff6f1f9401b0a9287a7b95b9e2290430098a1f3f04ade28a', 'lake-manifest.json': 'b27d060cc6fa0e87034822f115f324c1b7de786f7178990606d54c9f55370dde', 'lean-toolchain': '62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef'}
CLAIMS = "formalization/audit/claims.en.json"
TRANSLATION_REVIEW = "formalization/audit/translation-review.json"
VERIFIER_REVIEW = "formalization/audit/verifier-review.json"
MANIFEST = "formalization/audit/release-manifest.json"
VERIFIER = "formalization/scripts/verify_release.py"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_sha(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                     ensure_ascii=False).encode()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def local_path(relative):
    require(isinstance(relative, str) and relative, "Empty/non-string release path")
    parsed = PurePosixPath(relative)
    require(not parsed.is_absolute() and ".." not in parsed.parts and "\\" not in relative,
            "Release paths must be relative and stay inside the package")
    path = RELEASE_ROOT / relative
    require(path.resolve().is_relative_to(RELEASE_ROOT.resolve()), "Release path escapes package")
    require(path.is_file(), "Missing release file: " + relative)
    return path


def redact(text):
    # Logs remain useful without publishing the builder's home or temporary path.
    text = str(text).replace(str(RELEASE_ROOT), ".")
    return re.sub(r"(?:/Users/|/home/|/private/tmp/|/tmp/)[^\s\"'<>]*", "<local-path>", text)


def uncomment(source: str) -> str:
    """Remove nested Lean comments while retaining newlines and token boundaries."""
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif not depth and source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i] if not depth or source[i] == "\n" else " ")
            i += 1
    if depth:
        raise ValueError("Unterminated Lean block comment")
    return "".join(out)


def declarations(path: Path) -> list[dict]:
    code = uncomment(path.read_text())
    # Conservative local hygiene policy. The kernel axiom closure is also checked.
    forbidden = r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|sorryAx|run_tac)\b|debug\.skipKernelTC|decide\s*\+native"
    match = re.search(forbidden, code)
    if match:
        raise ValueError(f"Forbidden construct {match[0]!r} in {path.relative_to(ROOT)}")
    stack, names = [], []
    for line, s in enumerate(code.splitlines(), 1):
        n = re.match(r"\s*(namespace|section)\s*([^\s]*)", s)
        if n:
            stack.append((n[1], n[2]))
        if re.match(r"\s*end(?:\s|$)", s):
            if stack:
                stack.pop()
        # Enumerate explicit public names, including semantic interfaces and
        # named instances. Anonymous instances and generated constructors,
        # projections and recursors are covered by whole-module kernel replay.
        # Binder-opening characters cannot be mistaken for instance names.
        m = re.search(r"\b(theorem|lemma|def|abbrev|class|structure|inductive|instance)\s+([^\s(:\[{]+)", s)
        if m:
            if "private" in s[:m.start()]:
                if m[1] in ("theorem", "lemma"):
                    raise ValueError("Private theorem needs an explicit audit-name mapping")
                # Private definitions have mangled names. Their proofs are replayed
                # by leanchecker and their axioms occur in the public closure.
                continue
            namespace = ".".join(n for k, n in stack if k == "namespace")
            names.append({"name": namespace + "." + m[2], "kind": m[1],
                          "file": str(path.relative_to(ROOT)), "line": line})
    return names


def module_name(path):
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def check_anchors(data, source_text):
    claims = data["claims"]
    require(len(claims) == EXPECTED_COUNTS["claims"], "Incorrect claim count")
    by_id = {c["id"]: c for c in claims}
    require(len(by_id) == len(claims), "Duplicate claim ID")
    ranges = 0
    for claim in claims:
        require(claim["verdict"] == "full", "A publication mapping is incomplete: " + claim["id"])
        require(claim["source_ranges"], "Claim has no exact source anchor")
        require(set(claim["dependencies"]) <= set(by_id), "Unknown dependency claim")
        for entry in claim["source_ranges"]:
            excerpt = entry["source_excerpt"]
            require(isinstance(excerpt, str) and excerpt, "Empty source excerpt")
            require(hashlib.sha256(excerpt.encode()).hexdigest() == entry["excerpt_sha256"],
                    "Source excerpt hash differs: " + claim["id"])
            require(source_text.count(excerpt) == 1, "Source excerpt missing or nonunique: " + claim["id"])
            start = source_text.index(excerpt)
            line = source_text[:start].count("\n") + 1
            require(entry["line"] == line and entry["end_line"] == line + excerpt.count("\n"),
                    "Source excerpt position differs: " + claim["id"])
            ranges += 1
    require(ranges == EXPECTED_COUNTS["anchors"], "Incorrect exact source range count")
    tex = re.sub(r"(?<!\\)%[^\n]*", "", source_text)
    named = set(re.findall(r"\\begin\{(?:thm|lem|cor|prop|exmp|rem)\}\s*\\label(?:\[[^\]]+\])?\{([^}]+)\}", tex))
    require(len(named) == EXPECTED_COUNTS["named"] and named <= set(by_id),
            "Named manuscript statements differ from the reviewed inventory")
    canonical_mapping = [{k: c[k] for k in
                         ("id", "dependencies", "source_ranges", "declarations", "verdict")}
                         for c in sorted(claims, key=lambda c: c["id"])]
    require(canonical_sha(canonical_mapping) == ORIGINAL_MAPPING,
            "The mathematical mapping differs from the independently reviewed original")
    return sorted(named), ranges


def check_metadata():
    """Return an exact snapshot of all required release inputs; never rewrite them."""
    for relative, digest in ORIGINAL_BUILD_INPUTS.items():
        require(sha(ROOT / relative) == digest, "Build environment differs from the reviewed original: " + relative)
    files = sorted((ROOT / "LinearStochastic").rglob("*.lean"))
    proof_hashes = {str(p.relative_to(ROOT)): sha(p) for p in files}
    require(len(files) == EXPECTED_COUNTS["modules"] and canonical_sha(proof_hashes) == ORIGINAL_PROOFS,
            "Local proof inventory differs from the verified 384-module original")
    aggregate = "".join(f"import {module_name(p)}\n" for p in files)
    require((ROOT / "LinearStochastic.lean").read_text() == aggregate,
            "Aggregate must contain exactly the current module imports and no declarations")
    names = [d for p in files for d in declarations(p)]
    require(len(names) == EXPECTED_COUNTS["declarations"] and
            len({d["name"] for d in names}) == len(names), "Incorrect/duplicate declaration inventory")
    manifest = read_json(local_path(MANIFEST))
    require(manifest["schema_version"] == 1, "Unsupported release manifest schema")
    bindings = manifest["files"]
    require(isinstance(bindings, dict) and MANIFEST not in bindings,
            "Manifest cannot hash itself")
    required = {"main.tex", "main.pdf", "references.bib", "autart.cls", CLAIMS,
                TRANSLATION_REVIEW, VERIFIER_REVIEW, VERIFIER,
                "formalization/LinearStochastic.lean", "formalization/lakefile.toml",
                "formalization/lake-manifest.json", "formalization/lean-toolchain",
                "formalization/licenses/NOTICE.md", "formalization/licenses/MathFin-APACHE-2.0.txt"}
    required |= {"formalization/" + p for p in proof_hashes}
    require(required <= set(bindings), "Manifest omits required publication inputs")
    for relative, digest in bindings.items():
        require(not relative.startswith(("formalization/verification/", "formalization/.lake/")),
                "Generated results or dependency caches must not be frozen release inputs")
        require(sha(local_path(relative)) == digest, "Release file changed: " + relative)
    source = local_path("main.tex")
    require(sha(source) == ORIGINAL_SOURCE, "Manuscript differs from the reviewed original")
    data = read_json(local_path(CLAIMS))
    require(data["source"]["path"] == "main.tex" and data["source"]["sha256"] == ORIGINAL_SOURCE,
            "English inventory has a stale manuscript hash")
    require(data["source"]["line_count"] == len(source.read_text().splitlines()), "Stale source line count")
    require(data["reviewed_files"] == proof_hashes, "English inventory does not bind every original proof")
    require(data["expected_counts"] == EXPECTED_COUNTS, "English inventory expected counts differ")
    named, ranges = check_anchors(data, source.read_text())
    available = {d["name"] for d in names}
    for claim in data["claims"]:
        ds = claim["declarations"]
        require(ds and len(ds) == len(set(ds)) and set(ds) <= available,
                "Missing/unknown/duplicate mapped declaration: " + claim["id"])
    translation = read_json(local_path(TRANSLATION_REVIEW))
    require(translation.get("independent_approval") is True and translation.get("verdict") == "pass",
            "Independent publication translation review is not approved")
    require(translation.get("reviewer") and translation.get("translator") and
            translation["reviewer"] != translation["translator"], "Translation review must be independent")
    require(not translation.get("blocking_findings", []), "Translation review has blocking findings")
    for key, value in {"claims_sha256": sha(local_path(CLAIMS)), "source_sha256": ORIGINAL_SOURCE,
                       "proof_inventory_sha256": ORIGINAL_PROOFS, "mapping_sha256": ORIGINAL_MAPPING}.items():
        require(translation.get(key) == value, "Stale publication translation review: " + key)
    code_review = read_json(local_path(VERIFIER_REVIEW))
    require(code_review.get("independent_approval") is True and code_review.get("verdict") == "pass",
            "Publication verifier independent review is not approved")
    require(code_review.get("reviewer") and code_review.get("author") and
            code_review["reviewer"] != code_review["author"], "Verifier review must be independent")
    require(not code_review.get("blocking_findings", []) and
            code_review.get("verifier_sha256") == sha(local_path(VERIFIER)), "Stale/blocked publication verifier review")
    # Bind all inputs including both reviews and the manifest itself for end-of-run freshness.
    snapshot = {relative: sha(local_path(relative)) for relative in bindings}
    snapshot[MANIFEST] = sha(local_path(MANIFEST))
    return files, names, data, snapshot, named, ranges


def run(command, log):
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (OUTPUT / log).write_text(redact(result.stdout), encoding="utf-8")
    return result


def dependency_pins():
    manifest = read_json(ROOT / "lake-manifest.json")
    packages = manifest["packages"]
    require(packages and len({d["name"] for d in packages}) == len(packages),
            "Missing or duplicate pinned dependencies")
    records = []
    for dep in packages:
        name = dep["name"]
        require(re.fullmatch(r"[A-Za-z0-9_.-]+", name) is not None and dep["type"] == "git" and
                re.fullmatch(r"[0-9a-f]{40}", dep["rev"]) is not None, "Dependency is not pinned to a Git commit")
        directory = ROOT / ".lake/packages" / name
        def git(*args):
            return subprocess.check_output(["git", "-C", str(directory), *args], text=True).strip()
        actual = git("rev-parse", "HEAD")
        dirty = git("status", "--porcelain", "--untracked-files=no")
        extra = git("ls-files", "--others", "--exclude-standard").splitlines()
        extra_lean = [p for p in extra if p.endswith(".lean") and not p.startswith(".lake/")]
        require(actual == dep["rev"] and not dirty and not extra_lean,
                "Dependency source checkout is not the clean pinned commit: " + name)
        records.append({"name": name, "revision": actual, "url": dep["url"], "clean": True})
    return records


def replay_modules(lake, modules, workers):
    """Separate unchanged leanchecker invocations, bounded to at most four jobs."""
    def one(module):
        result = subprocess.run([lake, "env", "leanchecker", "--verbose", module],
                                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        markers = re.findall(r"^replaying (\S+)$", result.stdout, re.M)
        return result.stdout, {"module": module, "exit_code": result.returncode,
                               "replayed_modules": markers, "exact_target_replayed": markers == [module]}
    completed = {}
    with (OUTPUT / "kernel-replay.log").open("w", encoding="utf-8") as log:
        with ThreadPoolExecutor(max_workers=workers) as pool:
            pending = {pool.submit(one, module): module for module in modules}
            for future in as_completed(pending):
                module = pending[future]
                output, record = future.result()
                completed[module] = record
                log.write(redact(output) + "\n"); log.flush()
                print(f"Kernel replay {len(completed)}/{len(modules)}: {module} "
                      f"(exit {record['exit_code']}, exact target {record['exact_target_replayed']})", flush=True)
    return [completed[module] for module in modules]


def check_freshness(snapshot, modules):
    for relative, digest in snapshot.items():
        require(sha(local_path(relative)) == digest, "Input changed during verification: " + relative)
    current = sorted(module_name(p) for p in (ROOT / "LinearStochastic").rglob("*.lean"))
    require(current == modules, "Proof module inventory changed during verification")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kernel-jobs", type=int, choices=range(1, 5), default=2)
    parser.add_argument("--metadata-only", action="store_true",
                        help="Check publication bindings only; never report formal verification as passed")
    args = parser.parse_args()
    OUTPUT.mkdir(exist_ok=True)
    result = {"schema_version": 1, "checked_at": datetime.now(timezone.utc).isoformat(),
              "mode": "metadata-only" if args.metadata_only else "full",
              "metadataPassed": False, "kernelSubsetPassed": False, "allAxiomsAllowed": False,
              "fullPaperPassed": False, "errors": [], "declarations": [],
              "trust_scope": "Same Lean kernel; local proof-object replay, not an independent kernel or a fresh replay of all dependency proofs. Semantic correspondence is the bound independent publication review."}
    destination = OUTPUT / "verification.json"
    # Invalidate any older result before starting a new verification attempt.
    destination.write_text(json.dumps(result, indent=2) + "\n")
    try:
        files, names, data, snapshot, named, ranges = check_metadata()
        modules = [module_name(p) for p in files]
        result.update(input_sha256=snapshot, manuscript_sha256=ORIGINAL_SOURCE,
                      verifier_sha256=sha(local_path(VERIFIER)), proof_inventory_sha256=ORIGINAL_PROOFS,
                      mapping_sha256=ORIGINAL_MAPPING, original_verification_sha256=ORIGINAL_VERIFICATION,
                      named_manuscript_claims=named, source_anchor_count=ranges,
                      declarations=names, metadataPassed=True)
        if not args.metadata_only:
            lake = shutil.which("lake")
            require(lake is not None, "lake was not found; install the pinned Lean toolchain first")
            result["dependencies"] = dependency_pins()
            toolchain = (ROOT / "lean-toolchain").read_text().strip()
            version = run([lake, "env", "lean", "--version"], "toolchain.log")
            expected_version = toolchain.rsplit(":v", 1)[-1]
            match = re.search(r"version ([^,\s)]+)", version.stdout)
            require(version.returncode == 0 and match and match[1] == expected_version,
                    "Active Lean version differs from lean-toolchain")
            result["toolchain"] = redact(version.stdout.strip())
            build = run([lake, "build"], "build.log")
            result["build_exit_code"] = build.returncode
            require(build.returncode == 0, "lake build failed; see verification/build.log")
            records = replay_modules(lake, modules, args.kernel_jobs)
            result["kernel_replay_workers"] = args.kernel_jobs
            result["kernel_replay_runs"] = records
            require([r["module"] for r in records] == modules and all(
                r["exit_code"] == 0 and r["exact_target_replayed"] and r["replayed_modules"] == [r["module"]]
                for r in records), "A module replay failed or did not identify exactly its target")
            result["replayed_modules"] = modules
            inspection = "import LinearStochastic\nset_option format.width 120\n" + "\n".join(
                f"#check @{d['name']}\n#print axioms {d['name']}" for d in names) + "\n"
            (OUTPUT / "check.lean").write_text(inspection, encoding="utf-8")
            audit = run([lake, "env", "lean", "verification/check.lean"], "axioms.log")
            result["audit_exit_code"] = audit.returncode
            require(audit.returncode == 0, "Type/axiom inspection failed; see verification/axioms.log")
            pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
            entries = [(m[1], sorted(x.strip() for x in (m[2] or "").split(",") if x.strip()))
                       for m in re.finditer(pattern, audit.stdout)]
            require(Counter(n for n, _ in entries) == Counter(d["name"] for d in names),
                    "Axiom output has missing, duplicate, or unexpected declarations")
            closures = dict(entries)
            for declaration in names:
                axioms = closures[declaration["name"]]
                declaration.update(axioms=axioms, axioms_allowed=set(axioms) <= ALLOW)
            require(all(d["axioms_allowed"] for d in names), "Unapproved transitive axiom dependency")
            result["allAxiomsAllowed"] = True
            require(dependency_pins() == result["dependencies"], "Dependency checkout changed during verification")
        check_freshness(snapshot, modules)
        if not args.metadata_only:
            result["kernelSubsetPassed"] = True
            result["coverage"] = [{"id": c["id"], "status": "full", "declarations": c["declarations"]}
                                  for c in data["claims"]]
            result["fullPaperPassed"] = True
    except (Exception, KeyboardInterrupt) as error:
        result["errors"].append(redact(type(error).__name__ + ": " + str(error)))
        result["kernelSubsetPassed"] = False
        result["fullPaperPassed"] = False
    temporary = OUTPUT / "verification.json.tmp"
    temporary.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    os.replace(temporary, destination)
    print(json.dumps({k: result[k] for k in
                     ("metadataPassed", "kernelSubsetPassed", "allAxiomsAllowed", "fullPaperPassed", "errors")}))
    return 1 if result["errors"] else 0


if __name__ == "__main__":
    sys.exit(main())
