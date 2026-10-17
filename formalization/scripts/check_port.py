#!/usr/bin/env python3
"""Build the port and inspect the reference declarations plus Palomar entry points.

This local check does not replace sandboxed Comparator, independent kernels,
statement review, or Palomar's editorial decision. Historical reports are untouched.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
ALLOW = {"propext", "Quot.sound", "Classical.choice"}
ADVERTISED = ["LinearStochastic.Palomar.classification", "LinearStochastic.Palomar.ito_unique"]


def inspect_axioms(output: str, expected: list[str]) -> dict[str, list[str]]:
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    entries = [(m[1], sorted(a.strip() for a in (m[2] or "").split(",") if a.strip()))
               for m in re.finditer(pattern, output)]
    if Counter(n for n, _ in entries) != Counter(expected):
        raise ValueError("Missing, duplicate, or unexpected axiom output")
    for name, axioms in entries:
        if not set(axioms) <= ALLOW:
            raise ValueError(f"Unapproved transitive axioms for {name}: {axioms}")
    return dict(entries)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_snapshot(project: Path) -> dict[str, str]:
    paths = []
    for directory, dirs, files in os.walk(project):
        dirs[:] = [d for d in dirs if d not in {".lake", ".git", "__pycache__"}]
        paths.extend(Path(directory) / f for f in files
                     if f.endswith(".lean") or f in {"lakefile.toml", "lake-manifest.json", "lean-toolchain"})
    paths += [project / f for f in ["comparator.json", "scripts/check_port.py"]]
    return {str(p.relative_to(project)): digest(p) for p in sorted(paths)}


def pinned_dependencies(project: Path) -> list[dict]:
    result = []
    for dependency in json.loads((project / "lake-manifest.json").read_text())["packages"]:
        if dependency["type"] == "path":
            path = (project / dependency["dir"]).resolve()
            if not path.is_relative_to(project) or not path.is_dir():
                raise ValueError("Path dependency must remain inside this project")
            result.append({"name": dependency["name"], "path": dependency["dir"]})
            continue
        if dependency["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", dependency["rev"]):
            raise ValueError("Dependency is not pinned to a full Git commit")
        path = project / ".lake/packages" / dependency["name"]
        def git(*args):
            return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()
        if git("rev-parse", "HEAD") != dependency["rev"] or git("status", "--porcelain", "--untracked-files=no"):
            raise ValueError(f"Modified dependency: {dependency['name']}")
        if any(f.endswith(".lean") for f in git("ls-files", "--others", "--exclude-standard").splitlines()):
            raise ValueError(f"Untracked Lean source in dependency: {dependency['name']}")
        result.append({"name": dependency["name"], "revision": dependency["rev"], "url": dependency["url"]})
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=PROJECT)
    args = parser.parse_args()
    project = args.project.resolve()
    logs = project / ".lake/palomar-checks"
    logs.mkdir(parents=True, exist_ok=True)
    destination = project / "palomar/local-check.json"
    destination.parent.mkdir(exist_ok=True)
    report = {"checked_at": datetime.now(timezone.utc).isoformat(), "status": "running",
              "scope": "local build and named transitive axiom inspection; not Palomar verification"}
    destination.write_text(json.dumps(report, indent=2) + "\n")
    def run(command, name):
        with (logs / name).open("w") as stream:
            result = subprocess.run(command, cwd=project, stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"Command failed ({result.returncode}); see .lake/palomar-checks/{name}")
        return (logs / name).read_text()
    try:
        snapshot = source_snapshot(project)
        report["toolchain"] = run(["lake", "env", "lean", "--version"], "version.log").strip()
        expected = (project / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
        if not re.search(r"version " + re.escape(expected) + r"[,\s)]", report["toolchain"]):
            raise ValueError("Active toolchain differs from the pinned version")
        report["dependencies"] = pinned_dependencies(project)
        run(["lake", "build"], "build.log")
        report["build_passed"] = True
        inspection = (project / "verification/check.lean").read_text()
        names = re.findall(r"^#print axioms (\S+)$", inspection, re.M)
        if len(names) != 2559 or len(set(names)) != len(names):
            raise ValueError("Reference declaration inventory changed")
        axioms = inspect_axioms(run(["lake", "env", "lean", "verification/check.lean"], "reference-axioms.log"), names)
        additional = logs / "Advertised.lean"
        additional.write_text("module\nimport Solution\nset_option format.width 120\n" +
                              "\n".join("#print axioms " + n for n in ADVERTISED) + "\n")
        axioms.update(inspect_axioms(run(["lake", "env", "lean", str(additional)], "advertised-axioms.log"), ADVERTISED))
        if snapshot != source_snapshot(project) or report["dependencies"] != pinned_dependencies(project):
            raise ValueError("Inputs changed during the check")
        report.update(status="passed_local_checks", input_sha256=snapshot,
                      declaration_count=len(axioms), declaration_axioms=axioms)
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        report.update(status="failed", error=str(error))
    destination.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({k: report[k] for k in ["status", "scope", "declaration_count", "error"] if k in report}))
    return int(report["status"] != "passed_local_checks")


if __name__ == "__main__":
    raise SystemExit(main())
