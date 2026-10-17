#!/usr/bin/env python3
"""Run read-only structural checks using a pinned Palomar official checkout.

This is not a proof check and never reports a repository as submission-ready.
Requires Python 3.11+ and the official checker's PyYAML dependency.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

PIPELINE_COMMIT = "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44"
REPOSITORY = Path(__file__).resolve().parents[2]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pipeline", type=Path, required=True,
                        help="PalomarRegistry/PalomarSubmission checkout at the recorded pin")
    parser.add_argument("--repository", type=Path, default=REPOSITORY)
    parser.add_argument("--output", type=Path, help="Optional JSON report, outside historical verification/")
    args = parser.parse_args()
    pipeline = args.pipeline.resolve()
    commit = subprocess.check_output(
        ["git", "-C", str(pipeline), "rev-parse", "HEAD"], text=True).strip()
    if commit != PIPELINE_COMMIT:
        parser.error(f"Official checker must be pinned to {PIPELINE_COMMIT}, got {commit}")
    subprocess.run(["git", "-C", str(pipeline), "diff", "--exit-code", "HEAD", "--",
                    "scripts", "toolchains.json", "taxonomies"], check=True, stdout=subprocess.DEVNULL)
    sys.path.insert(0, str(pipeline))
    from scripts.source_requirements import inspect_lean_sources
    from scripts.submission_contract import load_formalization_metadata
    from scripts.verify_submission import (
        contained_path_dependency, load_comparator_config, manifest_packages,
        manifest_packages_directory, repository_license_file, supported_toolchain,
    )

    root = args.repository.resolve()
    project = root / "formalization"
    report = {"scope": "local structural checks only; no compilation or proof verification",
              "pipeline_commit": commit, "checks": {}, "errors": []}

    def check(name, action):
        try:
            result = action()
            report["checks"][name] = {"status": "pass", "result": result}
            return result
        except (OSError, ValueError, RuntimeError) as error:
            message = str(error)
            report["checks"][name] = {"status": "fail", "error": message}
            report["errors"].append(f"{name}: {message}")
            return None

    def sources():
        result, issues = inspect_lean_sources(root)
        result["issue_count"] = len(issues)
        result["issues"] = [str(issue) for issue in issues]
        if issues:
            report["errors"].append(f"lean_sources: {len(issues)} source violations")
        return result

    source_result = check("lean_sources", sources)
    if source_result and source_result["issue_count"]:
        report["checks"]["lean_sources"]["status"] = "fail"
    check("toolchain", lambda: supported_toolchain((project / "lean-toolchain").read_text().strip()))
    check("metadata", lambda: load_formalization_metadata(project / "formalization.yaml"))

    def dependencies():
        packages = manifest_packages(project)
        directories = {project.resolve()}
        for package in packages:
            if package["url"].startswith("path:"):
                directory = contained_path_dependency(
                    project, package["url"].removeprefix("path:"), root, package["name"])
                directories.add(directory)
                # Parse the contained package's committed lockfile as well.
                manifest_packages(directory)
        packages_dir = manifest_packages_directory(project, checkout=root)
        if packages_dir.parent.parent not in directories:
            raise ValueError("Lake package directory is not owned by the project or a contained package")
        return packages

    check("dependency_manifests", dependencies)
    # This checks the conventional file requirement only. The official Linux
    # workflow also performs independent SPDX detection with Licensee.
    check("root_license_file", lambda: str(repository_license_file(root).relative_to(root)))
    config = check("comparator_config", lambda: load_comparator_config(project / "comparator.json"))
    if config:
        for field in ("challenge_module", "solution_module"):
            path = project.joinpath(*config[field].split(".")).with_suffix(".lean")
            def module_source(path=path, field=field):
                if path.is_symlink() or not path.is_file():
                    raise ValueError(f"Missing regular source file: {path.relative_to(root)}")
                data = path.read_bytes()
                lines = data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))
                if field == "challenge_module" and (len(data) > 100 * 1024 or lines > 1000):
                    raise ValueError("Challenge exceeds 100 KiB or 1,000 physical lines")
                return {"path": str(path.relative_to(root)), "bytes": len(data), "lines": lines}
            check(field, module_source)

    report["status"] = "failed" if report["errors"] else "passed_structural_checks"
    report["not_checked"] = [
        "Lean parsing and complete clean build", "canonical transitive Challenge imports",
        "exact Challenge/Solution correspondence", "transitive permitted axioms",
        "Lean, NanoDa and con-ron kernel replay", "SPDX license detection",
        "manuscript fidelity and editorial review", "public fixed-commit availability",
    ]
    if args.output:
        output = args.output.resolve()
        if output.is_relative_to(root / "formalization/verification"):
            parser.error("Do not overwrite historical release verification with a preparation report")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": report["status"], "errors": report["errors"],
                      "scope": report["scope"]}, indent=2))
    return int(bool(report["errors"]))


if __name__ == "__main__":
    raise SystemExit(main())
