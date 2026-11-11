"""Reproduce a fixed proof revision and preserve observed verification results."""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args, cwd=ROOT):
    return subprocess.check_output(["git", *args], cwd=cwd, text=True, encoding="utf-8").strip()


def tracked_hashes():
    names = git("ls-files", "-z").split("\0")
    return {name: digest(ROOT / name) for name in names if name}


def dependencies():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    results = []
    for package in manifest["packages"]:
        path = ROOT / manifest["packagesDir"] / package["name"]
        head = git("rev-parse", "HEAD", cwd=path)
        changes = git("status", "--porcelain", "--untracked-files=no", cwd=path)
        results.append({"name": package["name"], "expected": package["rev"],
                        "actual": head, "tracked_changes": changes})
        if head != package["rev"] or changes:
            raise RuntimeError("Dependency does not match the lockfile: " + package["name"])
    return results


def analyze_axioms(path, expected):
    content = path.read_text(encoding="utf-8", errors="replace")
    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", content)
    records = {name: [a.strip() for a in raw.split(",") if a.strip()] for name, raw in rows}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", content):
        records[name] = []
    missing = sorted(set(expected) - set(records))
    extras = {n: a for n, a in records.items() if set(a) - ALLOWED_AXIOMS}
    result = {"expected_count": len(expected), "observed_count": len(records),
              "missing": missing, "unexpected_axioms": extras, "axioms_by_target": records}
    result["passed"] = not missing and not extras
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--lake", type=Path)
    args = parser.parse_args()
    timestamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    output = args.output or ROOT / "verification-runs" / timestamp
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    lake = args.lake or Path(shutil.which("lake") or "lake")
    lake = lake.resolve()
    before = tracked_hashes()
    commit = git("rev-parse", "HEAD")
    if git("status", "--porcelain", "--untracked-files=no"):
        raise RuntimeError("Tracked source must be clean before verification")
    env = dict(os.environ)
    for name in ["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_OPTS"]:
        env.pop(name, None)
    env["LEAN_NUM_THREADS"] = "1"
    env["PATH"] = str(lake.parent) + os.pathsep + env.get("PATH", "")
    results = {
        "proof_commit": commit, "started_utc": timestamp, "os": platform.platform(),
        "machine": platform.machine(), "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "lake_executable_sha256": digest(lake), "source_sha256": before,
        "process_environment": {"LEAN_NUM_THREADS": "1", "inherited_lean_paths": "cleared"},
        "execution_model": "dedicated checkout on local host; revision-checked dependency caches",
        "steps": [], "all_checks_passed": False,
    }

    def save():
        (output / "RESULTS.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")

    def run(name, arguments):
        log = output / (name + ".log")
        start = time.monotonic()
        command = [str(lake), *arguments]
        with log.open("wb") as stream:
            process = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
        record = {"name": name, "command": ["lake", *arguments], "cwd": ".",
                  "exit_code": process.returncode, "elapsed_seconds": round(time.monotonic() - start, 3),
                  "log": log.name, "log_sha256": digest(log)}
        results["steps"].append(record)
        save()
        print(json.dumps(record), flush=True)
        if process.returncode:
            raise RuntimeError("Verification command failed: " + name)

    try:
        results["dependencies_before"] = dependencies()
        run("lean-version", ["env", "lean", "--version"])
        version = (output / "lean-version.log").read_text(encoding="utf-8")
        if not re.search(r"version 4\.34\.0(?:[,\s])", version):
            raise RuntimeError("Unexpected Lean version")
        run("lake-version", ["--version"])
        results["project_build_was_empty"] = not (ROOT / ".lake/build").exists()
        run("build", ["build"])
        for name, path in [
            ("statement", "verification/StatementCheck.lean"),
            ("solution", "Erdos302/Solution.lean"),
            ("rational-enclosures", "Erdos302/RationalEnclosure.lean"),
            ("lower-bound", "Erdos302/CambieLowerBound.lean"),
            ("standalone", "Erdos302Full.lean"),
            ("modular-axioms", "verification/CurrentAudit.lean"),
            ("standalone-axioms", "verification/FullAudit.lean"),
            ("expanded-targets", "verification/ExpandedTargets.lean"),
        ]:
            run(name, ["env", "lean", path])
        registry = json.loads((ROOT / "verification/current-targets.json").read_text(encoding="utf-8"))
        expected = [target["name"] for target in registry["targets"]]
        results["axiom_audits"] = {}
        for name in ["modular-axioms", "standalone-axioms"]:
            analysis = analyze_axioms(output / (name + ".log"), expected)
            results["axiom_audits"][name] = analysis
            if not analysis["passed"]:
                raise RuntimeError("Incomplete or nonstandard axiom audit: " + name)
        run("kernel-replay", ["env", "leanchecker", "--fresh", "--verbose", "verification.StatementCheck"])
        results["dependencies_after"] = dependencies()
        results["source_unchanged"] = tracked_hashes() == before and git("rev-parse", "HEAD") == commit
        if not results["source_unchanged"]:
            raise RuntimeError("Tracked source changed during verification")
        results["all_checks_passed"] = True
        results["completed_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    except Exception as error:
        results["error"] = str(error)
        raise
    finally:
        save()
    print(json.dumps({"all_checks_passed": True, "proof_commit": commit}), flush=True)


if __name__ == "__main__":
    main()
