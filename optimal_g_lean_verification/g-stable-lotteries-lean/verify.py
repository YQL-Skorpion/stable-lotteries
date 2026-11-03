"""Reproduce the finite-election distortion bounds with the pinned Lean toolchain."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
AUDIT = "OptimalG.CertifiedApproximateAudit"
REPORTS = ROOT / "verification"
PUBLIC_RESULTS = {
    "certifiedActivation_admissible",
    "certifiedActivation_stable_exists",
    "certified_upper_212466",
    "certified_witness_above_212465",
    "certified_metric_witness_above_212465",
    "certified_optimalDistortion_bounds",
    "certifiedActivation_distortion_bounds",
    "rational_bracket_width",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def check_sources():
    """Check the released inputs. The Lean files are listed in import order."""
    sources = []
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        path = ROOT / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit("Source or build input differs from the release: " + name)
        if path.suffix == ".lean":
            sources.append(Path(name))
    return sources


def check_dependencies():
    for package in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]:
        checkout = ROOT / ".lake" / "packages" / package["name"]
        git = ["git", "-C", str(checkout)]
        revision = subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip()
        changes = subprocess.check_output(git + ["status", "--porcelain", "-uno"])
        extra = subprocess.check_output(git + ["ls-files", "--others", "--exclude-standard", "-z"])
        extra_sources = [p for p in extra.split(b"\0") if p.endswith(b".lean") or
                         p.rsplit(b"/", 1)[-1] in {b"lakefile.toml", b"lake-manifest.json", b"lean-toolchain"}]
        if revision != package["rev"] or changes or extra_sources:
            raise SystemExit("Dependency differs from the pinned checkout: " + package["name"])


def run_lake(args, log_name):
    path = REPORTS / log_name
    with path.open("w") as log:
        result = subprocess.run(["lake", *args], stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit("Lake failed. See " + str(path))
    return path


def check_axioms(output):
    results = {}
    for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S):
        results[name] = {value.strip() for value in values.split(",") if value.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        results[name] = set()
    if set(results) != {"OptimalG." + name for name in PUBLIC_RESULTS}:
        raise SystemExit("Unexpected theorem list. See verification/axioms.log")
    for name, axioms in results.items():
        if axioms - ALLOWED_AXIOMS:
            raise SystemExit(f"Unexpected axioms for {name}: {sorted(axioms - ALLOWED_AXIOMS)}")


def verify():
    os.chdir(ROOT)
    sources = check_sources()
    print("Preparing the pinned Lean and mathlib environment...", flush=True)
    run_lake(["exe", "cache", "get"], "dependencies.log")
    version = subprocess.check_output(["lake", "env", "lean", "--version"], text=True)
    expected = (ROOT / "lean-toolchain").read_text().strip().split(":v")[-1]
    if f"version {expected}," not in version:
        raise SystemExit("Expected Lean " + expected + ". Found " + version.strip())
    check_dependencies()

    # A fresh checkout is built one module at a time to bound peak memory.
    # On a repeat run, Lake's final build checks freshness of all cached imports.
    objects = ROOT / ".lake/build/lib/lean"
    for index, source in enumerate(sources, 1):
        if (objects / source.with_suffix(".olean")).is_file():
            continue
        module = ".".join(source.with_suffix("").parts)
        print(f"[{index}/{len(sources)}] Checking {module}", flush=True)
        run_lake(["build", module], "last-module.log")

    print("Checking the final target and its axioms...", flush=True)
    run_lake(["build", AUDIT], "build.log")
    audit = run_lake(["env", "lean", "OptimalG/CertifiedApproximateAudit.lean"], "axioms.log")
    check_axioms(audit.read_text())
    check_sources()
    check_dependencies()
    print("Verified [2.12465, 2.12466]. All 8 theorem axiom checks passed.")


if __name__ == "__main__":
    REPORTS.mkdir(exist_ok=True)
    with (REPORTS / "verify.lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            sys.exit("Another verification is running in this folder.")
        try:
            verify()
        except (OSError, subprocess.CalledProcessError) as error:
            sys.exit(str(error))
