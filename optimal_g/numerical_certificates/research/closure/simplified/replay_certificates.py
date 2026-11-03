#!/usr/bin/env python3
"""Replay the accepted certificate bundle, always in separate serial processes.

Examples (from the repository/package root):
  python3 research/closure/simplified/replay_certificates.py --list
  python3 research/closure/simplified/replay_certificates.py --group binary --dry-run
  python3 research/closure/simplified/replay_certificates.py --all

A group uses the supplied prerequisite certificates unless
--with-dependencies is requested. Checkers refresh their declared result JSON
files; imported exact-arithmetic helpers can also refresh auxiliary results.
No optimizer or exploratory checker is run. NumPy is required by interval
checks; the runner itself uses only the Python standard library.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
MANIFEST = HERE / "certificate_manifest.json"


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest() if hasattr(hashlib, "file_digest") else hashlib.sha256(stream.read()).hexdigest()


def main() -> int:
    if sys.flags.optimize:
        raise SystemExit("Certificate assertions are essential: run Python without -O/-OO and unset PYTHONOPTIMIZE.")
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--manifest", type=Path, default=MANIFEST)
    parser.add_argument("--list", action="store_true", help="List groups and exact commands without executing them.")
    parser.add_argument("--group", action="append", default=[], help="Select a manifest group; repeat to select several.")
    parser.add_argument("--id", action="append", default=[], help="Select an individual certificate ID; repeat as needed.")
    parser.add_argument("--all", action="store_true", help="Select every accepted certificate command.")
    parser.add_argument("--with-dependencies", action="store_true", help="Also replay prerequisite certificate commands.")
    parser.add_argument("--dry-run", action="store_true", help="Print the selected serial commands without running them.")
    parser.add_argument("--python", default=sys.executable, help="Python executable for the subprocesses; default is this interpreter.")
    parser.add_argument("--logs", type=Path, default=HERE / "replay_logs", help="Directory for stdout/stderr logs and replay summary.")
    parser.add_argument("--check-hashes", action="store_true", help="Check the archived file hashes before any selected replay.")
    parser.add_argument("--refresh-hashes", action="store_true", help="Refresh only this manifest's file hashes after a deliberate bundle edit; does not certify mathematics.")
    args = parser.parse_args()
    manifest_path = args.manifest.resolve()
    manifest = json.loads(manifest_path.read_text())
    certificates = manifest["certificates"]
    by_id = {item["id"]: item for item in certificates}
    if len(by_id) != len(certificates):
        parser.error("Duplicate certificate IDs in manifest")
    groups = manifest["groups"]
    unknown = set(args.group) - set(groups)
    if unknown:
        parser.error("Unknown groups: " + ", ".join(sorted(unknown)))
    unknown = set(args.id) - set(by_id)
    if unknown:
        parser.error("Unknown certificate IDs: " + ", ".join(sorted(unknown)))

    if args.refresh_hashes:
        pending = []
        known = {item["path"] for item in manifest["files"]}
        for relative in manifest.get("pending_delivery_files", []):
            if (ROOT / relative).is_file():
                if relative not in known:
                    manifest["files"].append({"path": relative, "roles": ["definitive_proof_appendix"]})
                    known.add(relative)
            else:
                pending.append(relative)
        manifest["pending_delivery_files"] = pending
        manifest["files"].sort(key=lambda item: item["path"])
        for item in manifest["files"]:
            path = ROOT / item["path"]
            if not path.is_file():
                parser.error("Missing manifest file: " + item["path"])
            item["sha256"] = digest(path)
            item["bytes"] = path.stat().st_size
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
        print("Refreshed archival hashes; no certificate was replayed.")

    if args.check_hashes:
        failures = []
        for item in manifest["files"]:
            path = ROOT / item["path"]
            if not path.is_file() or digest(path) != item["sha256"]:
                failures.append(item["path"])
        if failures:
            print("Archival hash mismatches:\n" + "\n".join(failures), file=sys.stderr)
            return 2
        print(f"All {len(manifest['files'])} archival hashes match.")

    selected = set(by_id) if args.all else set(args.id)
    selected.update(item["id"] for item in certificates if item["group"] in args.group)
    if args.with_dependencies:
        pending = list(selected)
        while pending:
            for dep in by_id[pending.pop()].get("depends_on", []):
                if dep not in by_id:
                    parser.error("Unknown dependency: " + dep)
                if dep not in selected:
                    selected.add(dep)
                    pending.append(dep)
    # The archived order is a dependency-compatible serial order. Validate it.
    positions = {item["id"]: i for i, item in enumerate(certificates)}
    for item in certificates:
        for dep in item.get("depends_on", []):
            if dep not in positions or positions[dep] >= positions[item["id"]]:
                parser.error("Manifest dependency order is invalid: " + item["id"] + " -> " + dep)

    if args.list or (not selected and not args.refresh_hashes and not args.check_hashes):
        for key, description in groups.items():
            print(f"{key}: {description}")
        print()
        for item in certificates:
            if selected and item["id"] not in selected:
                continue
            print(f"[{item['group']}] {item['id']}: {item['title']}")
            print("  " + shlex.join([args.python] + item["argv"]))
        return 0
    if not selected:
        return 0

    chosen = [item for item in certificates if item["id"] in selected]
    for item in chosen:
        for relative in [item["argv"][0]] + item.get("inputs", []) + item.get("module_dependencies", []):
            if not (ROOT / relative).is_file():
                parser.error(f"Missing required file for {item['id']}: {relative}")
    if args.dry_run:
        print(f"Repository/package root: {ROOT}")
        for item in chosen:
            print(shlex.join([args.python] + item["argv"]))
        print(f"Selected {len(chosen)} serial commands; none executed.")
        return 0

    interpreter_check = subprocess.run([args.python, "-c", "import sys; sys.exit(2 if sys.flags.optimize else 0)"], cwd=ROOT)
    if interpreter_check.returncode:
        print("The selected child interpreter enables optimization or cannot run; assertions must remain enabled.", file=sys.stderr)
        return 2
    print("A full replay can take substantial time; every checker runs in a fresh serial process.", flush=True)
    args.logs.mkdir(parents=True, exist_ok=True)
    summary = {"manifest": str(manifest_path), "python": args.python, "serial_separate_processes": True, "results": []}
    for index, item in enumerate(chosen, 1):
        command = [args.python] + item["argv"]
        print(f"\n[{index}/{len(chosen)}] {item['id']}\n{shlex.join(command)}", flush=True)
        started = time.monotonic()
        log_path = args.logs / (item["id"] + ".log")
        with log_path.open("w") as log:
            process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
            try:
                assert process.stdout is not None
                for line in process.stdout:
                    print(line, end="", flush=True)
                    log.write(line)
                code = process.wait()
            except KeyboardInterrupt:
                process.terminate()
                process.wait()
                raise
        result = {"id": item["id"], "returncode": code, "elapsed_seconds": time.monotonic() - started, "log": str(log_path)}
        summary["results"].append(result)
        (args.logs / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        if code:
            print(f"Stopped after failed certificate {item['id']} (exit {code}).", file=sys.stderr)
            return code if code > 0 else 1
    print(f"\nAll {len(chosen)} selected certificate commands exited successfully.")
    print("This replays the listed arithmetic; analytic hypotheses are in the companion proof files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
