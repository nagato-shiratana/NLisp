"""Compare NLisp execution and certificate verification paths.

The harness records raw per-run timings and sampled peak resident memory.
It is an experiment, not a proof of an asymptotic complexity bound.
"""

from __future__ import annotations

import argparse
import csv
import os
import pathlib
import subprocess
import sys
import time

try:
    import psutil
except ImportError:  # Memory sampling is optional on machines without psutil.
    psutil = None


ROOT = pathlib.Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "tools" / "verify_lean.py"
DEFAULT_EXAMPLES = ("factorial", "macros", "polymorphism")


def sampled_memory(process: subprocess.Popen[bytes]) -> int | None:
    if psutil is None:
        return None
    try:
        root = psutil.Process(process.pid)
        total = root.memory_info().rss
        for child in root.children(recursive=True):
            try:
                total += child.memory_info().rss
            except psutil.Error:
                pass
        return total
    except psutil.Error:
        return None


def measure(command: list[str], env: dict[str, str]) -> tuple[float, int | None]:
    process = subprocess.Popen(command, cwd=ROOT, env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    started = time.perf_counter()
    peak = sampled_memory(process)
    while process.poll() is None:
        current = sampled_memory(process)
        if current is not None:
            peak = current if peak is None else max(peak, current)
        time.sleep(0.01)
    stdout, stderr = process.communicate()
    elapsed = time.perf_counter() - started
    if process.returncode != 0:
        raise RuntimeError(
            f"command failed ({process.returncode}): {' '.join(command)}\n"
            f"{stdout.decode(errors='replace')}\n{stderr.decode(errors='replace')}"
        )
    return elapsed, peak


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nlisp", required=True, help="path to the NLisp executable")
    parser.add_argument("--lake", required=True, help="path to the elan lake launcher")
    parser.add_argument("--output-dir", required=True, help="directory for certificates and CSV")
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("examples", nargs="*", default=list(DEFAULT_EXAMPLES))
    args = parser.parse_args()

    nlisp = pathlib.Path(args.nlisp).resolve()
    lake = pathlib.Path(args.lake).resolve()
    output_dir = pathlib.Path(args.output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    elan_home = ROOT / ".tools" / "elan-home"
    env["ELAN_HOME"] = str(elan_home)
    env["PATH"] = str(elan_home / "bin") + os.pathsep + env.get("PATH", "")

    rows: list[dict[str, object]] = []
    for example in args.examples:
        source = ROOT / "examples" / f"{example}.nlisp"
        if not source.is_file():
            raise FileNotFoundError(source)
        certificate = output_dir / f"{example}.lean"
        expansion = subprocess.run([str(nlisp), "expand", str(source)], cwd=ROOT,
                                   env=env, capture_output=True, check=True)
        common = [sys.executable, str(BRIDGE), "--nlisp", str(nlisp), "--lake", str(lake)]
        for repetition in range(1, args.repeats + 1):
            commands = [
                ("no_certificate_run", [str(nlisp), "run", str(source)]),
                ("certificate_generation", common + [str(source), "--output", str(certificate)]),
            ]
            for mode, command in commands:
                seconds, peak = measure(command, env)
                rows.append({
                    "example": example,
                    "repetition": repetition,
                    "mode": mode,
                    "seconds": f"{seconds:.6f}",
                    "peak_rss_bytes_sampled": "" if peak is None else peak,
                    "source_bytes": source.stat().st_size,
                    "expanded_bytes": len(expansion.stdout),
                    "certificate_bytes": certificate.stat().st_size if certificate.exists() else "",
                })
            for mode, extra in (
                ("verification_with_reexecution", ["--verify-certificate", str(certificate)]),
                ("independent_verification", ["--verify-certificate", str(certificate), "--independent"]),
            ):
                seconds, peak = measure(common + extra, env)
                rows.append({
                    "example": example,
                    "repetition": repetition,
                    "mode": mode,
                    "seconds": f"{seconds:.6f}",
                    "peak_rss_bytes_sampled": "" if peak is None else peak,
                    "source_bytes": source.stat().st_size,
                    "expanded_bytes": len(expansion.stdout),
                    "certificate_bytes": certificate.stat().st_size,
                })

    result = output_dir / "benchmark-results.csv"
    with result.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
