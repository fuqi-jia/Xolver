#!/usr/bin/env python3
"""
Package Xolver benchmark distribution for server deployment.

Produces a self-contained tar.gz with:
- xolver binary
- Python benchmark/analyzer scripts
- CaseStats schema compatibility wrapper

Usage:
    python3 tools/release/package_dist.py --build-dir build --output xolver-dist.tar.gz

Server requirements (Ubuntu 22.04+):
    sudo apt-get install -y libgmp10 libmpfr6 python3
"""

import argparse
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


def check_binary(binary: Path):
    """Verify binary exists and check dynamic dependencies."""
    if not binary.exists():
        print(f"ERROR: Binary not found: {binary}")
        sys.exit(1)

    result = subprocess.run(["ldd", str(binary)], capture_output=True, text=True)
    externals = []
    for line in result.stdout.splitlines():
        if "=>" in line and not any(
            x in line for x in ["linux-vdso", "ld-linux", "libc.so", "libm.so", "libdl.so", "libpthread.so", "librt.so"]
        ):
            externals.append(line.strip())

    print(f"Binary: {binary}")
    print(f"External runtime dependencies ({len(externals)}):")
    for dep in externals:
        print(f"  {dep}")
    print()
    return externals


def main():
    parser = argparse.ArgumentParser(description="Package Xolver for server deployment")
    parser.add_argument("--build-dir", default=str(REPO_ROOT / "build"), help="Build directory containing xolver binary")
    parser.add_argument("--output", default="xolver-dist.tar.gz", help="Output tar.gz path")
    args = parser.parse_args()

    build_dir = Path(args.build_dir)
    binary = build_dir / "bin" / "xolver"
    externals = check_binary(binary)

    # Warn about glibc compatibility
    result = subprocess.run(["ldd", "--version"], capture_output=True, text=True)
    glibc_ver = result.stdout.splitlines()[0] if result.stdout else "unknown"
    print(f"Build host glibc: {glibc_ver}")
    print("WARNING: Binary may fail on servers with older glibc.")
    print("  Safe practice: compile on the OLDEST target server (Panda6, Ubuntu 22.04).")
    print()

    with tempfile.TemporaryDirectory() as tmpdir:
        dist = Path(tmpdir) / "xolver-dist"
        dist.mkdir()

        # Binary
        (dist / "bin").mkdir()
        shutil.copy2(binary, dist / "bin" / "xolver")
        (dist / "bin" / "xolver").chmod(0o755)

        # Python scripts
        (dist / "tools").mkdir()
        for script in [
            "regression/run_benchmark.py",
            "regression/run_regression.py",
            "differential/analyze_benchmark.py",
            "differential/freeze_baseline.py",
            "differential/compare_benchmarks.py",
            "differential/diff_common.sh",
            "differential/diff_ingest.py",
        ]:
            src = REPO_ROOT / "tools" / script
            dst = dist / "tools" / script
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)  # A missing required tool must fail packaging.

        # README
        readme = dist / "README.txt"
        readme.write_text(f"""Xolver Benchmark Distribution
================================

Server setup:
    sudo apt-get install -y libgmp10 libmpfr6 python3

Run benchmark:
    python3 tools/regression/run_benchmark.py --solver ./bin/xolver --logic QF_LIA -j 4 -t 100

Analyze results:
    python3 tools/differential/analyze_benchmark.py --current <run_dir> --output <analysis_dir>

External dependencies on this binary:
{chr(10).join("  " + e for e in externals)}

Build host glibc: {glibc_ver}
""")

        # Create tar.gz
        output_path = Path(args.output).resolve()
        with tarfile.open(output_path, "w:gz") as tar:
            tar.add(dist, arcname="xolver-dist")

        size_mb = output_path.stat().st_size / (1024 * 1024)
        print(f"Created: {output_path} ({size_mb:.2f} MB)")
        print(f"Contents:")
        for root, dirs, files in os.walk(dist):
            for f in files:
                p = Path(root) / f
                rel = p.relative_to(dist)
                size = p.stat().st_size / 1024
                print(f"  {rel} ({size:.1f} KB)")


if __name__ == "__main__":
    main()
