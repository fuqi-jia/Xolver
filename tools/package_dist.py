#!/usr/bin/env python3
"""
Package NLColver benchmark distribution for server deployment.

Produces a self-contained tar.gz with:
- nlcolver binary
- Python benchmark/analyzer scripts
- CaseStats schema compatibility wrapper

Usage:
    python3 tools/package_dist.py --build-dir build_old --output nlcolver-dist.tar.gz

Server requirements (Ubuntu 22.04+):
    sudo apt-get install -y libgmp10 libmpfr6 python3
"""

import argparse
import os
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path


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
    parser = argparse.ArgumentParser(description="Package NLColver for server deployment")
    parser.add_argument("--build-dir", default="build_old", help="Build directory containing nlcolver binary")
    parser.add_argument("--output", default="nlcolver-dist.tar.gz", help="Output tar.gz path")
    args = parser.parse_args()

    build_dir = Path(args.build_dir)
    binary = build_dir / "bin" / "nlcolver"
    externals = check_binary(binary)

    # Warn about glibc compatibility
    result = subprocess.run(["ldd", "--version"], capture_output=True, text=True)
    glibc_ver = result.stdout.splitlines()[0] if result.stdout else "unknown"
    print(f"Build host glibc: {glibc_ver}")
    print("WARNING: Binary may fail on servers with older glibc.")
    print("  Safe practice: compile on the OLDEST target server (Panda6, Ubuntu 22.04).")
    print()

    with tempfile.TemporaryDirectory() as tmpdir:
        dist = Path(tmpdir) / "nlcolver-dist"
        dist.mkdir()

        # Binary
        (dist / "bin").mkdir()
        subprocess.run(["cp", str(binary), str(dist / "bin" / "nlcolver")], check=True)
        subprocess.run(["chmod", "+x", str(dist / "bin" / "nlcolver")], check=True)

        # Python scripts
        (dist / "tools").mkdir()
        for script in ["run_benchmark.py", "analyze_benchmark.py", "bench_server.py", "freeze_baseline.py"]:
            src = Path("tools") / script
            if src.exists():
                subprocess.run(["cp", str(src), str(dist / "tools" / script)], check=True)

        # README
        readme = dist / "README.txt"
        readme.write_text(f"""NLColver Benchmark Distribution
================================

Server setup:
    sudo apt-get install -y libgmp10 libmpfr6 python3

Run benchmark:
    python3 tools/run_benchmark.py --solver ./bin/nlcolver --logic QF_LIA -j 128 -t 100

Analyze results:
    python3 tools/analyze_benchmark.py --current <run_dir> --output <analysis_dir>

External dependencies on this binary:
{chr(10).join("  " + e for e in externals)}

Build host glibc: {glibc_ver}
""")

        # Create tar.gz
        output_path = Path(args.output).resolve()
        with tarfile.open(output_path, "w:gz") as tar:
            tar.add(dist, arcname="nlcolver-dist")

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
