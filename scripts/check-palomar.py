#!/usr/bin/env python3
"""Compare Palomar statements and replay with Lean, NanoDa, and con-ron.

Run from any directory. This is a local check, not a Palomar submission.
The submitted JSON files remain within Palomar's configuration schema; kernel
commands are added only to temporary local configurations.
"""

import argparse
import json
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    available = ["QuantumQuery"]
    parser.add_argument("projects", nargs="*", help="QuantumQuery (default)")
    parser.add_argument(
        "--no-sandbox", action="store_true",
        help="check this trusted checkout without bubblewrap (needed on macOS)",
    )
    args = parser.parse_args()
    projects = args.projects or available
    if any(project not in available for project in projects):
        parser.error("project must be QuantumQuery")

    root = Path(__file__).resolve().parent.parent
    prefix = Path(subprocess.check_output(
        ["lean", "--print-prefix"], cwd=root, text=True,
    ).strip())
    kernels = {name: [str(prefix / "bin" / binary)] for name, binary in
               [("nanoda", "nanoda_bin"), ("con-ron", "con-ron")]}
    for command in kernels.values():
        if not Path(command[0]).is_file():
            parser.error(f"required toolchain checker is missing: {command[0]}")

    (root / ".lake").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="palomar-", dir=root / ".lake") as scratch:
        for project in projects:
            config = json.loads((root / "Palomar" / project / "comparator.json").read_text())
            config["external_kernels"] = kernels
            path = Path(scratch) / f"{project}.json"
            path.write_text(json.dumps(config, indent=2) + "\n")
            command = ["lake", "comparator", "--config", str(path)]
            if args.no_sandbox:
                command.append("--inadvisably-no-sandbox")
            print(f"Checking {project}: Comparator, NanoDa, con-ron, and Lean's kernel", flush=True)
            subprocess.run(command, cwd=root, check=True)


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from None
