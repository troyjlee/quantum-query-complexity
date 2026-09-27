#!/usr/bin/env python3
"""Build a separate Lake project that consumes the current library checkout."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parent.parent
    environment = os.environ.copy()
    environment.pop("LEAN_PATH", None)
    environment.pop("LEAN_SRC_PATH", None)
    environment.setdefault("LEAN_NUM_THREADS", "1")
    with tempfile.TemporaryDirectory(prefix="quantum-query-downstream-") as directory:
        client = Path(directory)
        (client / "lakefile.toml").write_text(
            'name = "QuantumQueryDownstream"\n'
            'defaultTargets = ["Downstream"]\n\n'
            '[[require]]\nname = "QuantumQueryComplexity"\n'
            f'path = {json.dumps(str(root))}\n\n'
            '[[lean_lib]]\nname = "Downstream"\n'
        )
        shutil.copy2(root / "lean-toolchain", client / "lean-toolchain")
        shutil.copy2(root / "tests/downstream/Downstream.lean", client / "Downstream.lean")
        packages = client / ".lake/packages"
        packages.mkdir(parents=True)
        manifest = json.loads((root / "lake-manifest.json").read_text())
        for package in manifest["packages"]:
            cached = root / ".lake/packages" / package["name"]
            if cached.is_dir():
                (packages / package["name"]).symlink_to(cached.resolve(), target_is_directory=True)
        for command in (["lake", "update"], ["lake", "build"]):
            subprocess.run(command, cwd=client, env=environment, check=True)
        print("Downstream Lake project built successfully using the library dependency.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from None
