#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

for required_command in lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required" >&2
    exit 2
  fi
done

sandbox=${COMPARATOR_BWRAP:-bwrap}
if ! command -v "$sandbox" >/dev/null 2>&1; then
  echo "error: install bubblewrap, or set COMPARATOR_BWRAP to its executable" >&2
  exit 2
fi
if ! "$sandbox" --ro-bind / / --unshare-user --unshare-net -- true; then
  cat >&2 <<'MESSAGE'
error: Bubblewrap cannot create the required user/network namespaces.
MESSAGE
  exit 2
fi

prefix=$(lean --print-prefix)
for tool in leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: the pinned Lean toolchain does not bundle $tool" >&2
    exit 2
  fi
done

config=$(mktemp)
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if "external_kernels" in config:
    raise SystemExit("error: external_kernels must not be in the submitted comparator.json")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron", "--jobs=2"],
}
pathlib.Path(destination).write_text(json.dumps(config) + "\n", encoding="utf-8")
PY
lake comparator --config "$config"
