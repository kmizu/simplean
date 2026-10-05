#!/usr/bin/env bash
# Extract Simplean to Scala 3 with Lens, check the extraction against the
# golden file, then compile + run it with scala-cli and diff the printed
# results against scala/expected.txt (Lean's own `#eval` ground truth, see
# scripts/expected.lean).
#
#   scripts/scala-check.sh                  # check; non-zero exit on any mismatch
#   UPDATE_GOLDEN=1 scripts/scala-check.sh  # accept the fresh extraction as golden
#   SCALA_CLI=/path/to/scala-cli scripts/scala-check.sh
set -euo pipefail
cd "$(dirname "$0")/.."

GEN=scala/generated/Simplean.scala
GOLDEN=tests/golden/Simplean.scala
EXPECTED=scala/expected.txt
SCALA_CLI=${SCALA_CLI:-$(command -v scala-cli || echo "$HOME/.local/share/coursier/bin/scala-cli")}

echo "== [1/4] build extractor (lake build Simplean Lens extract)"
lake build Simplean Lens extract >/dev/null

echo "== [2/4] extract -> $GEN"
lake exe extract --out "$GEN"

echo "== [3/4] golden check ($GOLDEN)"
if [ "${UPDATE_GOLDEN:-0}" = "1" ]; then
  mkdir -p "$(dirname "$GOLDEN")"
  cp "$GEN" "$GOLDEN"
  echo "golden UPDATED - review with git diff"
elif [ ! -f "$GOLDEN" ]; then
  echo "FAIL: missing $GOLDEN (run with UPDATE_GOLDEN=1)" >&2
  exit 1
elif ! diff -u "$GOLDEN" "$GEN"; then
  echo "FAIL: fresh extraction differs from $GOLDEN (UPDATE_GOLDEN=1 to accept)" >&2
  exit 1
else
  echo "golden OK"
fi

echo "== [4/4] scala-cli run + diff against $EXPECTED"
ACTUAL=$(mktemp)
trap 'rm -f "$ACTUAL"' EXIT
"$SCALA_CLI" run scala --server=false -q > "$ACTUAL"
cat "$ACTUAL"
if ! diff -u "$EXPECTED" "$ACTUAL"; then
  echo "FAIL: Scala results differ from $EXPECTED" >&2
  exit 1
fi
echo "scala-check: OK ($(wc -l < "$EXPECTED") programs match Lean)"
