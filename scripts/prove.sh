#!/usr/bin/env bash
# prove.sh — End-to-end: Julia computation → JSON trace → Lean verification
#
# Usage:
#   ./prove.sh                    # run everything
#   ./prove.sh --julia-only       # just emit trace
#   ./prove.sh --lean-only FILE   # just verify a trace file
#   ./prove.sh --check-lean       # just typecheck the Lean library

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
JULIA_DIR="$ROOT/julia"
LEAN_DIR="$ROOT/lean"
TRACE_FILE="${TRACE_FILE:-$ROOT/trace.json}"

case "${1:-all}" in
  --julia-only)
    echo "=== Julia: emit proof trace ==="
    cd "$JULIA_DIR"
    julia test_emit.jl > "$TRACE_FILE" 2>/dev/null
    echo "Trace written to $TRACE_FILE"
    ;;

  --lean-only)
    TRACE_FILE="${2:-$TRACE_FILE}"
    echo "=== Lean: verify trace from $TRACE_FILE ==="
    julia "$ROOT/scripts/replay.jl" "$TRACE_FILE" > "$LEAN_DIR/Generated.lean"
    cd "$LEAN_DIR"
    lake build
    echo "✓ Lean verification passed"
    ;;

  --check-lean)
    echo "=== Lean: typecheck library ==="
    cd "$LEAN_DIR"
    lake build
    echo "✓ All Lean files typecheck"
    ;;

  all)
    echo "=== Step 1: Julia computation ==="
    cd "$JULIA_DIR"
    julia test_emit.jl > "$TRACE_FILE" 2>/dev/null
    echo "Trace written to $TRACE_FILE"

    echo "=== Step 2: Replay trace → Generated.lean ==="
    julia "$ROOT/scripts/replay.jl" "$TRACE_FILE" > "$LEAN_DIR/Generated.lean"
    echo "Generated proof written to lean/Generated.lean"

    echo "=== Step 3: Lean verification ==="
    cd "$LEAN_DIR"
    lake build
    echo ""

    echo "✓ Full loop: Julia computed → trace replayed → Lean verified"
    echo "  Trace: $TRACE_FILE"
    ;;

  *)
    echo "Usage: $0 [--julia-only|--lean-only FILE|--check-lean]"
    exit 1
    ;;
esac
