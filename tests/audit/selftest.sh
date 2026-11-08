#!/usr/bin/env bash
# The full-project positive audit is a separate required check.
set -euo pipefail
cd "$(dirname "$0")/../.."
exec python3 scripts/audit-selftest.py
