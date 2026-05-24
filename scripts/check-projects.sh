#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

check_project() {
  local project="$1"
  local target="$2"

  echo "==> ${project}"
  (
    cd "${ROOT}/${project}"
    lake exe cache get
    lake build "${target}"
  )
}

check_project PythagoreanPolynomialParametrization Pyth
check_project QuantizingPythagoreanTriples Pythagore2
check_project AShortProofOfTheHiltonMilnerTheorem AShortProofOfTheHiltonMilnerTheorem
check_project CramerWoldTheorem CramerWoldTheorem
