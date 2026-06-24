# Contributing

Thank you for improving these formalizations. This repository is intended to be
public-facing, so contributions should keep the main branch small, buildable, and
clear about proof status.

## Branch Policy

- `main` is reserved for completed projects.
- A completed project must build and have no project-local `sorry`, `admit`,
  custom `axiom`, or `unsafe` in Lean files.
- Work-in-progress projects should live on separate draft pull requests until
  they meet the completed-project standard.
- Keep unrelated project work in separate branches and PRs.

## Development Workflow

1. Work from a topic branch.
2. Keep changes scoped to one project or one repository-level maintenance task.
3. Run the relevant Lake build before opening a PR.
4. Update the project README and blueprint whenever theorem coverage, proof
   status, or source mapping changes.
5. Mark PRs as draft if any Lean declarations still rely on `sorry`, `admit`, or
   project-local axioms.

For the completed projects on `main`, run:

```bash
./scripts/check-projects.sh
```

For a single project, run the Lake build from that project directory, for
example:

```bash
cd PythagoreanPolynomialParametrization
lake build Pyth
```

## Source-Backed Formalization Standards

- Every theorem meant to represent paper content should be traceable to a source
  statement, source proof block, or explicit modeling choice.
- Representation differences from the paper should be documented in the project
  blueprint.
- Avoid silently weakening a theorem to make proof completion easier.
- Keep explanatory or externally cited material separate from the main theorem
  path when practical.

## Licensing

By contributing, you agree that your contribution is licensed under the Apache
License 2.0 unless explicitly agreed otherwise before submission.

Do not add third-party source files, PDFs, datasets, or generated artifacts unless
their license permits redistribution in this repository and their provenance is
documented.
