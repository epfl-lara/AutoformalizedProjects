# Publication Limitations

This repository is suitable for public inspection as a collection of Lean
formalization projects, but readers should understand the following limitations.

## Formal Verification Scope

- A successful Lean build means the checked Lean statements typecheck under the
  pinned dependencies for that project.
- A successful build does not by itself prove that a Lean statement is the exact
  best translation of the informal paper statement.
- The project blueprints record source mapping, representation choices, and known
  scope differences. They should be read together with the Lean files.

## Completed vs. Work in Progress

- Projects on `main` are expected to have no project-local `sorry`, `admit`,
  custom `axiom`, or `unsafe`.
- Work-in-progress projects may build with `sorry` warnings and are kept on draft
  PR branches until they are proof-complete.
- A source-stated open conjecture may be represented as an explicit axiom only
  when the README and blueprint say so.

## Source Papers and Third-Party Material

- Paper links in the README point to public source pages such as arXiv.
- Local documentation may contain source extracts, PDFs, or reference material
  used during formalization. Before broad publication, check that each included
  third-party artifact is redistributable or replace it with a citation/link.
- The Apache 2.0 license applies to this repository's original code and
  documentation. It does not relicense third-party papers or reference material.

## Autoformalization Caveats

- Parts of the repository were produced with AI-assisted formalization workflows.
- Human review should focus on statement fidelity, proof dependencies, and
  whether source assumptions are represented faithfully.
- Mathematical names and decomposition lemmas may be engineering artifacts rather
  than claims appearing verbatim in the source papers.

## No Endorsement

This repository does not imply endorsement by the authors of the source papers
unless explicitly stated.
