# IMO 2026 LeanFlow Model Runs

This directory preserves two LeanFlow campaigns over the same six IMO 2026
formalizations. The archives intentionally distinguish completed proofs from
incomplete research attempts.

| Run | Model | Result | Archive |
| --- | --- | --- | --- |
| GPT-5.6-sol | `gpt-5.6-sol`, `xhigh` reasoning, Codex provider | Six kernel-checked solutions | [`GPT5.6-sol`](GPT5.6-sol) |
| GPT-5.6-luna | `gpt-5.6-luna`, `xhigh` reasoning, Codex provider | P1, P2, and P5 completed; P3 and P6 contain placeholders; P4 has a hard type error | [`GPT5.6-luna`](GPT5.6-luna) |

The [campaign report](leanflow-model-runs.html) gives a concise comparison of
the runs, their verification status, and the workflow lessons that informed
[LeanFlow PR #13](https://github.com/epfl-lara/LeanFlow/pull/13).

## Source and attribution

The theorem statements and initial Lean project came from Joseph Myers's
Apache-2.0-licensed [`jsm28/IMOLean`](https://github.com/jsm28/IMOLean)
repository. Lazar Milikic also contributed the accepted Problem 1 correction
in [`jsm28/IMOLean#1`](https://github.com/jsm28/IMOLean/pull/1). The original
copyright and license headers are retained in the Lean files.

These are research-assisted formalization runs. Lean and mathlib search,
public repositories, papers, and general web research were available to the
normal workflow. The archives document formal proof production, not claims of
independent discovery of the underlying mathematical solutions.

## Reproducibility

Each run is a standalone Lake project with a pinned toolchain and mathlib
revision. `SHA256SUMS` identifies the exact retained modules. The completed
run contains no project-local placeholders. The Luna archive deliberately
retains its five unresolved `sorry` placeholders and the P4 type mismatch so
the published state matches the stopped campaign.
