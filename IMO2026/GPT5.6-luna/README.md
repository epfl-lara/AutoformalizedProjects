# IMO 2026 — GPT-5.6-luna with LeanFlow

This directory preserves the exact Lean source state from an experimental
LeanFlow campaign using `gpt-5.6-luna` at `xhigh` reasoning effort through the
Codex provider. The campaign was stopped on 11 August 2026 after the Problem 6
search ceased producing a connected path toward the target.

## Status

This is an incomplete attempt archive, not a proof-complete solution set.

| Problem | Source status | Unresolved declarations |
| --- | --- | --- |
| P1 | Complete | None |
| P2 | Complete | None |
| P3 | Incomplete | Two local proof obligations in `result` |
| P4 | Does not elaborate | Hard type mismatch in `result` at line 2277 |
| P5 | Complete | None |
| P6 | Incomplete | `backward_affine_rigidity`, `globalize_eventual_affine_period`, and `result` |

The retained modules contain five project-local `sorry` placeholders: two in
P3 and three in P6. P4 contains no placeholder, but its final `result` fails
with a type mismatch between the retained `π / n` guarantee and the expected
`π / (n + 1)` target. These failures are intentional in the archive and make
it an honest representation of the stopped run. P2 and P6 import their
companion helper modules. The small P3 and P4 helper modules are also retained
as part of the exact exploratory source state, although their final modules do
not import them.

## What the run established

The model completed three of the six formalizations. It also developed a large
body of checked intermediate material for P3 and P6, including explicit
negative results that closed several tempting but invalid P6 routes. That
material remains useful research evidence, but checked helpers do not by
themselves establish the assigned theorem.

At the stopping point, the P6 graph reported 183 proved nodes, three formally
false nodes, one active proving node, and an empty dependency frontier for
`backward_affine_rigidity`. The source had grown to 5,388 lines plus a 311-line
helper module. This combination—large verified inventory with no connected
frontier—was the decisive signal that further continuation was no longer an
efficient use of the model.

## Workflow evidence

The [`run-evidence`](run-evidence) directory contains a curated campaign
summary and engineering lessons. The complete raw LeanFlow state, logs,
checkpoints, provider transcripts, and caches remain outside this repository;
they are substantially larger and may include machine-local operational data.

`SHA256SUMS` records the exact ten retained Lean modules.

## Source and attribution

The theorem statements and initial project structure came from Joseph Myers's
Apache-2.0-licensed
[`jsm28/IMOLean`](https://github.com/jsm28/IMOLean) repository. Lazar Milikic
contributed the accepted Problem 1 correction in
[`jsm28/IMOLean#1`](https://github.com/jsm28/IMOLean/pull/1). Original source
headers and the project license are preserved.

The run used LeanFlow's normal research capabilities, including Lean and
mathlib search, public repositories, papers, and general web research. It is a
research-assisted formalization attempt, not an independent-solution claim.

## Inspect

To reproduce the placeholder inventory:

```bash
rg -n --glob '*.lean' '\b(sorry|admit|axiom|unsafe)\b' .
```

To reproduce the project check:

```bash
lake exe cache get
lake build IMO2026
```

The build is expected to fail at P4. P1, P2, P3, P5, and P6 elaborate; P3 and
P6 do so only because Lean admits the five explicitly retained placeholders.
