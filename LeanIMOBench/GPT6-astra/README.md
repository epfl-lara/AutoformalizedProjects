# Lean-IMO-Bench — the 18 LEAP did not solve

Lean 4 proofs of the eighteen IMO-LeanProofBench problems that are **not**
covered by LEAP's published solutions, produced with
[LeanFlow](https://github.com/epfl-lara/LeanFlow) and `gpt-6-astra` through the
Codex provider.

## Status

- All 18 theorems are proved in `LeanIMOBench/Basic/` and
  `LeanIMOBench/Advanced/`, supported by 107 helper lemmas in `LeanFlowProofs/`.
- Every problem statement is **byte-identical** to the published benchmark
  statement; only the `sorry` was replaced. This was checked against the frozen
  baseline before publication, not merely asserted.
- The project has no project-local `sorry`, `admit`, custom `axiom`, or `unsafe`
  declaration, and every proof was kernel-checked with only `propext`,
  `Classical.choice` and `Quot.sound`.
- `lake build LeanIMOBench` completed successfully (8831 jobs, 0 errors) on
  8 September 2026, using Lean `v4.33.1` with mathlib pinned to
  `0df444a360eaa60ab8c11dca51a86af692955474`.

`SHA256SUMS` records the exact modules retained from the campaign.

## Source

The problems come from **IMO-LeanProofBench**, the Lean half of IMO-Bench
(Luong et al., *Towards Robust Mathematical Reasoning*), published in
[`google-deepmind/superhuman`](https://github.com/google-deepmind/superhuman)
as `imobench/lean_proof_bench_v2.csv`. The informal problems and their Lean
formalizations are the benchmark authors' work and are reproduced here unchanged
under CC-BY 4.0.

The benchmark has 60 problems. **LEAP** (Kung et al.,
[arXiv:2606.03303](https://arxiv.org/abs/2606.03303)) reports solving 42 and
publishes those proofs under `leap/solutions/LEAN-IMO-Bench/`. The eighteen here
are exactly the complement: the problems for which no LEAP solution file exists.

## Why these eighteen are the hard ones

LEAP's misses are not spread evenly across the benchmark. Its published
solutions cover:

| Category | LEAP solved |
| --- | --- |
| Algebra | 16 / 16 — all |
| Number theory | 14 / 14 — all |
| Combinatorics | 10 / 16 |
| Geometry | **2 / 14** |

So this set is **12 Geometry and 6 Combinatorics, with no Algebra and no Number
theory at all**. It is a concentrated sample of the two areas where a strong
formal prover was falling down, not a random residue.

Three things make them hard.

**Formalized Euclidean geometry has no synthetic shortcut.** `PB-Advanced-003`
asks one to show that three circumcircles built from the mixtilinear incircle
touch points are coaxial — a sentence of synthetic geometry, and a great deal of
mathlib. Every configuration fact must be routed through `EuclideanSpace`,
`Cospherical`, `affineSpan`, `orthogonalProjection` and inner-product algebra, so
a step a human takes from a picture becomes an explicit coordinate or
power-of-a-point computation. The retained helper lemmas show it directly: they
are named for tangency frames, altitude feet, incenter displacement and coaxial
secants.

**The terms get genuinely large.** These configurations inline substantial
instance towers. The kernel type of `PBAdvanced009` prints at 49.8 million
characters, because `orthogonalProjection (affineSpan R {A, G})` re-expands its
`HasOrthogonalProjection` and finite-dimensionality machinery at every
occurrence. Tooling that assumes a declaration's type is small breaks on these
before any mathematics is attempted.

**Twelve of the eighteen are new problems.** The benchmark marks them
`Novel Problem`: composed for IMO-ProofBench and never published, so there is no
informal write-up, no forum thread and no prior formalization to draw on. The
remaining six are `(Modified) IMO 2024 P3/P4/P5`, `USAMO 2025`, a modified
`IMO Shortlist 2008 G5`, and one folklore problem — recent or altered enough
that a memorized solution is unlikely to apply.

## Results

Nodes is the size of the proof graph LeanFlow built: the root theorem plus its
helper obligations.

| Problem | Category | Level | Benchmark source | Nodes | API calls | Wall (min) |
| --- | --- | --- | --- | --- | --- | --- |
| `PB-Basic-025` | Geometry | IMO-easy | folklore | 6 | 114 | 16 |
| `PB-Basic-026` | Geometry | IMO-medium | Novel Problem | 8 | 199 | 27 |
| `PB-Basic-028` | Geometry | IMO-medium | Novel Problem | 7 | 175 | 27 |
| `PB-Basic-029` | Geometry | IMO-medium | (modified) IMO Shortlist 2008 G5 | 2 | 162 | 57 |
| `PB-Basic-030` | Geometry | IMO-easy | Novel Problem | 2 | 169 | 97 |
| `PB-Advanced-002` | Combinatorics | IMO-medium | Novel Problem | 10 | 106 | 21 |
| `PB-Advanced-003` | Geometry | IMO-hard | Novel Problem | 5 | 674 | 221 |
| `PB-Advanced-004` | Combinatorics | IMO-easy | Novel Problem | 5 | 88 | 18 |
| `PB-Advanced-005` | Geometry | IMO-medium | Novel Problem | 6 | 105 | 24 |
| `PB-Advanced-009` | Geometry | IMO-hard | Novel Problem | 7 | 200 | 84 |
| `PB-Advanced-010` | Geometry | IMO-medium | Novel Problem | 8 | 158 | 44 |
| `PB-Advanced-015` | Geometry | IMO-hard | Novel Problem | 10 | 323 | 53 |
| `PB-Advanced-016` | Geometry | IMO-easy | Novel Problem | 7 | 202 | 35 |
| `PB-Advanced-018` | Combinatorics | IMO-hard | Novel Problem | 9 | 446 | 94 |
| `PB-Advanced-021` | Combinatorics | IMO-hard | (Modified) IMO 2024 P3 | 12 | 149 | 28 |
| `PB-Advanced-022` | Geometry | IMO-easy | (Modified) IMO 2024 P4 | 8 | 229 | 30 |
| `PB-Advanced-023` | Combinatorics | IMO-medium | (Modified) IMO 2024 P5 | 7 | 147 | 31 |
| `PB-Advanced-027` | Combinatorics | IMO-hard | USAMO 2025 | 6 | 62 | 15 |

Totals: 3708 API calls, 109M input and 1.6M output tokens, about seven hours of
wall-clock time across two and then three parallel lanes.

## Method

Each problem was proved in isolation: its own Lake project, its own frozen
budget, no shared state with the other seventeen. LeanFlow ran in research mode
with a top-down search order, and with the prover and the orchestrator at
**different reasoning efforts** — planning, review and research at `xhigh`, the
prover and negation passes at `low`. The orchestrator decomposes the target into
named helper obligations, the cheap prover discharges them, and results are
kernel-checked before being integrated.

That split shows up in the numbers. Helper lemmas are discharged cheaply, 6 to 33
calls each; the expensive part is assembling them into the root theorem.
Seventeen of the eighteen never needed the plan revised at all — only
`PB-Advanced-003` had a node block and go through negation and replanning, and it
still finished.

Internet access was disabled for every run (`allow_internet=false`), and Lean
checks ran inside a network-isolated sandbox. That matters here because LEAP's
own Lean proofs for the other 42 problems are public: for these eighteen no LEAP
solution exists, and for the twelve novel problems no solution of any kind has
ever been published.

**One caveat, recorded because it affects comparability.** Twelve of the eighteen
ran with local library search unavailable: `ripgrep` was missing from the
campaign container, so `search_project` and the offline branch of `lean_search`
failed on every call. The remaining six — `PB-Advanced-016`, `-018`, `-021`,
`-022`, `-023`, `-027` — ran with it working. These are two sub-conditions, not
one uniform arm. The twelve are, if anything, the more constrained result.

## Relationship to the published benchmark

The benchmark statements were verified upstream against Lean and mathlib
`4.27.0`; this project uses `4.33.1`. Every statement was checked to elaborate
unchanged at `4.33.1` before any proving began, but the proofs have not been
re-verified at `4.27.0`, so this is not a drop-in submission to the benchmark as
published.

## Reproduce

From this directory:

```bash
lake exe cache get
lake build LeanIMOBench
```

Source-level hygiene check:

```bash
rg -n --glob '*.lean' '\b(sorry|admit|axiom|unsafe)\b' LeanIMOBench LeanFlowProofs
```

The build should succeed and the search should produce no matches.

## License

Apache License 2.0; see `LICENSE`. The benchmark problem statements are
(c) 2026 Google LLC, reproduced unchanged under CC-BY 4.0 from
`google-deepmind/superhuman`.
