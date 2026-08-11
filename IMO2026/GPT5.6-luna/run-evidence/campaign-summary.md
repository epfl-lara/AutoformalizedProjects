# GPT-5.6-luna Campaign Summary

## Configuration

- Model: `gpt-5.6-luna`
- Reasoning effort: `xhigh`
- Provider: Codex
- Workflow: LeanFlow autonomous proving and research campaign
- Budget: 5m tokens per problem
- Source restriction: the previously completed IMO 2026 solution archive was
  excluded from the model's task-specific research inputs

All normal non-solution research capabilities remained available, including
Lean declarations, mathlib sources, papers, public code, and web search.

## Problem outcomes

### P1 — complete

The retained file has no project-local placeholder (sorry). Lean accepted the final solution, no task-local declarations were modified, and the model produced a valid proof of the target statement.

### P2 — complete

The retained file has no project-local placeholder (sorry). Lean accepted the final solution, no task-local declarations were modified, and the model produced a valid proof of the target statement.

### P3 — incomplete

The model built a substantial geometric and summation scaffold but left two
local obligations inside `result` after budget exhaustion. 

### P4 — invalid final attempt

The retained file has no project-local placeholder, but a clean Lake build
rejects `result` at line 2277. After simplification, the candidate provides a
winning guarantee for `π / n` where the target expects `π / (n + 1)`. This is
a hard type error, so P4 is not counted as complete.

### P5 — complete

The retained file has no project-local placeholder and keeps the formal target
statement unchanged. Lean accepted the final solution, the model produced a valid proof of the target statement.

### P6 — incomplete

The model generated extensive checked infrastructure and formally refuted
three proposed routes. The final active route attempted to globalize an
eventual affine-period relation. Three declarations remain open:

1. `backward_affine_rigidity`
2. `globalize_eventual_affine_period`
3. `result`

The graph at shutdown reported 183 proved nodes and an empty dependency
frontier for the active helper. Repeated attempts changed wrappers and helper
names without discharging the same reverse-boundary obligation. LeanFlow
therefore preserved the source and state, then the campaign was stopped by the
operator.

## Interpretation

The run demonstrates both capability and a failure mode. GPT-5.6-luna solved
three substantial formalizations and produced considerable valid mathematics
on the remaining three. On P6, however, the workflow did not sufficiently
constrain new helper admission to a live dependency path. The resulting source
growth made the model less oriented even while deterministic verification
continued to prevent false completion. 
