# Engineering Lessons from the Luna Run

The campaign was evaluated against three operating goals: relentlessness,
resourcefulness with durable organization, and efficiency. Relentlessness is
useful only while verified work continues to reduce the target; it must not
become unbounded repetition.

## Correctness and recovery

- Target completion remained fail-closed: model reports, advisor prose, and
  checked helpers could not bypass exact source and placeholder verification.
- Verified edits were transactional. Failed parent checks restored the prior
  source while retaining diagnostics.
- Interrupted and timed-out Lean checks were treated as retryable evidence,
  never as proof success.
- Canonical queue ownership was strengthened so hallucinated paths or theorem
  identifiers cannot redirect an assigned target probe.
- Lean diagnostic selection now prefers target-local errors over unrelated
  warnings.

## Search liveness

- Equivalent failed endpoints need semantic fingerprints. Textually different
  wrappers around the same unresolved goal should not receive unlimited broad
  checks.
- After repeated timeout or identical diagnostics, the workflow should extract
  the failing local `have` into a top-level helper and check that helper in
  isolation.
- Advisor circuits and pending advice must be reflected in the model's visible
  tool surface, so the model does not spend a full turn selecting an action the
  manager will immediately reject.
- Negative evidence and unknown-identifier tombstones must survive context
  compression and campaign epochs.

## Graph and source organization

- A checked helper should be admitted to production source only when it adds a
  new dependency edge, discharges an open premise, or has an identified live
  consumer.
- Equivalent wrappers, renamed audits, finite examples dominated by a general
  result, and direct forwarding lemmas belong in graph evidence—not in the
  production Lean file.
- Disconnected research findings should remain available without preempting
  foreground proof probes or forcing insertion.
- The generated plan must expose the dependency path to the assigned theorem.
  An empty frontier next to rapidly growing helper inventory is a liveness
  alarm, not a sign of progress.
- Reusable helpers should move to a companion module when that reduces target
  context; private one-use helpers should remain close to their consumer.

## Performance

- LeanProbe and prepared-file caching should remain the primary edit-time
  checker. Context compression must not discard a warm incremental session for
  unchanged source.
- Provider transport timeouts must match the allowance shown by managed
  heartbeats; otherwise a long synthesis can be discarded halfway through its
  advertised window.
- Timing reports should separate resource admission, incremental preparation,
  Lean elaboration, fallback checking, and post-tool callbacks.
- Broad whole-file fallback should not run repeatedly after a focused local
  diagnostic already identifies the same failing span.

## Merge boundary

The LeanFlow changes developed during the campaign focus on deterministic
verification, source rollback, incremental checks, timeout-aware refactoring,
advisor admission, durable retry guards, canonical target routing, and clearer
transition visibility. More ambitious semantic theorem-subsumption and fully
automatic graph pruning remain research work; they should not be represented
as completed merely because the current safety gate is sound.
