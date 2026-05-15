# EPFLemma Prep: PythagoreanPolynomialParametrization

EPFLemma checkout:

```bash
/localhome/milikic/EPFLemma
```

Initialize this Lean project for EPFLemma on `larapc2`:

```bash
cd /localhome/milikic/EPFLemma
source .venv/bin/activate
python -m epflemma_cli.main project init /localhome/milikic/AutoformalizedProjects/PythagoreanPolynomialParametrization --name PythagoreanPolynomialParametrization
```

Lean checks:

```bash
cd /localhome/milikic/AutoformalizedProjects/PythagoreanPolynomialParametrization
lake build Pyth.Main
rg "\\bsorry\\b|\\badmit\\b" Pyth --glob '*.lean'
```

Recommended proof workflow:

1. Prove one declaration at a time.
2. Keep the blueprint updated when a statement changes.
3. Commit after each coherent group of completed proofs.
