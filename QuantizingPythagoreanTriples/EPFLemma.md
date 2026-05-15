# EPFLemma Prep: QuantizingPythagoreanTriples

EPFLemma checkout:

```bash
/localhome/milikic/EPFLemma
```

Initialize this Lean project for EPFLemma on `larapc2`:

```bash
cd /localhome/milikic/EPFLemma
source .venv/bin/activate
python -m epflemma_cli.main project init /localhome/milikic/AutoformalizedProjects/QuantizingPythagoreanTriples --name QuantizingPythagoreanTriples
```

Lean checks:

```bash
cd /localhome/milikic/AutoformalizedProjects/QuantizingPythagoreanTriples
lake build Pythagore2.Main
rg "\\bsorry\\b|\\badmit\\b" Pythagore2 --glob '*.lean'
rg "^axiom\\b" Pythagore2 --glob '*.lean'
```

Recommended proof workflow:

1. Prove q-rational construction facts before attacking the q-Pythagorean theorem.
2. Keep `unimodality_conjecture` as the only axiom.
3. Update the blueprint whenever a source statement is refined.
