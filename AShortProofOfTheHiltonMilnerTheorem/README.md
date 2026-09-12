# A Short Proof of the Hilton-Milner Theorem

Lean 4 source-backed formalization setup for Denys Bulavka and Russ Woodroofe,
*A short proof of the Hilton-Milner Theorem*.

The active formalization is in:

- `AShortProofOfTheHiltonMilnerTheorem/`
- `AShortProofOfTheHiltonMilnerTheorem.lean`

The Lean declarations are split by proof role:

- `Basic.lean`: finite-family, uniformity, intersection, shifting, and extremal-family definitions.
- `MainTechnical.lean`: the main technical inequality and shifted/strict variants.
- `Shifting.lean`: Frankl--Furedi and strengthened shifting reductions.
- `HiltonMilner.lean`: the HM bound, uniqueness statement, and equality-case bridge lemmas.

## Status

- `lake build AShortProofOfTheHiltonMilnerTheorem` succeeds.
- Current version is a source-backed theorem skeleton with `sorry` proof obligations.
- The formalization focuses on finite set families, cross-intersection, shadows, shifting,
  the Hilton-Milner bound, and the uniqueness bridge described in the source.

See:

- `AShortProofOfTheHiltonMilnerTheorem/Blueprint.md`
- `docs/source/A_short_proof_of_the_Hilton-Milner_theorem.tex`
- `docs/bulavka_woodroofe2024_hilton_milner.pdf`
