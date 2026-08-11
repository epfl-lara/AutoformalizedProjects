import AShortProofOfTheHiltonMilnerTheorem.Basic

/-!
Source-backed statements for the main technical inequality and shifted variants.
-/

namespace AShortProofOfTheHiltonMilnerTheorem

/--
Source theorem `thm:MainTechnical`, lines 106--115.

Source proof: the paper proves this by induction on `n`.  The base case
`n = 2k - 1` uses complements.  The inductive step shifts the families, splits
according to whether a set contains `n`, applies induction to the not-`n` and
containing/deleted parts, treats the empty cases for `𝓑(n)`, and finishes by
Pascal identities for binomial coefficients.

Prover notes: introduce the two split families, prove the shadow and
cross-intersection hypotheses are inherited, use `Finset.card_powersetCard`,
`Finset.mem_shadow_iff`, and `Nat.choose` recurrence lemmas for the counting
part.
-/
theorem mainTechnical (n k : ℕ) (𝓐 𝓑 : SetFamily)
    (hk : 0 < k) (hkn : 2 * k ≤ n + 1)
    (hA : UniformFamily n (k - 1) 𝓐) (hB : UniformFamily n k 𝓑)
    (hcross : CrossIntersecting 𝓐 𝓑) (hne : 𝓑.Nonempty)
    (hshadow : Finset.shadow 𝓑 ⊆ 𝓐) :
    𝓐.card + 𝓑.card ≤ mainTechnicalBound n k := by
  sorry

/--
Source remark `line-224`, lines 224--227.

Source proof: no separate proof is given; the paper observes that the proof of
Hilton--Milner only needs the shifted special case of `thm:MainTechnical`.

Prover notes: once `mainTechnical` is available this follows immediately, but
it is kept as a separate source-backed target because the paper highlights the
shifted case as the actual dependency of the HM proof.
-/
theorem mainTechnical_shiftedSpecialCase (n k : ℕ) (𝓐 𝓑 : SetFamily)
    (hk : 0 < k) (hkn : 2 * k ≤ n + 1)
    (hA : UniformFamily n (k - 1) 𝓐) (hB : UniformFamily n k 𝓑)
    (hcross : CrossIntersecting 𝓐 𝓑) (hne : 𝓑.Nonempty)
    (hshadow : Finset.shadow 𝓑 ⊆ 𝓐)
    (_hshiftA : ShiftedOn n 𝓐) (_hshiftB : ShiftedOn n 𝓑) :
    𝓐.card + 𝓑.card ≤ mainTechnicalBound n k := by
  exact mainTechnical n k 𝓐 𝓑 hk hkn hA hB hcross hne hshadow

/--
Source proof-discussion helper from the uniqueness section, lines 303--326.

Source proof: for shifted families, the proof of `thm:MainTechnical` can be
modified by strengthening `𝓑.Nonempty` to `2 ≤ 𝓑.card`.  If `𝓑(n)` is empty,
the two-element hypothesis makes the estimate for `𝓐(n)` strict; if `𝓑(n)` is
nonempty, the equation `(2)` estimate is already strict when `4 ≤ k`.

Prover notes: reuse the induction split from `mainTechnical`, but carry strict
inequalities through the two cases for the containing-`n` part.
-/
theorem mainTechnical_shiftedStrictTwoB (n k : ℕ) (𝓐 𝓑 : SetFamily)
    (hk4 : 4 ≤ k) (hkn : 2 * k ≤ n + 1)
    (hA : UniformFamily n (k - 1) 𝓐) (hB : UniformFamily n k 𝓑)
    (hcross : CrossIntersecting 𝓐 𝓑) (hcardB : 2 ≤ 𝓑.card)
    (hshadow : Finset.shadow 𝓑 ⊆ 𝓐)
    (hshiftA : ShiftedOn n 𝓐) (hshiftB : ShiftedOn n 𝓑) :
    𝓐.card + 𝓑.card < mainTechnicalBound n k := by
  sorry

end AShortProofOfTheHiltonMilnerTheorem
