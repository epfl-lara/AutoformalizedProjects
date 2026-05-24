import AShortProofOfTheHiltonMilnerTheorem.MainTechnical
import AShortProofOfTheHiltonMilnerTheorem.Shifting

/-!
Hilton--Milner theorem statements and uniqueness bridge lemmas.
-/

namespace AShortProofOfTheHiltonMilnerTheorem

/--
Source theorem `thm:HM`, lines 91--95; proof in lines 206--223.

Source proof: first use the Frankl--Füredi shifting lemma to reduce to a shifted
family.  Split the shifted family into sets containing `1` and sets not
containing `1`; delete `1` from the first part to obtain `𝓐`, and call the
second part `𝓑`.  Shiftedness gives `∂𝓑 ⊆ 𝓐`; pairwise intersection gives
cross-intersection; empty total intersection gives nonemptiness of both parts.
Then apply `thm:MainTechnical` on the remaining ground set.

Prover notes: the Lean proof should make the reindexing from `{2, ..., n}` to a
standard `[n-1]` ground set explicit, or add a companion bridge lemma for the
binomial expression after deleting the distinguished element.
-/
theorem hiltonMilner (n k : ℕ) (𝓕 : SetFamily)
    (hk : 0 < k) (hkn : 2 * k ≤ n)
    (hF : UniformFamily n k 𝓕)
    (hinter : PairwiseIntersecting 𝓕) (hempty : EmptyTotalIntersection 𝓕) :
    𝓕.card ≤ hiltonMilnerBound n k := by
  sorry

/--
Shifted-family uniqueness case used in source theorem `thm:StrictHM`, from the
discussion at lines 303--326.

Source proof: for shifted families, split the family as in the proof of
Hilton--Milner.  The strict shifted variant `mainTechnical_shiftedStrictTwoB`
rules out two or more exceptional sets, so equality forces exactly one
exceptional `k`-set `B`; maximality then fills in all `k`-sets containing the
center and intersecting `B`.

Prover notes: this is the precise shifted classification that the final
non-shifted theorem reduces to.  It should be proved before trying to use
`strongShiftedReduction`.
-/
theorem strictHiltonMilner_shifted (n k : ℕ) (𝓕 : SetFamily)
    (hk4 : 4 ≤ k) (hkn : 2 * k < n)
    (hF : UniformFamily n k 𝓕)
    (hinter : PairwiseIntersecting 𝓕) (hempty : EmptyTotalIntersection 𝓕)
    (hshift : ShiftedOn n 𝓕)
    (hmax : 𝓕.card = hiltonMilnerBound n k) :
    IsHiltonMilnerFamily n k 𝓕 := by
  sorry

/--
Non-deletion-empty bridge for source theorem `thm:StrictHM`.

Source/proof bridge: if the strengthened deletion-empty property fails, then
some member `F₀` and some element `i` have the property that every other member
contains `i`.  The empty-total-intersection hypothesis forces `i ∉ F₀`.  Since
the family is maximal, every `k`-set containing `i` and intersecting `F₀` must
already be present; otherwise it could be added without breaking pairwise
intersection or empty total intersection.  Thus the source HM form follows
directly, without applying the strengthened shifting lemma.

Prover notes: unfold `DeletionEmptyTotalIntersection` to obtain `F₀` and `i`;
use maximality against the canonical `hiltonMilnerFamily n k i F₀`.
-/
lemma strictHiltonMilner_nonDeletionEmptyCase (n k : ℕ) (𝓕 : SetFamily)
    (hk4 : 4 ≤ k) (hkn : 2 * k < n)
    (hF : UniformFamily n k 𝓕)
    (hinter : PairwiseIntersecting 𝓕) (hempty : EmptyTotalIntersection 𝓕)
    (hmax : 𝓕.card = hiltonMilnerBound n k)
    (hnotDelete : ¬ DeletionEmptyTotalIntersection 𝓕) :
    IsHiltonMilnerFamily n k 𝓕 := by
  sorry

/--
Deletion-empty bridge for source theorem `thm:StrictHM`.

Source/proof bridge: under `DeletionEmptyTotalIntersection`, use
`strongShiftedReduction` to reach a shifted family with no smaller cardinality.
The Hilton--Milner upper bound and maximality force every size comparison in
the reduction to be an equality.  Apply `strictHiltonMilner_shifted` to the
shifted witness, then inspect the equality cases in the reduction: ordinary
shifts must preserve the extremal HM structure, and any standard-family
replacement can occur at equality only when the original family already has the
same HM form.  This reflection step is the missing bridge between the existential
shifted reduction and the final equality for the original family.

Prover notes: do not use `strongShiftedReduction` as a black box only.  The proof
must carry equality through its shift/replacement construction, using the source
standard-family comparison when a replacement occurs.
-/
lemma strictHiltonMilner_deletionEmptyReduction (n k : ℕ) (𝓕 : SetFamily)
    (hk4 : 4 ≤ k) (hkn : 2 * k < n)
    (hF : UniformFamily n k 𝓕)
    (hinter : PairwiseIntersecting 𝓕) (hempty : EmptyTotalIntersection 𝓕)
    (hdelete : DeletionEmptyTotalIntersection 𝓕)
    (hmax : 𝓕.card = hiltonMilnerBound n k) :
    IsHiltonMilnerFamily n k 𝓕 := by
  sorry

/--
Source theorem `thm:StrictHM`, lines 295--301; proof discussion lines 303--326.

Source proof: first prove the shifted classification using the strict shifted
variant of `thm:MainTechnical`.  For a non-shifted family, split on the stronger
deletion-empty property from the final source lemma.  If it fails, all but one
set contain a common center, and maximality directly gives the HM family.  If it
holds, use the strengthened shifting reduction, but carry equality through the
reduction so that the HM form of the shifted extremal witness reflects back to
the original family.

Prover notes: prove `strictHiltonMilner_shifted`, then the two bridge lemmas
`strictHiltonMilner_nonDeletionEmptyCase` and
`strictHiltonMilner_deletionEmptyReduction`; the latter is the explicit bridge
showing that `strongShiftedReduction` is sufficient for uniqueness, not merely
for obtaining some shifted family of no smaller cardinality.
-/
theorem strictHiltonMilner (n k : ℕ) (𝓕 : SetFamily)
    (hk4 : 4 ≤ k) (hkn : 2 * k < n)
    (hF : UniformFamily n k 𝓕)
    (hinter : PairwiseIntersecting 𝓕) (hempty : EmptyTotalIntersection 𝓕)
    (hmax : 𝓕.card = hiltonMilnerBound n k) :
    ∃ (B : Finset ℕ) (i : ℕ),
      B ∈ kSubsets n k ∧ i ∈ ground n ∧ i ∉ B ∧
        𝓕 = hiltonMilnerFamily n k i B := by
  classical
  by_cases hdelete : DeletionEmptyTotalIntersection 𝓕
  · exact strictHiltonMilner_deletionEmptyReduction n k 𝓕 hk4 hkn hF hinter hempty hdelete hmax
  · exact strictHiltonMilner_nonDeletionEmptyCase n k 𝓕 hk4 hkn hF hinter hempty hmax hdelete

end AShortProofOfTheHiltonMilnerTheorem
