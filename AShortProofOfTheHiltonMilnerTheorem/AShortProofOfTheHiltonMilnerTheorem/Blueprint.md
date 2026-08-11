# Formalization Blueprint: docs/source/A_short_proof_of_the_Hilton-Milner_theorem.tex

- Source: `docs/source/A_short_proof_of_the_Hilton-Milner_theorem.tex`
- Nearby PDF checked: `docs/bulavka_woodroofe2024_hilton_milner.pdf`
- Target Lean entry file: `AShortProofOfTheHiltonMilnerTheorem/Main.lean`
- Status: statement/source review approved; strict Hilton--Milner bridge corrections added for proof handoff.  Lean proofs remain as `sorry` skeletons for a user-started prove workflow.

## Planner Checklist

- [x] Identify definitions and notation that must exist before theorem statements.
- [x] Split large source theorems into Lean-sized lemmas.
- [x] Record source labels/pages/equations for every generated declaration.
- [x] Check local project and Mathlib names before introducing duplicates.
- [x] Verify drafted Lean statements match the source document.
- [x] Run independent statement/source verification review and apply corrections.
- [x] Attach the complete source proof text when available, or explicitly record why it is unavailable.
- [x] Record a natural-language proof strategy or source proof pointer for each theorem/lemma.
- [x] Resolve all construction stubs before proof handoff.
- [x] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow. (Checked after independent review stamped every source entry.)

## Import Plan

Direct Lean imports expected in generated Lean files only:
- `Mathlib`

Root coverage:
- `AShortProofOfTheHiltonMilnerTheorem.lean` imports `AShortProofOfTheHiltonMilnerTheorem.Main`.

## Suggested Search Modules

Non-gating modules or namespaces to search while proving. Do not force these into `.lean` imports unless the prover actually needs them.
- `Mathlib.Combinatorics.SetFamily.Shadow` for `Finset.shadow`, `Finset.mem_shadow_iff`, and shadow monotonicity.
- `Mathlib.Combinatorics.SetFamily.Intersecting` for Mathlib's `Set.Intersecting` reference definition.
- `Mathlib.Data.Finset.Powerset` for `Finset.powersetCard` and cardinality of fixed-size subsets.
- `Mathlib.Data.Nat.Choose.Basic` and nearby binomial lemmas for Pascal identities.
- `Mathlib.Data.Finset.Interval` for `Finset.Icc` facts about the ground set `[n]`.

Search notes from the planner refresh:
- `Finset.powersetCard`, `Finset.mem_powersetCard`, and `Finset.card_powersetCard` are the Mathlib fixed-cardinality subset interface.
- `Finset.shadow`, `Finset.mem_shadow_iff`, `Finset.shadow_mono`, and `Finset.shadow_monotone` are the Mathlib shadow interface matching the source shadow under uniformity.
- `Nat.choose_succ_succ`, `Nat.choose_succ_left`, and `Nat.choose_succ_right` are the likely Pascal/binomial recurrence lemmas.

## Generated File Layout

- Aggregator entry file: `AShortProofOfTheHiltonMilnerTheorem/Main.lean`
- `AShortProofOfTheHiltonMilnerTheorem/Basic.lean`: finite-family, uniformity, intersection, shifting, and extremal-family definitions.
- `AShortProofOfTheHiltonMilnerTheorem/MainTechnical.lean`: the main technical inequality and shifted/strict variants.
- `AShortProofOfTheHiltonMilnerTheorem/Shifting.lean`: Frankl--Furedi and strengthened shifting reductions.
- `AShortProofOfTheHiltonMilnerTheorem/HiltonMilner.lean`: the HM bound, uniqueness statement, and equality-case bridge lemmas.

## Lean Representation Plan

The source works with finite set systems of subsets of `[n] = {1, ..., n}`. The Lean draft uses finite set families directly:

- `SetFamily := Finset (Finset ℕ)` represents a finite family of finite sets of natural numbers.
- `ground n := Finset.Icc 1 n` represents `[n]`.
- `kSubsets n k := (ground n).powersetCard k` represents all `k`-element subsets of `[n]`.
- `FamilyOn n 𝓕` and `UniformFamily n k 𝓕` record that every member of `𝓕` lies in `[n]` and has cardinality `k`.
- `PairwiseIntersecting 𝓕` says distinct members of `𝓕` have nonempty intersection.
- `CrossIntersecting 𝓐 𝓑` says every `A ∈ 𝓐` intersects every `B ∈ 𝓑`.
- `EmptyTotalIntersection 𝓕` says no natural number is contained in all members of `𝓕`.
- `DeletionEmptyTotalIntersection 𝓕` formalizes the strengthened property in the final lemma: after deleting any fixed `F₀`, the remaining family has empty total intersection.
- `shiftedSet`, `shiftOperation`, and `ShiftedOn n 𝓕` formalize the shifting definition from lines 138-146.
- `Finset.shadow 𝓑` is Mathlib's one-element-deletion shadow. Under `UniformFamily n k 𝓑`, this matches the source shadow of all `(k-1)`-subsets of members of `𝓑`.
- `mainTechnicalBound n k` and `hiltonMilnerBound n k` name the two binomial upper bounds.
- `hiltonMilnerFamily n k i B` represents the extremal family consisting of `B` and all `k`-sets in `[n]` that contain `i` and intersect `B`.
- `IsHiltonMilnerFamily n k 𝓕` names the exact existential conclusion of the uniqueness theorem, so bridge lemmas can pass the HM structure around without duplicating the long existential.

Representation bridge notes:
- The source's inequalities `2k - 1 ≤ n`, `k ≤ n/2`, and `k < n/2` are encoded over naturals as `2 * k ≤ n + 1`, `2 * k ≤ n`, and `2 * k < n` respectively.
- The draft adds `0 < k` where the source uses `(k-1)`-element families but leaves positivity implicit. This is a domain clarification for natural-number indexing, not intended as a mathematical weakening for the paper's positive-uniformity setting.

## Source Statement Inventory

### thm:HM

- Kind: theorem
- Source locator: `docs/source/A_short_proof_of_the_Hilton-Milner_theorem.tex:91-95`; proof at lines 198-223 after Lemma `lem:Frankl-Furedi` is introduced.
- Planned Lean declarations: `hiltonMilner`; supporting definitions `SetFamily`, `ground`, `UniformFamily`, `PairwiseIntersecting`, `EmptyTotalIntersection`, `hiltonMilnerBound`.
- Dependencies: `franklFurediShifted`, `mainTechnical`, shifting definitions, shadow containment for the HM split families.
- Formal statement review: Lean states the cardinal upper bound for any finite family of `k`-element subsets of `[n]` that is pairwise intersecting and has empty total intersection. The source condition `k ≤ n/2` is encoded as `2 * k ≤ n`; the conclusion is `𝓕.card ≤ hiltonMilnerBound n k`.
- Source qualifiers: mathematical object class is a finite family of `k`-element subsets of `[n]`; quantifiers are over natural parameters `n k` and a family `𝓕`; parameter domain includes `k ≤ n/2` and implicit positive `k`; side conditions are pairwise intersection and empty total intersection; output is an upper bound on `|𝓕|` by the stated binomial expression.
- Lean coverage: `UniformFamily n k 𝓕` covers `k`-element subsets of `[n]`; `PairwiseIntersecting 𝓕` covers pairwise-intersecting; `EmptyTotalIntersection 𝓕` covers `⋂_{F∈𝓕} F = ∅`; `2 * k ≤ n` covers `k ≤ n/2`; `hiltonMilnerBound` is exactly `{n-1 choose k-1} - {n-1-k choose k-1} + 1` using `Nat.choose`.
- Scope changes: finite-family representation by `Finset`; explicit `0 < k`; natural-arithmetic encoding of `k ≤ n/2` as `2 * k ≤ n`.
- Statement verification status: approved by codex verifier
- Complete source proof: Given the lemma, the proof of Theorem~\ref{thm:HM} is nearly immediate. Let $\mathcal{F}$ be a shifted family satisfying the conditions of the theorem. Define $\mathcal{A}=\{F\setminus1 : F\in\mathcal{F}\text{ with }1\in\mathcal{F}\}$ and $\mathcal{B}=\{F : F\in\mathcal{F}\text{ with }1\notin\mathcal{F}\}$. Since $\mathcal{F}$ is shifted, if $F\in\mathcal{F}$ does not have $1$, then $(F\setminus i)\cup1\in\mathcal{F}$ for each $i\in F$. It follows that $\partial\mathcal{B}\subseteq\mathcal{A}$. Since $\mathcal{F}$ is intersecting, also $\mathcal{A},\mathcal{B}$ are cross-intersecting systems of subsets of $\{2,\dots,n\}$. Since $\mathcal{F}$ has empty intersection, both of $\mathcal{A},\mathcal{B}$ are nonempty. The desired bound is now immediate from Theorem~\ref{thm:MainTechnical}.
- Source proof / prover notes: First use `franklFurediShifted` to reduce to shifted `𝓕`. Split members according to whether they contain `1`, deleting `1` from the containing part to define `𝓐`, and keeping the non-containing part as `𝓑` on the remaining ground set. Prove shadow containment from shiftedness, cross-intersection from pairwise intersection, and nonemptiness from empty total intersection. Apply `mainTechnical` with the ground set reindexed from `{2, ..., n}` to `[n-1]`; the binomial expression then matches `hiltonMilnerBound`.

### thm:MainTechnical

- Kind: theorem
- Source locator: `docs/source/A_short_proof_of_the_Hilton-Milner_theorem.tex:106-115`; proof at lines 155-196.
- Planned Lean declarations: `mainTechnical`; supporting definitions `UniformFamily`, `CrossIntersecting`, `mainTechnicalBound`.
- External Mathlib reference in the statement: Finset shadow for the source shadow operator.
- Dependencies: shifting preservation facts, induction on `n`, fixed-size subset counting, binomial/Pascal identities, complement argument in the base case.
- Formal statement review: Lean states the source inequality for finite families `𝓐` of `(k-1)`-sets and `𝓑` of `k`-sets in `[n]`, with cross-intersection, nonempty `𝓑`, and `Finset.shadow 𝓑 ⊆ 𝓐`.
- Source qualifiers: object classes are two uniform finite set families over `[n]`; quantifier order is `n`, `k`, `𝓐`, `𝓑`; parameter domain is `2k-1 ≤ n` and implicit `0 < k`; side conditions are cross-intersection, nonempty `𝓑`, and shadow containment; output is the cardinal inequality with binomial bound `{n choose k-1} - {n-k choose k-1} + 1`.
- Lean coverage: `hkn : 2 * k ≤ n + 1` encodes `2k-1 ≤ n`; `UniformFamily n (k - 1) 𝓐` and `UniformFamily n k 𝓑` cover the uniform families; `CrossIntersecting 𝓐 𝓑` covers cross-intersection; `𝓑.Nonempty` covers nonempty `𝓑`; `Finset.shadow 𝓑 ⊆ 𝓐` covers `∂𝓑 ⊆ 𝓐`; `mainTechnicalBound` covers the exact numeric bound.
- Scope changes: finite-family representation by `Finset`; explicit `0 < k`; natural-arithmetic encoding `2 * k ≤ n + 1`; Mathlib one-step shadow used with the uniformity bridge noted above.
- Statement verification status: approved by codex verifier
- Complete source proof: We carry out a straightforward induction on $n$. If $n=2k-1$, then the upper bound is ${n \choose k-1}$, and the result follows by noticing that if a $(k-1)$-element set is in $\mathcal{A}$, then its complement cannot be in $\mathcal{B}$ (and vice-versa). For the inductive step, we may assume that $\mathcal{A}$ and $\mathcal{B}$ are shifted; otherwise, shift. Let $\mathcal{A}(\neg n),\mathcal{B}(\neg n)$ consist of the subsets in $\mathcal{A},\mathcal{B}$ that do not contain $n$. It is immediate that these are shifted, cross-intersecting, and satisfy the shadow condition. Let $\mathcal{A}(n),\mathcal{B}(n)$ be obtained by taking subsets that contain $n$, then deleting $n$. These are also shifted, cross-intersecting, and satisfy the shadow condition. As $\mathcal{A}$ and $\mathcal{B}$ are shifted, $\mathcal{A}(\neg n)$ and $\mathcal{B}(\neg n)$ are nonempty, so induction gives equation (1): $|\mathcal{A}(\neg n)|+|\mathcal{B}(\neg n)|\leq {n-1\choose k-1}-{n-1-k\choose k-1}+1$. For $\mathcal{A}(n),\mathcal{B}(n)$: if $\mathcal{A}(n)$ is empty then the shadow condition makes $\mathcal{B}(n)$ empty; if $\mathcal{B}(n)$ is empty, shiftedness and nonempty $\mathcal{B}$ give $\{1,\dots,k\}\in\mathcal{B}$, so every set in $\mathcal{A}(n)$ intersects it and $|\mathcal{A}(n)|\leq {n-1\choose k-2}-{n-1-k\choose k-2}$; if $\mathcal{B}(n)$ is nonempty, induction gives equation (2), $|\mathcal{A}(n)|+|\mathcal{B}(n)|\leq {n-1\choose k-2}-{n-1-k\choose k-2}$. Combine with Pascal's identity.
- Source proof / prover notes: Formal proof should introduce no-containing and containing/deleted subfamilies, prove they partition both families by membership of `n`, apply induction to the not-`n` part and either induction or direct counting to the `n` part, then finish with `Nat.choose` Pascal identities. Search `Finset.card_powersetCard`, `Finset.mem_shadow_iff`, and `Nat.choose` recurrence lemmas.

### lem:Frankl-Furedi

- Kind: lemma
- Source locator: `docs/source/A_short_proof_of_the_Hilton-Milner_theorem.tex:201-206`; proof at lines 230-255.
- Planned Lean declarations: `franklFurediShifted`; supporting definitions `ShiftedOn`, `shiftOperation`, `UniformFamily`, `PairwiseIntersecting`, `EmptyTotalIntersection`.
- Dependencies: combinatorial shifting operation, preservation of pairwise intersection and cardinality under shifts, termination of repeated shifts, and the fallback argument using the boundary of `{1, ..., k+1}`.
- Formal statement review: Lean states existence of a shifted family `𝓕'` on the same ground set with the same uniformity, pairwise-intersection, and empty-total-intersection properties, and with `𝓕.card ≤ 𝓕'.card`.
- Source qualifiers: object class is a pairwise-intersecting family of `k`-element subsets of `[n]`; side condition is empty total intersection; output codomain is an existential shifted family satisfying the same properties and cardinality at least the original.
- Lean coverage: `UniformFamily n k 𝓕`, `PairwiseIntersecting 𝓕`, `EmptyTotalIntersection 𝓕`; existential witness `𝓕' : SetFamily` with `ShiftedOn n 𝓕'`, same properties, and `𝓕.card ≤ 𝓕'.card`.
- Scope changes: finite-family representation by `Finset`; explicit `0 < k`; shiftedness is restricted to `i,j ∈ ground n`, matching shifts over `[n]`.
- Statement verification status: approved by codex verifier
- Complete source proof: Given $\mathcal{F}$ as in Theorem~\ref{thm:HM}, apply shifting operations $\operatorname{Shift}_{i\leftarrow j}$. Each such operation preserves the pairwise-intersecting property and cardinality, but may or may not result in a system with a common element of intersection. If a sequence of shifting operations ends in a shifted system with empty intersection, then we are done. Otherwise, some shift results in a system where every set contains $i_0$. Before this step every set contains either $i_0$ or $j_0$. Relabel to `1` and `2`, continue shifting over all `3 ≤ i < j`. Then `{1,3,...,k+1}` and `{2,3,...,k+1}` are in the system. Since every set contains `1` or `2`, add all `k`-element subsets containing `{1,2}` if needed. Thus the boundary of `{1,...,k+1}` is contained in the system; it has empty intersection and is preserved by further shifts, so shifting to stability gives the result.
- Source proof / prover notes: This is the deepest shifting reduction. The proof likely needs separate lemmas for shift preservation, a finite termination measure for repeated shifts, relabeling invariance, and the boundary subfamily witness for empty intersection. Do not try to prove it by pure simplification.

### line-224

- Kind: remark formalized as a theorem-shaped special case
- Source locator: `docs/source/A_short_proof_of_the_Hilton-Milner_theorem.tex:224-227`
- Planned Lean declarations: `mainTechnical_shiftedSpecialCase`.
- Dependencies: same as `mainTechnical`, plus `ShiftedOn n 𝓐` and `ShiftedOn n 𝓑` hypotheses.
- Formal statement review: The source remark is meta-mathematical: the HM proof needs only the shifted case of Theorem 2. The Lean declaration records the mathematical shifted special case by adding shiftedness hypotheses to `mainTechnical` and retaining the same conclusion.
- Source qualifiers: follow-on claim about the preceding proof's dependency on a shifted-special-case theorem.
- Lean coverage: `mainTechnical_shiftedSpecialCase` covers the shifted-special-case theorem. It does not formalize proof-dependency minimality itself.
- Scope changes: partial coverage of a prose remark; converted to a theorem statement rather than a meta-theorem about the proof script.
- Statement verification status: approved by codex verifier
- Complete source proof: no separate proof text; the remark says, "This proof requires only the special case of Theorem~\ref{thm:MainTechnical} where the set systems are shifted."
- Source proof / prover notes: Once `mainTechnical` is proved this special case follows immediately, but in the source it is intended as a possible independent target for the HM proof.

### proof-discussion-strict-main-technical

- Kind: theorem helper extracted from proof discussion.
- Source locator: `docs/source/A_short_proof_of_the_Hilton-Milner_theorem.tex:303-326` in the uniqueness section.
- Planned Lean declarations: `mainTechnical_shiftedStrictTwoB`.
- Dependencies: shifted version of `mainTechnical`, induction split used in `thm:MainTechnical`, the strict `|𝓑| ≥ 2` case analysis, and binomial inequalities around equation `(2)`.
- Formal statement review: Lean records the shifted strict variant explicitly: for shifted cross-intersecting families satisfying the shadow condition, if `4 ≤ k`, `2k - 1 ≤ n`, and `𝓑` has at least two members, then the same upper bound from `mainTechnical` is not attained.
- Source qualifiers: object classes are the same two uniform shifted finite set families as in the shifted special case of Theorem 2; parameter domain includes `k ≥ 4`, `2k - 1 ≤ n`, and `|𝓑| ≥ 2`; side conditions are cross-intersection, shadow containment, and shiftedness; output is the strict inequality `|𝓐| + |𝓑| < {n \choose k-1} - {n-k \choose k-1} + 1`.
- Lean coverage: `hk4 : 4 ≤ k`; `hkn : 2 * k ≤ n + 1`; `UniformFamily n (k - 1) 𝓐` and `UniformFamily n k 𝓑`; `CrossIntersecting 𝓐 𝓑`; `hcardB : 2 ≤ 𝓑.card`; `Finset.shadow 𝓑 ⊆ 𝓐`; `ShiftedOn n 𝓐`; `ShiftedOn n 𝓑`; conclusion `𝓐.card + 𝓑.card < mainTechnicalBound n k`.
- Scope changes: finite-family representation by `Finset`; natural-arithmetic encoding `2 * k ≤ n + 1`; this helper covers only the shifted proof-discussion variant, not a separate non-shifted theorem.
- Statement verification status: approved by codex verifier
- Complete source proof: The proof for a shifted family requires a straightforward modification of Theorem~\ref{thm:MainTechnical}. Require `k ≥ 4` and strengthen nonempty `\mathcal{B}` to `|\mathcal{B}| ≥ 2`; with this strengthened hypothesis, the inequality is strict. In the induction step, `\mathcal{B}(n)` is empty or nonempty. If empty, then because `\mathcal{B}` has at least two elements, `\mathcal{A}(n)` is strictly smaller than the displayed bound. If nonempty, the bound in equation `(2)` is already strict when `k ≥ 4`. Hence each induction step yields a strict inequality.
- Source proof / prover notes: Reuse the split-family proof of `mainTechnical`, but strengthen the estimates for the containing-`n` part. In the empty `𝓑(n)` case use `2 ≤ 𝓑.card` to avoid equality; in the nonempty case use the strictness of the final binomial comparison for `k ≥ 4`.

### thm:StrictHM

- Kind: theorem
- Source locator: `docs/source/A_short_proof_of_the_Hilton-Milner_theorem.tex:295-301`; proof discussion at lines 303-326 and dependent lemma at lines 328-363.
- Planned Lean declarations: `strictHiltonMilner`; supporting definitions `hiltonMilnerFamily` and `IsHiltonMilnerFamily`; supporting lemmas `mainTechnical_shiftedStrictTwoB`, `strictHiltonMilner_shifted`, `strictHiltonMilner_nonDeletionEmptyCase`, `strictHiltonMilner_deletionEmptyReduction`, and `strongShiftedReduction`.
- Dependencies: `hiltonMilner`, shifted strict variant `mainTechnical_shiftedStrictTwoB`, shifted classification `strictHiltonMilner_shifted`, the non-deletion-empty maximality bridge, the deletion-empty reflection bridge using `strongShiftedReduction`, and the extremal-family construction.
- Formal statement review: Lean states that if the HM hypotheses hold, `4 ≤ k`, `2 * k < n`, and the HM upper bound is achieved, then `𝓕` equals `hiltonMilnerFamily n k i B` for some `B ∈ kSubsets n k` and `i ∈ ground n` with `i ∉ B`.
- Source qualifiers: object class and hypotheses are those of `thm:HM`; additional parameter domain `4 ≤ k < n/2`; equality/image condition is attaining the upper bound; output is existence of a `k`-set `B` and element `i ∉ B` such that the family consists exactly of `B` plus all `k`-sets containing `i` and intersecting `B`.
- Lean coverage: HM hypotheses are repeated as `UniformFamily`, `PairwiseIntersecting`, and `EmptyTotalIntersection`; `hmax : 𝓕.card = hiltonMilnerBound n k` covers attaining the upper bound; `hiltonMilnerFamily` and `IsHiltonMilnerFamily` cover the exact family description; `B ∈ kSubsets n k`, `i ∈ ground n`, and `i ∉ B` cover the existential qualifiers.
- Scope changes: finite-family representation by `Finset`; strict `k < n/2` encoded as `2 * k < n`; Lean explicitly asserts `i ∈ [n]` and `B ⊆ [n]`, which are implicit in the source family description.
- Statement verification status: approved by codex verifier
- Complete source proof: The source requires `k ≥ 4` to avoid technicalities and reduce to shifted families. For shifted families, modify Theorem~\ref{thm:MainTechnical} by strengthening nonempty `\mathcal{B}` to `|\mathcal{B}| ≥ 2`; with this strengthened hypothesis the inequality is strict. If `\mathcal{B}(n)` is empty, `|\mathcal{B}| ≥ 2` makes `\mathcal{A}(n)` strictly smaller than the bound. If `\mathcal{B}(n)` is nonempty, the bound in equation (2) is already strict when `k ≥ 4`. Thus the induction step yields a strict inequality. Theorem~\ref{thm:StrictHM} follows for shifted families by applying this variant to the same split families as in the HM proof. For non-shifted families, split on `DeletionEmptyTotalIntersection`. If it fails, some `F₀` and center `i` make every other set contain `i`; empty total intersection gives `i ∉ F₀`, and maximality fills exactly the HM family. If it holds, apply the strengthened shifting lemma, use the HM upper bound and maximality to force equality throughout the reduction, classify the shifted witness, and reflect the equality case back through the shifts or standard-family replacement.
- Source proof / prover notes: Use `mainTechnical_shiftedStrictTwoB` to prove the shifted classification `strictHiltonMilner_shifted`. Then prove `strictHiltonMilner_nonDeletionEmptyCase` for the failure of the deletion-empty property. In the deletion-empty case, `strictHiltonMilner_deletionEmptyReduction` must not treat `strongShiftedReduction` as a mere black box: it must carry equality through the reduction and show that the shifted witness having HM form implies the original family already has HM form.
- Proof bridge helper declarations:
  - `strictHiltonMilner_shifted`: shifted equality case from the strict variant of the main technical theorem.
  - `strictHiltonMilner_nonDeletionEmptyCase`: handles the case where deleting one member leaves a common center in all remaining sets.
  - `strictHiltonMilner_deletionEmptyReduction`: uses `strongShiftedReduction` plus equality-case reflection to transfer the shifted HM structure back to the original family.

### line-328

- Kind: lemma
- Source locator: `docs/source/A_short_proof_of_the_Hilton-Milner_theorem.tex:328-334`; proof at lines 336-363.
- Planned Lean declarations: `strongShiftedReduction`; supporting definition `DeletionEmptyTotalIntersection`.
- Dependencies: shifting operation, strengthened no-common-intersection-after-deletion invariant, standard family comparison, preservation of boundary subfamilies under shifts.
- Formal statement review: Lean states the strengthened shifting reduction: from a pairwise-intersecting uniform family on `[n]` satisfying the deletion-empty-total-intersection property, there exists a shifted family with the same properties and no smaller cardinality.
- Source qualifiers: object class is a pairwise-intersecting family of `k`-element subsets of `[n]`; additional property is that for every `F₀ ∈ 𝓕`, the intersection over `𝓕 \ {F₀}` is empty; output is a shifted family satisfying the same properties and with cardinality at least the original.
- Lean coverage: `UniformFamily n k 𝓕`, `PairwiseIntersecting 𝓕`, and `DeletionEmptyTotalIntersection 𝓕`; existential witness with `ShiftedOn n`, same properties, and `𝓕.card ≤ 𝓕'.card`.
- Scope changes: finite-family representation by `Finset`; explicit `0 < k`; deletion of a member is represented by requiring, for each natural `x`, a witness `F ∈ 𝓕` with `F ≠ F₀` and `x ∉ F`.
- Statement verification status: approved by codex verifier
- Complete source proof: By the standard family, mean the shifted family with $A=\{2,\dots,k+1\}$, $A'=\{2,\dots,k,k+2\}$, and all `k`-element sets that both contain `1` and intersect `A` and `A'`. It is obvious that the standard family is at least as large as any family where all but two sets contain `1`. Given `𝓕`, perform shifts. If these terminate in a shifted family with the desired properties, we are done. Otherwise, a shift destroys the additional property; stop just before and relabel to get a family containing sets with `1` not `2`, with `2` not `1`, with both `1` and `2`, and possibly `B={3,...,k+2}`. Assume all sets containing both `1,2` and intersecting `B` are present. Since these sets have no common intersection other than `1,2`, shifts over all `3≤i<j` preserve the additional property. After those shifts, if only one set has `1` not `2` or only one set has `2` not `1`, replace by the standard family. Otherwise the family contains `{a,3,...,k+1}` and `{a,3,...,k,k+2}` for `a=1,2`, plus all sets containing `{1,2}` and intersecting `B`. Hence it contains both boundaries `∂{1,...,k+1}` and `∂{1,...,k,k+2}`. Both have empty intersection and are preserved by all shifts, so shift until stable.
- Source proof / prover notes: Expect to need helper lemmas for the standard family, the two boundary subfamilies, and preservation of the deletion-empty invariant under restricted shifts. This lemma is separate from the original Frankl-Furedi lemma and should not be silently replaced by it. For uniqueness, the bare existential shifted witness is not enough; use `strictHiltonMilner_deletionEmptyReduction` to carry equality and HM structure back to the original family.
