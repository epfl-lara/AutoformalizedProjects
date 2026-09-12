import Mathlib

/-!
Shared definitions for the source-backed Hilton--Milner formalization.
-/

namespace AShortProofOfTheHiltonMilnerTheorem

/-- A finite set system, represented as a finite family of finite subsets of `ℕ`. -/
@[reducible] def SetFamily : Type := Finset (Finset ℕ)

/-- The source ground set `[n] = {1, ..., n}`. -/
def ground (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 n

/-- All `k`-element subsets of the source ground set `[n]`. -/
def kSubsets (n k : ℕ) : SetFamily :=
  (ground n).powersetCard k

/-- A finite family all of whose members are subsets of `[n]`. -/
def FamilyOn (n : ℕ) (𝓕 : SetFamily) : Prop :=
  ∀ ⦃F : Finset ℕ⦄, F ∈ 𝓕 → F ⊆ ground n

/-- A finite family of `k`-element subsets of `[n]`. -/
def UniformFamily (n k : ℕ) (𝓕 : SetFamily) : Prop :=
  ∀ ⦃F : Finset ℕ⦄, F ∈ 𝓕 → F.card = k ∧ F ⊆ ground n

/-- Pairwise-intersecting finite set family. -/
def PairwiseIntersecting (𝓕 : SetFamily) : Prop :=
  ∀ ⦃F G : Finset ℕ⦄, F ∈ 𝓕 → G ∈ 𝓕 → F ≠ G → (F ∩ G).Nonempty

/-- Cross-intersecting finite set families. -/
def CrossIntersecting (𝓐 𝓑 : SetFamily) : Prop :=
  ∀ ⦃A B : Finset ℕ⦄, A ∈ 𝓐 → B ∈ 𝓑 → (A ∩ B).Nonempty

/-- The total intersection of the family is empty. -/
def EmptyTotalIntersection (𝓕 : SetFamily) : Prop :=
  ∀ x : ℕ, ∃ F : Finset ℕ, F ∈ 𝓕 ∧ x ∉ F

/-- After deleting any one member, the remaining family has empty total intersection. -/
def DeletionEmptyTotalIntersection (𝓕 : SetFamily) : Prop :=
  ∀ ⦃F₀ : Finset ℕ⦄, F₀ ∈ 𝓕 → ∀ x : ℕ,
    ∃ F : Finset ℕ, F ∈ 𝓕 ∧ F ≠ F₀ ∧ x ∉ F

/-- Replace `j` by `i` in a set when `j ∈ F` and `i ∉ F`. -/
def shiftedSet (i j : ℕ) (F : Finset ℕ) : Finset ℕ :=
  if j ∈ F ∧ i ∉ F then insert i (F.erase j) else F

/-- The source combinatorial shifting operation `Shift_{i ← j}` on a set family. -/
def shiftOperation (i j : ℕ) (𝓕 : SetFamily) : SetFamily :=
  (𝓕.filter (fun F : Finset ℕ => j ∉ F ∨ i ∈ F ∨ shiftedSet i j F ∈ 𝓕)) ∪
    ((𝓕.filter (fun F : Finset ℕ => j ∈ F ∧ i ∉ F)).image (shiftedSet i j))

/-- Shiftedness over the ground set `[n]`. -/
def ShiftedOn (n : ℕ) (𝓕 : SetFamily) : Prop :=
  ∀ ⦃i j : ℕ⦄ ⦃F : Finset ℕ⦄,
    i ∈ ground n → j ∈ ground n → i < j → F ∈ 𝓕 → j ∈ F → i ∉ F →
      shiftedSet i j F ∈ 𝓕

/-- The numerical upper bound in the main technical theorem. -/
def mainTechnicalBound (n k : ℕ) : ℕ :=
  Nat.choose n (k - 1) - Nat.choose (n - k) (k - 1) + 1

/-- The numerical upper bound in the Hilton--Milner theorem. -/
def hiltonMilnerBound (n k : ℕ) : ℕ :=
  Nat.choose (n - 1) (k - 1) - Nat.choose (n - 1 - k) (k - 1) + 1

/--
The extremal Hilton--Milner family from the source uniqueness theorem: a single
`k`-set `B`, together with all `k`-sets in `[n]` that contain `i` and intersect
`B`.
-/
def hiltonMilnerFamily (n k i : ℕ) (B : Finset ℕ) : SetFamily :=
  insert B ((kSubsets n k).filter (fun F : Finset ℕ => i ∈ F ∧ (F ∩ B).Nonempty))

/-- The exact structural conclusion of the Hilton--Milner uniqueness theorem. -/
def IsHiltonMilnerFamily (n k : ℕ) (𝓕 : SetFamily) : Prop :=
  ∃ (B : Finset ℕ) (i : ℕ),
    B ∈ kSubsets n k ∧ i ∈ ground n ∧ i ∉ B ∧
      𝓕 = hiltonMilnerFamily n k i B

end AShortProofOfTheHiltonMilnerTheorem
