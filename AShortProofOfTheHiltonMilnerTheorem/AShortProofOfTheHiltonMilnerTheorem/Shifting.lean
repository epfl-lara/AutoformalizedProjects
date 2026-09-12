import AShortProofOfTheHiltonMilnerTheorem.Basic

/-!
Shifting reductions used by the Hilton--Milner upper bound and uniqueness proof.
-/

namespace AShortProofOfTheHiltonMilnerTheorem

private lemma franklFurediShifted_of_shifted (n k : ℕ) (𝓕 : SetFamily)
    (hF : UniformFamily n k 𝓕)
    (hinter : PairwiseIntersecting 𝓕) (hempty : EmptyTotalIntersection 𝓕)
    (hshift : ShiftedOn n 𝓕) :
    ∃ 𝓕' : SetFamily,
      UniformFamily n k 𝓕' ∧ PairwiseIntersecting 𝓕' ∧
      EmptyTotalIntersection 𝓕' ∧ ShiftedOn n 𝓕' ∧ 𝓕.card ≤ 𝓕'.card := by
  exact ⟨𝓕, hF, hinter, hempty, hshift, le_rfl⟩

private lemma shiftedSet_card (i j : ℕ) (F : Finset ℕ) :
    (shiftedSet i j F).card = F.card := by
  unfold shiftedSet
  by_cases h : j ∈ F ∧ i ∉ F
  · rw [if_pos h]
    have hi_erase : i ∉ F.erase j := by
      simp [h.2]
    rw [Finset.card_insert_of_notMem hi_erase]
    exact Finset.card_erase_add_one h.1
  · rw [if_neg h]

private lemma shiftedSet_subset_ground (n i j : ℕ) {F : Finset ℕ}
    (hi : i ∈ ground n) (hF : F ⊆ ground n) :
    shiftedSet i j F ⊆ ground n := by
  unfold shiftedSet
  by_cases h : j ∈ F ∧ i ∉ F
  · rw [if_pos h]
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hi
    · exact hF (Finset.mem_of_mem_erase hx)
  · rw [if_neg h]
    exact hF

private lemma shiftOperation_uniform (n k i j : ℕ) (𝓕 : SetFamily)
    (hi : i ∈ ground n) (hF : UniformFamily n k 𝓕) :
    UniformFamily n k (shiftOperation i j 𝓕) := by
  intro G hG
  unfold shiftOperation at hG
  rw [Finset.mem_union] at hG
  rcases hG with hG | hG
  · rw [Finset.mem_filter] at hG
    exact hF hG.1
  · rw [Finset.mem_image] at hG
    rcases hG with ⟨F, hFmove, rfl⟩
    rw [Finset.mem_filter] at hFmove
    have horig := hF hFmove.1
    exact ⟨by rw [shiftedSet_card]; exact horig.1,
      shiftedSet_subset_ground n i j hi horig.2⟩

private lemma shiftedSet_mem_shiftOperation_of_movable (i j : ℕ) (𝓕 : SetFamily)
    {F : Finset ℕ} (hFmem : F ∈ 𝓕) (hjF : j ∈ F) (hiF : i ∉ F) :
    shiftedSet i j F ∈ shiftOperation i j 𝓕 := by
  unfold shiftOperation
  rw [Finset.mem_union]
  right
  rw [Finset.mem_image]
  refine ⟨F, ?_, rfl⟩
  rw [Finset.mem_filter]
  exact ⟨hFmem, hjF, hiF⟩

private lemma shiftedSet_eq_uvCompress (i j : ℕ) (F : Finset ℕ) :
    shiftedSet i j F = UV.compress ({i} : Finset ℕ) ({j} : Finset ℕ) F := by
  unfold shiftedSet UV.compress
  by_cases h : j ∈ F ∧ i ∉ F
  · rw [if_pos h]
    have hdis : Disjoint ({i} : Finset ℕ) F := by
      simp [h.2]
    have hle : ({j} : Finset ℕ) ≤ F := by
      intro x hx
      simp at hx
      simpa [hx] using h.1
    rw [if_pos ⟨hdis, hle⟩]
    ext x
    by_cases hxj : x = j
    · subst x
      have hij : i ≠ j := by
        intro hji
        exact h.2 (by simpa [hji] using h.1)
      simp [h.1, hij.symm]
    · by_cases hxi : x = i
      · subst x
        simp [hxj]
      · simp [hxj, hxi]
  · rw [if_neg h]
    have hnot : ¬(Disjoint ({i} : Finset ℕ) F ∧ ({j} : Finset ℕ) ≤ F) := by
      intro hc
      apply h
      constructor
      · exact hc.2 (by simp)
      · intro hi
        exact (Finset.disjoint_left.mp hc.1) (by simp) hi
    rw [if_neg hnot]

private lemma uvCompress_singleton_eq_self_of_not_movable {i j : ℕ} {F : Finset ℕ}
    (h : j ∉ F ∨ i ∈ F) :
    UV.compress ({i} : Finset ℕ) ({j} : Finset ℕ) F = F := by
  rw [← shiftedSet_eq_uvCompress]
  unfold shiftedSet
  rw [if_neg]
  intro hmov
  exact h.elim (fun hj => hj hmov.1) (fun hi => hmov.2 hi)

private lemma shiftOperation_eq_uvCompression (i j : ℕ) (𝓕 : SetFamily) :
    shiftOperation i j 𝓕 = UV.compression ({i} : Finset ℕ) ({j} : Finset ℕ) 𝓕 := by
  ext G
  simp only [shiftOperation, UV.compression, Finset.mem_union, Finset.mem_filter,
    Finset.mem_image, shiftedSet_eq_uvCompress]
  constructor
  · intro hG
    rcases hG with hstay | hmove
    · rcases hstay with ⟨hGmem, hstay⟩
      left
      refine ⟨hGmem, ?_⟩
      rcases hstay with hjnot | hiin | hcompmem
      · rw [uvCompress_singleton_eq_self_of_not_movable (Or.inl hjnot)]
        exact hGmem
      · rw [uvCompress_singleton_eq_self_of_not_movable (Or.inr hiin)]
        exact hGmem
      · exact hcompmem
    · rcases hmove with ⟨a, hmov, hcompaG⟩
      rcases hmov with ⟨ha, hja, hia⟩
      by_cases hGmem : G ∈ 𝓕
      · left
        refine ⟨hGmem, ?_⟩
        rw [← hcompaG, UV.compress_idem]
        simpa [hcompaG] using hGmem
      · right
        exact ⟨⟨a, ha, hcompaG⟩, hGmem⟩
  · intro hG
    rcases hG with hstay | hmove
    · rcases hstay with ⟨hGmem, hcompmem⟩
      left
      exact ⟨hGmem, Or.inr (Or.inr hcompmem)⟩
    · rcases hmove with ⟨hpre, hGnot⟩
      rcases hpre with ⟨a, ha, hcompaG⟩
      right
      have hja : j ∈ a := by
        by_contra hjnot
        have hself : UV.compress ({i} : Finset ℕ) ({j} : Finset ℕ) a = a :=
          uvCompress_singleton_eq_self_of_not_movable (Or.inl hjnot)
        have hGa : G = a := hcompaG.symm.trans hself
        exact hGnot (by simpa [hGa] using ha)
      have hia : i ∉ a := by
        by_contra hiin
        have hself : UV.compress ({i} : Finset ℕ) ({j} : Finset ℕ) a = a :=
          uvCompress_singleton_eq_self_of_not_movable (Or.inr hiin)
        have hGa : G = a := hcompaG.symm.trans hself
        exact hGnot (by simpa [hGa] using ha)
      exact ⟨a, ⟨ha, hja, hia⟩, hcompaG⟩

private lemma shiftOperation_card (i j : ℕ) (𝓕 : SetFamily) :
    (shiftOperation i j 𝓕).card = 𝓕.card := by
  rw [shiftOperation_eq_uvCompression]
  exact UV.card_compression ({i} : Finset ℕ) ({j} : Finset ℕ) 𝓕

private lemma shiftOperation_mem_cases (i j : ℕ) (𝓕 : SetFamily) {A : Finset ℕ}
    (hA : A ∈ shiftOperation i j 𝓕) :
    (A ∈ 𝓕 ∧ (j ∉ A ∨ i ∈ A ∨ shiftedSet i j A ∈ 𝓕)) ∨
      ∃ F : Finset ℕ, F ∈ 𝓕 ∧ j ∈ F ∧ i ∉ F ∧ shiftedSet i j F = A := by
  unfold shiftOperation at hA
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image] at hA
  rcases hA with hA | hA
  · exact Or.inl hA
  · rcases hA with ⟨F, hF, rfl⟩
    exact Or.inr ⟨F, hF.1, hF.2.1, hF.2.2, rfl⟩

private lemma mem_shiftedSet_inserted_of_movable {i j : ℕ} {F : Finset ℕ}
    (hjF : j ∈ F) (hiF : i ∉ F) :
    i ∈ shiftedSet i j F := by
  unfold shiftedSet
  rw [if_pos ⟨hjF, hiF⟩]
  simp

private lemma mem_shiftedSet_of_mem_ne_erased {i j x : ℕ} {F : Finset ℕ}
    (hxF : x ∈ F) (hxj : x ≠ j) :
    x ∈ shiftedSet i j F := by
  unfold shiftedSet
  by_cases h : j ∈ F ∧ i ∉ F
  · rw [if_pos h]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxj, hxF⟩))
  · rw [if_neg h]
    exact hxF

private lemma not_mem_shiftedSet_erased_of_movable {i j : ℕ} {F : Finset ℕ}
    (hij : i < j) (hjF : j ∈ F) (hiF : i ∉ F) :
    j ∉ shiftedSet i j F := by
  unfold shiftedSet
  rw [if_pos ⟨hjF, hiF⟩]
  have hji : j ≠ i := Nat.ne_of_gt hij
  simp [hji]

private lemma mem_of_mem_shiftedSet_ne_inserted_of_movable {i j x : ℕ} {F : Finset ℕ}
    (hjF : j ∈ F) (hiF : i ∉ F)
    (hx : x ∈ shiftedSet i j F) (hxi : x ≠ i) :
    x ∈ F := by
  unfold shiftedSet at hx
  rw [if_pos ⟨hjF, hiF⟩] at hx
  rcases Finset.mem_insert.mp hx with hxi' | hxerase
  · exact False.elim (hxi hxi')
  · exact (Finset.mem_erase.mp hxerase).2

private lemma shiftedSet_ne_self_of_movable {i j : ℕ} {F : Finset ℕ}
    (hjF : j ∈ F) (hiF : i ∉ F) :
    shiftedSet i j F ≠ F := by
  intro h
  have hi_shift : i ∈ shiftedSet i j F := mem_shiftedSet_inserted_of_movable hjF hiF
  have : i ∈ F := by simpa [h] using hi_shift
  exact hiF this

private lemma shiftedSet_inter_shiftedSet_nonempty_of_movable {i j : ℕ} {F G : Finset ℕ}
    (hjF : j ∈ F) (hiF : i ∉ F) (hjG : j ∈ G) (hiG : i ∉ G) :
    (shiftedSet i j F ∩ shiftedSet i j G).Nonempty := by
  refine ⟨i, ?_⟩
  exact Finset.mem_inter.mpr
    ⟨mem_shiftedSet_inserted_of_movable hjF hiF,
      mem_shiftedSet_inserted_of_movable hjG hiG⟩

private lemma kept_inter_shiftedSet_nonempty_of_pairwise (i j : ℕ) (𝓕 : SetFamily)
    (hij : i < j) (hinter : PairwiseIntersecting 𝓕)
    {A G : Finset ℕ}
    (hA : A ∈ 𝓕)
    (hAkeep : j ∉ A ∨ i ∈ A ∨ shiftedSet i j A ∈ 𝓕)
    (hG : G ∈ 𝓕) (hjG : j ∈ G) (hiG : i ∉ G) :
    (A ∩ shiftedSet i j G).Nonempty := by
  by_cases hiA : i ∈ A
  · refine ⟨i, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨hiA, mem_shiftedSet_inserted_of_movable hjG hiG⟩
  by_cases hjA : j ∈ A
  · have hshiftA : shiftedSet i j A ∈ 𝓕 := by
      rcases hAkeep with hjnotA | hi_or_shift
      · exact False.elim (hjnotA hjA)
      · rcases hi_or_shift with hiA' | hshiftA
        · exact False.elim (hiA hiA')
        · exact hshiftA
    have hshiftA_ne_G : shiftedSet i j A ≠ G := by
      intro hEq
      have hi_shiftA : i ∈ shiftedSet i j A :=
        mem_shiftedSet_inserted_of_movable hjA hiA
      have : i ∈ G := by simpa [hEq] using hi_shiftA
      exact hiG this
    rcases hinter hshiftA hG hshiftA_ne_G with ⟨x, hx⟩
    have hxShiftA : x ∈ shiftedSet i j A := (Finset.mem_inter.mp hx).1
    have hxG : x ∈ G := (Finset.mem_inter.mp hx).2
    have hxi : x ≠ i := by
      intro hxi'
      exact hiG (by simpa [hxi'] using hxG)
    have hxj : x ≠ j := by
      intro hxj'
      have : j ∈ shiftedSet i j A := by simpa [hxj'] using hxShiftA
      exact not_mem_shiftedSet_erased_of_movable hij hjA hiA this
    have hxA : x ∈ A :=
      mem_of_mem_shiftedSet_ne_inserted_of_movable hjA hiA hxShiftA hxi
    refine ⟨x, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨hxA, mem_shiftedSet_of_mem_ne_erased hxG hxj⟩
  · have hAG_ne : A ≠ G := by
      intro hEq
      exact hjA (by simpa [hEq] using hjG)
    rcases hinter hA hG hAG_ne with ⟨x, hx⟩
    have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
    have hxG : x ∈ G := (Finset.mem_inter.mp hx).2
    have hxj : x ≠ j := by
      intro hxj'
      exact hjA (by simpa [hxj'] using hxA)
    refine ⟨x, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨hxA, mem_shiftedSet_of_mem_ne_erased hxG hxj⟩

private lemma shiftOperation_pairwise_of_lt (i j : ℕ) (𝓕 : SetFamily)
    (hij : i < j) (hinter : PairwiseIntersecting 𝓕) :
    PairwiseIntersecting (shiftOperation i j 𝓕) := by
  intro A B hA hB hAB
  rcases shiftOperation_mem_cases i j 𝓕 hA with hAkeep | hAmove
  · rcases shiftOperation_mem_cases i j 𝓕 hB with hBkeep | hBmove
    · exact hinter hAkeep.1 hBkeep.1 hAB
    · rcases hBmove with ⟨G, hG, hjG, hiG, hshiftG⟩
      simpa [hshiftG] using
        kept_inter_shiftedSet_nonempty_of_pairwise i j 𝓕 hij hinter
          hAkeep.1 hAkeep.2 hG hjG hiG
  · rcases hAmove with ⟨F, hF, hjF, hiF, hshiftF⟩
    rcases shiftOperation_mem_cases i j 𝓕 hB with hBkeep | hBmove
    · rcases kept_inter_shiftedSet_nonempty_of_pairwise i j 𝓕 hij hinter
          hBkeep.1 hBkeep.2 hF hjF hiF with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hxB : x ∈ B := (Finset.mem_inter.mp hx).1
      have hxShiftF : x ∈ shiftedSet i j F := (Finset.mem_inter.mp hx).2
      exact Finset.mem_inter.mpr ⟨by simpa [hshiftF] using hxShiftF, hxB⟩
    · rcases hBmove with ⟨G, hG, hjG, hiG, hshiftG⟩
      simpa [hshiftF, hshiftG] using
        shiftedSet_inter_shiftedSet_nonempty_of_movable hjF hiF hjG hiG

private lemma mem_shiftOperation_self_or_shifted_of_mem (i j : ℕ) {𝓕 : SetFamily}
    {F : Finset ℕ} (hF : F ∈ 𝓕) :
    F ∈ shiftOperation i j 𝓕 ∨ shiftedSet i j F ∈ shiftOperation i j 𝓕 := by
  classical
  unfold shiftOperation
  by_cases hmove : j ∈ F ∧ i ∉ F
  · by_cases hshift : shiftedSet i j F ∈ 𝓕
    · left
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hF, Or.inr (Or.inr hshift)⟩))
    · right
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨F, Finset.mem_filter.mpr ⟨hF, hmove⟩, rfl⟩))
  · left
    have hkeep : j ∉ F ∨ i ∈ F ∨ shiftedSet i j F ∈ 𝓕 := by
      by_cases hjF : j ∈ F
      · right
        left
        by_contra hiF
        exact hmove ⟨hjF, hiF⟩
      · exact Or.inl hjF
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hF, hkeep⟩))

private lemma not_mem_shiftedSet_of_not_mem_ne_inserted {i j x : ℕ} {F : Finset ℕ}
    (hxF : x ∉ F) (hxi : x ≠ i) :
    x ∉ shiftedSet i j F := by
  unfold shiftedSet
  by_cases hmove : j ∈ F ∧ i ∉ F
  · rw [if_pos hmove]
    intro hx
    rcases Finset.mem_insert.mp hx with hxi' | hxerase
    · exact hxi hxi'
    · exact hxF (Finset.mem_of_mem_erase hxerase)
  · rw [if_neg hmove]
    exact hxF

private lemma shiftOperation_common_inserted_of_not_empty {i j : ℕ} {𝓕 : SetFamily}
    (hempty : EmptyTotalIntersection 𝓕)
    (hnot : ¬ EmptyTotalIntersection (shiftOperation i j 𝓕)) :
    ∀ ⦃A : Finset ℕ⦄, A ∈ shiftOperation i j 𝓕 → i ∈ A := by
  classical
  unfold EmptyTotalIntersection at hempty hnot
  push Not at hnot
  rcases hnot with ⟨x, hxcommon⟩
  have hxi : x = i := by
    rcases hempty x with ⟨F, hFmem, hxF⟩
    rcases mem_shiftOperation_self_or_shifted_of_mem i j (𝓕 := 𝓕) hFmem with hFshift | hshiftF
    · exact False.elim (hxF (hxcommon F hFshift))
    · by_contra hne
      exact not_mem_shiftedSet_of_not_mem_ne_inserted hxF hne (hxcommon (shiftedSet i j F) hshiftF)
  intro A hA
  simpa [hxi] using hxcommon A hA

private lemma cover_and_opposite_side_of_common_shift {i j : ℕ} {𝓕 : SetFamily}
    (hempty : EmptyTotalIntersection 𝓕)
    {F : Finset ℕ} (hFmem : F ∈ 𝓕) (hjF : j ∈ F) (hiF : i ∉ F)
    (hnot : ¬ EmptyTotalIntersection (shiftOperation i j 𝓕)) :
    (∀ ⦃A : Finset ℕ⦄, A ∈ 𝓕 → i ∈ A ∨ j ∈ A) ∧
    (∃ A : Finset ℕ, A ∈ 𝓕 ∧ j ∈ A ∧ i ∉ A) ∧
    (∃ B : Finset ℕ, B ∈ 𝓕 ∧ i ∈ B ∧ j ∉ B) := by
  classical
  have hcommon := shiftOperation_common_inserted_of_not_empty (i := i) (j := j)
    (𝓕 := 𝓕) hempty hnot
  have hcover : ∀ ⦃A : Finset ℕ⦄, A ∈ 𝓕 → i ∈ A ∨ j ∈ A := by
    intro A hA
    by_cases hiA : i ∈ A
    · exact Or.inl hiA
    · by_cases hjA : j ∈ A
      · exact Or.inr hjA
      · exfalso
        have hAshift : A ∈ shiftOperation i j 𝓕 := by
          unfold shiftOperation
          exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_filter.mpr ⟨hA, Or.inl hjA⟩))
        exact hiA (hcommon hAshift)
  refine ⟨hcover, ⟨F, hFmem, hjF, hiF⟩, ?_⟩
  rcases hempty j with ⟨B, hBmem, hjB⟩
  rcases hcover hBmem with hiB | hjB'
  · exact ⟨B, hBmem, hiB, hjB⟩
  · exact False.elim (hjB hjB')

private lemma shiftedSet_mem_shiftOperation_of_mem_shiftOperation (i j : ℕ) {𝓕 : SetFamily}
    {A : Finset ℕ} (hA : A ∈ shiftOperation i j 𝓕) :
    shiftedSet i j A ∈ shiftOperation i j 𝓕 := by
  rw [shiftOperation_eq_uvCompression] at hA ⊢
  rw [shiftedSet_eq_uvCompress]
  exact UV.compress_mem_compression_of_mem_compression hA

private lemma shiftOperation_idem (i j : ℕ) (𝓕 : SetFamily) :
    shiftOperation i j (shiftOperation i j 𝓕) = shiftOperation i j 𝓕 := by
  simp [shiftOperation_eq_uvCompression, UV.compression_idem]

private lemma shiftOperation_empty_or_bad_shape {i j : ℕ} {𝓕 : SetFamily}
    (hempty : EmptyTotalIntersection 𝓕)
    {F : Finset ℕ} (hFmem : F ∈ 𝓕) (hjF : j ∈ F) (hiF : i ∉ F) :
    EmptyTotalIntersection (shiftOperation i j 𝓕) ∨
      ((∀ ⦃A : Finset ℕ⦄, A ∈ 𝓕 → i ∈ A ∨ j ∈ A) ∧
      (∃ A : Finset ℕ, A ∈ 𝓕 ∧ j ∈ A ∧ i ∉ A) ∧
      (∃ B : Finset ℕ, B ∈ 𝓕 ∧ i ∈ B ∧ j ∉ B)) := by
  by_cases h : EmptyTotalIntersection (shiftOperation i j 𝓕)
  · exact Or.inl h
  · exact Or.inr <| cover_and_opposite_side_of_common_shift (i := i) (j := j)
      (𝓕 := 𝓕) hempty hFmem hjF hiF h

private lemma opposite_side_sets_intersect_off_pair {i j : ℕ} {𝓕 : SetFamily}
    (hinter : PairwiseIntersecting 𝓕)
    {A B : Finset ℕ} (hA : A ∈ 𝓕) (_hjA : j ∈ A) (hiA : i ∉ A)
    (hB : B ∈ 𝓕) (hiB : i ∈ B) (hjB : j ∉ B) :
    ∃ x : ℕ, x ∈ A ∧ x ∈ B ∧ x ≠ i ∧ x ≠ j := by
  have hAB : A ≠ B := by
    intro hEq
    exact hiA (by rw [hEq]; exact hiB)
  rcases hinter hA hB hAB with ⟨x, hx⟩
  have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
  have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
  refine ⟨x, hxA, hxB, ?_, ?_⟩
  · intro hxi
    exact hiA (by simpa [hxi] using hxA)
  · intro hxj
    exact hjB (by simpa [hxj] using hxB)

/--
Source lemma `lem:Frankl-Furedi`, lines 201--206.

Source proof: apply shifts.  If shifting terminates in a shifted family with
empty total intersection, done.  Otherwise a last bad shift makes all sets
contain one element; relabel it and its partner to `1` and `2`, continue shifting
on labels at least `3`, add the `k`-sets containing `{1,2}` if necessary, and
use the boundary of `{1, ..., k+1}` as an empty-intersection subfamily preserved
by further shifts.

Prover notes: prove or import separate facts for preservation of cardinality,
pairwise intersection, uniformity, and the empty-intersection fallback under
combinatorial shifts.  A termination measure for repeated shifts will be needed.
-/
lemma franklFurediShifted (n k : ℕ) (𝓕 : SetFamily)
    (hk : 0 < k) (hF : UniformFamily n k 𝓕)
    (hinter : PairwiseIntersecting 𝓕) (hempty : EmptyTotalIntersection 𝓕) :
    ∃ 𝓕' : SetFamily,
      UniformFamily n k 𝓕' ∧ PairwiseIntersecting 𝓕' ∧
      EmptyTotalIntersection 𝓕' ∧ ShiftedOn n 𝓕' ∧ 𝓕.card ≤ 𝓕'.card := by
  classical
  by_cases hshift : ShiftedOn n 𝓕
  · exact franklFurediShifted_of_shifted n k 𝓕 hF hinter hempty hshift
  · -- TODO: formalize the non-shifted Frankl--Furedi shifting construction.
    -- This branch needs repeated shifts, preservation lemmas, and the
    -- empty-intersection boundary fallback described in the source proof.
    rw [ShiftedOn] at hshift
    push Not at hshift
    rcases hshift with ⟨i, j, F, hi, hj, hij, hFmem, hjF, hiF, hbad⟩
    let 𝓖 : SetFamily := shiftOperation i j 𝓕
    have hGunif : UniformFamily n k 𝓖 := by
      dsimp [𝓖]
      exact shiftOperation_uniform n k i j 𝓕 hi hF
    have hGinter : PairwiseIntersecting 𝓖 := by
      dsimp [𝓖]
      exact shiftOperation_pairwise_of_lt i j 𝓕 hij hinter
    have hmove : shiftedSet i j F ∈ 𝓖 := by
      dsimp [𝓖]
      exact shiftedSet_mem_shiftOperation_of_movable i j 𝓕 hFmem hjF hiF
    have hGcard : 𝓖.card = 𝓕.card := by
      dsimp [𝓖]
      exact shiftOperation_card i j 𝓕
    -- `hbad` is the first concrete bad shift: replacing `j` by `i` in `F`
    -- leaves the current family.  If this shift destroys empty total
    -- intersection, the new helper below extracts the structural fallback data
    -- used in the Frankl--Furedi proof.
    have hbadShape :
        ¬ EmptyTotalIntersection 𝓖 →
          (∀ ⦃A : Finset ℕ⦄, A ∈ 𝓕 → i ∈ A ∨ j ∈ A) ∧
          (∃ A : Finset ℕ, A ∈ 𝓕 ∧ j ∈ A ∧ i ∉ A) ∧
          (∃ B : Finset ℕ, B ∈ 𝓕 ∧ i ∈ B ∧ j ∉ B) := by
      intro hnot
      dsimp [𝓖] at hnot
      exact cover_and_opposite_side_of_common_shift (i := i) (j := j) (𝓕 := 𝓕)
        hempty hFmem hjF hiF hnot
    -- The remaining proof must either iterate good shifts preserving
    -- `EmptyTotalIntersection`, or invoke the full Frankl--Furedi
    -- relabel-and-boundary fallback starting from `hbadShape`.
    sorry

/--
Source lemma `line-328`, lines 328--334; proof in lines 336--363.

Source proof: perform shifts while preserving the stronger property that every
one-set deletion leaves empty total intersection.  If a shift would destroy this
property, stop just before it, relabel to obtain sets with `1` not `2`, with `2`
not `1`, and with both; compare with the standard family built from
`{2, ..., k+1}` and `{2, ..., k, k+2}`.  After restricted shifts on labels at
least `3`, either replace by the standard family or use the two preserved
boundary subfamilies to continue shifting until stable.

Prover notes: this is stronger than `franklFurediShifted`; expect helper lemmas
for the standard family, the two boundary subfamilies, and preservation of the
deletion-empty invariant under restricted shifts.  The bare existential output
does not by itself reflect uniqueness of the original extremal family; the final
theorem uses bridge lemmas for that step.
-/
lemma strongShiftedReduction (n k : ℕ) (𝓕 : SetFamily)
    (hk : 0 < k) (hF : UniformFamily n k 𝓕)
    (hinter : PairwiseIntersecting 𝓕)
    (hdelete : DeletionEmptyTotalIntersection 𝓕) :
    ∃ 𝓕' : SetFamily,
      UniformFamily n k 𝓕' ∧ PairwiseIntersecting 𝓕' ∧
      DeletionEmptyTotalIntersection 𝓕' ∧ ShiftedOn n 𝓕' ∧ 𝓕.card ≤ 𝓕'.card := by
  by_cases hshift : ShiftedOn n 𝓕
  · exact ⟨𝓕, hF, hinter, hdelete, hshift, le_rfl⟩
  · -- TODO: formalize the strengthened shifting construction from the source proof.
    -- The proof must preserve `DeletionEmptyTotalIntersection` through restricted
    -- shifts and the standard-family replacement step.
    sorry

end AShortProofOfTheHiltonMilnerTheorem
