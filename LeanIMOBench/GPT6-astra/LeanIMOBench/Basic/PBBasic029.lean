import LeanFlowProofs.PBBasic029PairCount
import Mathlib

/-
Let $p$ and $n$ be integers with $0\le p\le n-2$. Consider a set
$S$ of $n$ lines in the plane such that no two of them are parallel
and no three have a common point. Denote by $I$ the set of intersections
of lines in $S$. Let $O$ be a point in the plane not lying on any
line of $S$. A point $X\in I$ is colored red if the open line segment
$OX$ intersects at most $p$ lines in $S$. What is the minimum number
of red points that is contained in $I$?
Answer: $\frac{(p + 1)(p + 2)}{2}$
-/
open Affine
abbrev Point := EuclideanSpace ℝ (Fin 2)

def Line := {l : AffineSubspace ℝ Point // Module.rank ℝ l.direction = 1}
local instance : Membership Point Line where mem l X := X ∈ l.1

/-
A set of lines is in a general position if no two lines are parallel, and no three lines are concurrent.
-/
abbrev GeneralPosition (lines : Set Line) : Prop :=
  (∀ l1 ∈ lines, ∀ l2 ∈ lines, l1 ≠ l2 → ¬ l1.1 ∥ l2.1) ∧
  (∀ l1 ∈ lines, ∀ l2 ∈ lines, ∀ l3 ∈ lines, l1 ≠ l2 → l1 ≠ l3 → l2 ≠ l3 →
    (l1.1 : Set Point) ∩ l2.1 ∩ l3.1 = ∅)

-- The set of all intersections of a set of lines
abbrev intersections (lines : Set Line) : Set Point :=
  { X : Point | ∃ l1 ∈ lines, ∃ l2 ∈ lines, l1 ≠ l2 ∧ X ∈ l1 ∧ X ∈ l2 }

-- A point avoids a set of lines if it is not contained in any
abbrev Point.avoids (lines : Set Line) (X : Point) := ∀ l ∈ lines, X ∉ l

-- A predicate claiming that there at most `k` lines strictly between `O` `X`
abbrev atMostBetween (lines : Set Line) (p : ℕ) (O X : Point) : Prop :=
  { line ∈ lines | ∃ inter : Point, Sbtw ℝ O inter X ∧ inter ∈ line }.encard ≤ p

-- All points in the plane that have at most `p` lines
abbrev redPoints (lines : Set Line) (p : ℕ) (O : Point) : Set Point :=
  atMostBetween lines p O

-- The minimum possible number of red intersections given `p` and `n`
noncomputable
def minRed (p n : ℕ) : ℕ := sInf {
  (intersections lines ∩ redPoints lines p O).encard |
  -- we consider all general positions of `n` lines
  (lines : Set Line) (_ : lines.encard = n) (_ : GeneralPosition lines)
  -- and all positions of the point `O`
  (O : Point) (_ : O.avoids lines)
}

theorem PBBasic029 (p n : ℕ) (le : p+2 ≤ n) :
  minRed p n = (p+1) * (p+2) / 2 := by 
  classical
  have crossing (f : Point →ₗ[ℝ] ℝ) (c : ℝ) (O X : Point)
      (hO : f O ≠ c) :
      (∃ Y : Point, Sbtw ℝ O Y X ∧ f Y = c) ↔
        (f O - c) * (f X - c) < 0 := by
    constructor
    · rintro ⟨Y, ⟨⟨t, ht, rfl⟩, hYO, hYX⟩, hY⟩
      have ht0 : 0 < t := by
        apply lt_of_le_of_ne ht.1
        intro h
        apply hYO
        simp [← h]
      have ht1 : t < 1 := by
        apply lt_of_le_of_ne ht.2
        intro h
        apply hYX
        simp [h]
      have hf : t * (f X - f O) + f O = c := by
        simpa [AffineMap.lineMap_apply, map_add, map_smul, map_sub] using hY
      rcases lt_or_gt_of_ne hO with ho | ho
      · have hx : c < f X := by
          by_contra! hx
          nlinarith [mul_nonneg (le_of_lt ht0) (sub_nonneg.mpr hx),
            mul_pos (sub_pos.mpr ht1) (sub_pos.mpr ho)]
        exact mul_neg_of_neg_of_pos (sub_neg.mpr ho) (sub_pos.mpr hx)
      · have hx : f X < c := by
          by_contra! hx
          nlinarith [mul_nonneg (le_of_lt ht0) (sub_nonneg.mpr hx),
            mul_pos (sub_pos.mpr ht1) (sub_pos.mpr ho)]
        exact mul_neg_of_pos_of_neg (sub_pos.mpr ho) (sub_neg.mpr hx)
    · intro h
      have hx : f X ≠ c := by
        intro he
        simp [he] at h
      have hd : f X - f O ≠ 0 := by
        intro he
        have he' : f X = f O := sub_eq_zero.mp he
        rw [he'] at h
        nlinarith [sq_nonneg (f O - c)]
      let t := (c - f O) / (f X - f O)
      have ht : 0 < t ∧ t < 1 := by
        rcases mul_neg_iff.mp h with ⟨ho, hx'⟩ | ⟨ho, hx'⟩
        · have hd' : f X - f O < 0 := by linarith
          constructor
          · exact div_pos_of_neg_of_neg (by linarith) hd'
          · exact (div_lt_one_of_neg hd').mpr (by linarith)
        · have hd' : 0 < f X - f O := by linarith
          constructor
          · exact div_pos (by linarith) hd'
          · exact (div_lt_one hd').mpr (by linarith)
      have hf : f (AffineMap.lineMap O X t) = c := by
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          map_add, map_smul, map_sub, smul_eq_mul]
        dsimp [t]
        field_simp
        <;> ring
      refine ⟨AffineMap.lineMap O X t, ⟨?_, ?_, ?_⟩, hf⟩
      · exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
      · intro he
        exact hO (he ▸ hf)
      · intro he
        exact hx (he ▸ hf)
  have gp_mono {L M : Set Line} (hML : M ⊆ L)
      (hL : GeneralPosition L) : GeneralPosition M := by
    constructor
    · intro a ha b hb hab
      exact hL.1 a (hML ha) b (hML hb) hab
    · intro a ha b hb c hc hab hac hbc
      exact hL.2 a (hML ha) b (hML hb) c (hML hc) hab hac hbc
  have avoids_mono {L M : Set Line} (hML : M ⊆ L)
      {O : Point} (hO : O.avoids L) : O.avoids M := by
    intro a ha
    exact hO a (hML ha)
  have intersections_mono {L M : Set Line} (hML : M ⊆ L) :
      intersections M ⊆ intersections L := by
    rintro X ⟨a, ha, b, hb, hab, hXa, hXb⟩
    exact ⟨a, hML ha, b, hML hb, hab, hXa, hXb⟩
  have intersections_delete_off {L : Set Line} (hL : GeneralPosition L)
      {a : Line} (ha : a ∈ L) :
      ∀ X ∈ intersections (L \ {a}), X ∉ a := by
    rintro X ⟨b, hb, c, hc, hbc, hXb, hXc⟩ hXa
    have hba : b ≠ a := by simpa using hb.2
    have hca : c ≠ a := by simpa using hc.2
    have hh := hL.2 b hb.1 c hc.1 a ha hbc hba hca
    have hm : X ∈ (b.1 : Set Point) ∩ c.1 ∩ a.1 := ⟨⟨hXb, hXc⟩, hXa⟩
    rw [hh] at hm
    exact hm
  have restore_red {L : Set Line} (a : Line) (q : ℕ) (O X : Point)
      (hX : atMostBetween (L \ {a}) q O X) : atMostBetween L (q+1) O X := by
    let C : Set Line := {l ∈ L | ∃ Y : Point, Sbtw ℝ O Y X ∧ Y ∈ l}
    let D : Set Line := {l ∈ L \ {a} | ∃ Y : Point, Sbtw ℝ O Y X ∧ Y ∈ l}
    have hs : C ⊆ insert a D := by
      intro l hl
      by_cases he : l = a
      · exact Set.mem_insert_iff.mpr (Or.inl he)
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨⟨hl.1, he⟩, hl.2⟩)
    change C.encard ≤ ((q+1 : ℕ) : ENat)
    calc
      C.encard ≤ (insert a D).encard := Set.encard_mono hs
      _ ≤ D.encard + 1 := Set.encard_insert_le _ _
      _ ≤ (q : ENat) + 1 := add_le_add hX le_rfl
      _ = ((q+1 : ℕ) : ENat) := by simp
  have rank_selection (q : ℕ) (S : Finset ℝ) (v : ℝ) :
      ∃ T : Finset ℝ, T ⊆ S ∧ T.card = min (q+1) S.card ∧
        ∀ x ∈ T, (S.filter (fun y => |y-v| < |x-v|)).card ≤ q := by
    classical
    induction q generalizing S with
    | zero =>
      by_cases hS : S.Nonempty
      · obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image S (fun x => |x-v|) hS
        refine ⟨{a}, Finset.singleton_subset_iff.mpr ha, ?_, ?_⟩
        · simp only [Finset.card_singleton, Nat.zero_add]
          exact (Nat.min_eq_left (Finset.card_pos.mpr hS)).symm
        · intro x hx
          have hx' : x = a := Finset.mem_singleton.mp hx
          subst x
          have hh : S.filter (fun y => |y-v| < |a-v|) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro y hy
            exact (not_lt_of_ge (hmin y (Finset.mem_filter.mp hy).1))
              (Finset.mem_filter.mp hy).2
          simp [hh]
      · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
        · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
        · simp
    | succ q ih =>
      by_cases hS : S.Nonempty
      · obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image S (fun x => |x-v|) hS
        obtain ⟨T, hTS, hTcard, hT⟩ := ih (S.erase a)
        refine ⟨insert a T, ?_, ?_, ?_⟩
        · exact Finset.insert_subset ha (hTS.trans (Finset.erase_subset _ _))
        · have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTS h)).1 rfl
          rw [Finset.card_insert_of_notMem haT, hTcard, Finset.card_erase_of_mem ha]
          have hs : 0 < S.card := Finset.card_pos.mpr hS
          omega
        · intro x hx
          rcases Finset.mem_insert.mp hx with he | hx
          · subst x
            have hh : S.filter (fun y => |y-v| < |a-v|) = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro y hy
              exact (not_lt_of_ge (hmin y (Finset.mem_filter.mp hy).1))
                (Finset.mem_filter.mp hy).2
            simp [hh]
          · have hs : S.filter (fun y => |y-v| < |x-v|) ⊆
                insert a ((S.erase a).filter (fun y => |y-v| < |x-v|)) := by
              intro y hy
              by_cases he : y = a
              · simp [he]
              · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
                  ⟨Finset.mem_erase.mpr ⟨he, (Finset.mem_filter.mp hy).1⟩,
                    (Finset.mem_filter.mp hy).2⟩))
            exact (Finset.card_le_card hs).trans
              ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hT x hx) 1))
      · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
        · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
        · simp
  have abs_between {v y x : ℝ} (h : Sbtw ℝ v y x) : |y-v| < |x-v| := by
    rcases h with ⟨⟨t, ht, rfl⟩, hyv, hyx⟩
    have ht1 : t < 1 := by
      apply lt_of_le_of_ne ht.2
      intro he
      apply hyx
      simp [he]
    have hxv : x - v ≠ 0 := by
      intro he
      have hxv := sub_eq_zero.mp he
      apply hyv
      simp [hxv]
    have he : AffineMap.lineMap v x t - v = t * (x-v) := by
      simp [AffineMap.lineMap_apply]
    rw [he, abs_mul, abs_of_nonneg ht.1]
    simpa using mul_lt_mul_of_pos_right ht1 (abs_pos.mpr hxv)
  have rank_between (q : ℕ) (S : Finset ℝ) (v : ℝ) :
      ∃ T : Finset ℝ, T ⊆ S ∧ T.card = min (q+1) S.card ∧
        ∀ x ∈ T, (S.filter (fun y => Sbtw ℝ v y x)).card ≤ q := by
    classical
    obtain ⟨T, hTS, hcard, hT⟩ := rank_selection q S v
    refine ⟨T, hTS, hcard, ?_⟩
    intro x hx
    apply le_trans (Finset.card_le_card _) (hT x hx)
    intro y hy
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
      abs_between (Finset.mem_filter.mp hy).2⟩
  have triangular_step (q : ℕ) :
      (q+1)*(q+2)/2 + (q+2) = (q+2)*(q+3)/2 := by
    have he : (q+2)*(q+3) = (q+1)*(q+2) + 2*(q+2) := by ring
    omega
  have lower_of_incident
      (incident : ∀ (q m : ℕ), q+2 ≤ m → ∀ (L : Set Line),
        L.encard = (m : ENat) → GeneralPosition L → ∀ (O : Point),
        O.avoids L → ∃ a ∈ L,
          ((q+1 : ℕ) : ENat) ≤
            ((intersections L ∩ redPoints L q O) ∩ (a.1 : Set Point)).encard) :
      ∀ (q m : ℕ), q+2 ≤ m → ∀ (L : Set Line),
        L.encard = (m : ENat) → GeneralPosition L → ∀ (O : Point),
        O.avoids L → (((q+1)*(q+2)/2 : ℕ) : ENat) ≤
          (intersections L ∩ redPoints L q O).encard := by
    intro q
    induction q with
    | zero =>
      intro m hqm L hcard hgp O hO
      obtain ⟨a, ha, hred⟩ := incident 0 m hqm L hcard hgp O hO
      exact hred.trans (Set.encard_mono Set.inter_subset_left)
    | succ q ih =>
      intro m hqm L hcard hgp O hO
      obtain ⟨a, ha, hred⟩ := incident (q+1) m hqm L hcard hgp O hO
      have hcard' : (L \ {a}).encard = ((m-1 : ℕ) : ENat) := by
        rw [Set.encard_diff_singleton_of_mem ha, hcard]
        simp
      have hsub : L \ {a} ⊆ L := Set.diff_subset
      have hlow := ih (m-1) (by omega) (L \ {a}) hcard'
        (gp_mono hsub hgp) O (avoids_mono hsub hO)
      let A := intersections (L \ {a}) ∩ redPoints (L \ {a}) q O
      let B := (intersections L ∩ redPoints L (q+1) O) ∩ (a.1 : Set Point)
      have hdis : Disjoint A B := by
        apply Set.disjoint_left.mpr
        intro X hXA hXB
        exact intersections_delete_off hgp ha X hXA.1 hXB.2
      have hsubset : A ∪ B ⊆ intersections L ∩ redPoints L (q+1) O := by
        intro X hX
        rcases hX with hX | hX
        · exact ⟨intersections_mono hsub hX.1, restore_red a q O X hX.2⟩
        · exact hX.1
      calc
        (((q+1+1)*(q+1+2)/2 : ℕ) : ENat) =
            (((q+1)*(q+2)/2 : ℕ) : ENat) + ((q+2 : ℕ) : ENat) := by
          rw [← Nat.cast_add, triangular_step]
        _ ≤ A.encard + B.encard := add_le_add hlow hred
        _ = (A ∪ B).encard := (Set.encard_union_eq hdis).symm
        _ ≤ (intersections L ∩ redPoints L (q+1) O).encard := Set.encard_mono hsubset
  have root_of_bounds
      (lower : ∀ (L : Set Line), L.encard = (n : ENat) → GeneralPosition L →
        ∀ O : Point, O.avoids L → (((p+1)*(p+2)/2 : ℕ) : ENat) ≤
          (intersections L ∩ redPoints L p O).encard)
      (witness : ∃ (L : Set Line), L.encard = (n : ENat) ∧ GeneralPosition L ∧
        ∃ O : Point, O.avoids L ∧
          (intersections L ∩ redPoints L p O).encard = (((p+1)*(p+2)/2 : ℕ) : ENat)) :
      minRed p n = (p+1)*(p+2)/2 := by
    unfold minRed
    obtain ⟨L, hcard, hgp, O, hO, hred⟩ := witness
    have hmem : (p+1)*(p+2)/2 ∈ {x : ℕ | ∃ L : Set Line,
        ∃ (_ : L.encard = (n : ENat)) (_ : GeneralPosition L),
        ∃ O : Point, ∃ (_ : O.avoids L),
          (intersections L ∩ redPoints L p O).encard = (x : ENat)} :=
      ⟨L, hcard, hgp, O, hO, hred⟩
    apply le_antisymm
    · exact Nat.sInf_le hmem
    · apply le_csInf ⟨_, hmem⟩
      rintro k ⟨M, hc, hg, P, hP, hr⟩
      have hh := lower M hc hg P hP
      rw [hr] at hh
      exact_mod_cast hh
  have line_param (l : Line) : ∃ (A d : Point), d ≠ 0 ∧
      ∀ X : Point, X ∈ l ↔ ∃ t : ℝ, X = t • d + A := by
    unfold Line at l
    have hnonempty : (l.1 : Set Point).Nonempty := by
      rcases l.1.eq_bot_or_nonempty with he | he
      · have hr : Module.rank ℝ l.1.direction = 1 := l.2
        rw [he] at hr
        have hb : Module.rank ℝ (⊥ : Submodule ℝ Point) = 0 := rank_bot ℝ Point
        have he' : Module.rank ℝ (⊥ : AffineSubspace ℝ Point).direction = 0 := by
          rw [AffineSubspace.direction_bot]
          exact hb
        exact False.elim (zero_ne_one (he'.symm.trans hr))
      · exact he
    obtain ⟨A, hA⟩ := hnonempty
    obtain ⟨d, hd, hs⟩ := finrank_eq_one_iff'.mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp l.2)
    refine ⟨A, d, ?_, ?_⟩
    · intro he
      apply hd
      exact Subtype.ext he
    · intro X
      constructor
      · intro hX
        have hXA : X - A ∈ l.1.direction := l.1.vsub_mem_direction hX hA
        obtain ⟨t, ht⟩ := hs ⟨X-A, hXA⟩
        refine ⟨t, ?_⟩
        have ht' : t • (d : Point) = X-A := congrArg Subtype.val ht
        rw [ht']
        exact (sub_add_cancel X A).symm
      · rintro ⟨t, rfl⟩
        exact l.1.vadd_mem_of_mem_direction (l.1.direction.smul_mem t d.2) hA
  let dot (u : Point) : Point →ₗ[ℝ] ℝ :=
    { toFun := fun X => u 0 * X 0 + u 1 * X 1
      map_add' := by intro X Y; simp; ring
      map_smul' := by intro t X; simp; ring }
  have dot_apply (u X : Point) : dot u X = u 0 * X 0 + u 1 * X 1 := rfl
  have det_zero (d W : Point) (hd : d ≠ 0) :
      -d 1 * W 0 + d 0 * W 1 = 0 ↔ ∃ t : ℝ, W = t • d := by
    constructor
    · intro h
      by_cases hd0 : d 0 = 0
      · have hd1 : d 1 ≠ 0 := by
          intro he
          apply hd
          ext i
          fin_cases i <;> simp [hd0, he]
        refine ⟨W 1 / d 1, ?_⟩
        ext i
        fin_cases i
        · change W 0 = W 1 / d 1 * d 0
          rw [hd0, mul_zero]
          have hh : d 1 * W 0 = 0 := by rw [hd0] at h; nlinarith only [h]
          exact (mul_eq_zero.mp hh).resolve_left hd1
        · simp [PiLp.smul_apply, hd1]
      · refine ⟨W 0 / d 0, ?_⟩
        ext i
        fin_cases i
        · simp [PiLp.smul_apply, hd0]
        · change W 1 = W 0 / d 0 * d 1
          field_simp
          nlinarith only [h]
    · rintro ⟨t, rfl⟩
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
  have line_normal (l : Line) : ∃ (u : Point) (c : ℝ), u ≠ 0 ∧
      ∀ X : Point, X ∈ l ↔ dot u X = c := by
    obtain ⟨A, d, hd, hparam⟩ := line_param l
    let u : Point := !₂[-d 1, d 0]
    have hu0 : u 0 = -d 1 := rfl
    have hu1 : u 1 = d 0 := rfl
    refine ⟨u, dot u A, ?_, ?_⟩
    · intro hu
      apply hd
      have h0 : -d 1 = 0 := by simpa [hu0] using congrArg (fun X : Point => X 0) hu
      have h1 : d 0 = 0 := by simpa [hu1] using congrArg (fun X : Point => X 1) hu
      ext i
      fin_cases i
      · exact h1
      · exact neg_eq_zero.mp h0
    · intro X
      rw [hparam X]
      have hdet := det_zero d (X-A) hd
      have he : (∃ t : ℝ, X = t • d + A) ↔ ∃ t : ℝ, X-A = t • d := by
        constructor
        · rintro ⟨t, rfl⟩; exact ⟨t, add_sub_cancel_right _ _⟩
        · rintro ⟨t, ht⟩; exact ⟨t, (sub_eq_iff_eq_add.mp ht)⟩
      rw [he, ← hdet]
      simp only [dot_apply, hu0, hu1, PiLp.sub_apply]
      constructor <;> intro h <;> nlinarith only [h]
  have normalized (l : Line) (O : Point) (hO : O ∉ l) : ∃ u : Point,
      u ≠ 0 ∧ ∀ X : Point, X ∈ l ↔ dot u (X-O) = 1 := by
    obtain ⟨u, c, hu, hform⟩ := line_normal l
    have hden : c - dot u O ≠ 0 := sub_ne_zero.mpr (Ne.symm (mt (hform O).mpr hO))
    refine ⟨(c-dot u O)⁻¹ • u, smul_ne_zero (inv_ne_zero hden) hu, ?_⟩
    intro X
    rw [hform]
    have he : dot ((c-dot u O)⁻¹ • u) (X-O) = (dot u X-dot u O)/(c-dot u O) := by
      simp only [dot_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring
    rw [he, div_eq_one_iff_eq hden]
    constructor <;> intro h <;> linarith only [h]
  have dot_pos (u : Point) (hu : u ≠ 0) : 0 < dot u u := by
    rw [dot_apply]
    have hn : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_contra! hh
      apply hu
      ext i
      fin_cases i <;> simp [hh.1, hh.2]
    rcases hn with hn | hn
    · nlinarith only [sq_pos_of_ne_zero hn, sq_nonneg (u 1)]
    · nlinarith only [sq_pos_of_ne_zero hn, sq_nonneg (u 0)]
  have dot_strict (u v : Point) (hne : v ≠ u)
      (hle : dot v v ≤ dot u u) : dot v u < dot u u := by
    have hn : v 0 - u 0 ≠ 0 ∨ v 1 - u 1 ≠ 0 := by
      by_contra! hh
      apply hne
      ext i
      fin_cases i
      · exact sub_eq_zero.mp hh.1
      · exact sub_eq_zero.mp hh.2
    simp only [dot_apply] at hle ⊢
    rcases hn with hn | hn
    · nlinarith only [hle, sq_pos_of_ne_zero hn, sq_nonneg (v 1-u 1)]
    · nlinarith only [hle, sq_pos_of_ne_zero hn, sq_nonneg (v 0-u 0)]
  have exposed (L : Set Line) (hfin : L.Finite) (hnon : L.Nonempty)
      (O : Point) (hO : O.avoids L) : ∃ a ∈ L, ∃ V : Point, V ∈ a ∧
        ∀ b ∈ L, b ≠ a → ∃ u : Point, u ≠ 0 ∧
          (∀ X : Point, X ∈ b ↔ dot u (X-O) = 1) ∧ dot u (V-O) < 1 := by
    letI : Fintype L := hfin.fintype
    have hn : ∀ l : L, ∃ u : Point, u ≠ 0 ∧
        ∀ X : Point, X ∈ l.val ↔ dot u (X-O) = 1 :=
      fun l => normalized l.val O (hO l.val l.property)
    choose u hu hf using hn
    have hnon' : (Finset.univ : Finset L).Nonempty := by
      obtain ⟨l, hl⟩ := hnon
      exact ⟨⟨l, hl⟩, Finset.mem_univ _⟩
    obtain ⟨a, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun l : L => dot (u l) (u l)) hnon'
    let V : Point := (dot (u a) (u a))⁻¹ • u a + O
    have hpos := dot_pos (u a) (hu a)
    have heV : V-O = (dot (u a) (u a))⁻¹ • u a := add_sub_cancel_right _ _
    refine ⟨a.val, a.property, V, ?_, ?_⟩
    · apply (hf a V).mpr
      rw [heV, map_smul]
      simp [ne_of_gt hpos]
    · intro b hb hba
      let b' : L := ⟨b, hb⟩
      refine ⟨u b', hu b', hf b', ?_⟩
      have hne : u b' ≠ u a := by
        intro he
        apply hba
        apply Subtype.ext
        apply AffineSubspace.ext
        intro X
        exact (hf b' X).trans ((by rw [he] : dot (u b') (X-O) = 1 ↔ dot (u a) (X-O) = 1).trans (hf a X).symm)
      have hlt := dot_strict (u a) (u b') hne (hmax b' (Finset.mem_univ _))
      rw [heV, map_smul]
      change (dot (u a) (u a))⁻¹ * dot (u b') (u a) < 1
      rw [← div_eq_inv_mul]
      exact (div_lt_one hpos).mpr hlt
  have line_param_at (a : Line) (V : Point) (hV : V ∈ a) : ∃ d : Point,
      d ≠ 0 ∧ ∀ X : Point, X ∈ a ↔ ∃ t : ℝ, X = t • d + V := by
    obtain ⟨A, d, hd, hp⟩ := line_param a
    obtain ⟨v, hv⟩ := (hp V).mp hV
    refine ⟨d, hd, ?_⟩
    intro X
    rw [hp X]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t-v, ?_⟩
      rw [hv]
      module
    · rintro ⟨t, rfl⟩
      refine ⟨t+v, ?_⟩
      rw [hv]
      module
  have slope_nonzero (a b : Line) (hnp : ¬ a.1 ∥ b.1)
      (V d O u : Point) (hd : d ≠ 0)
      (hp : ∀ X : Point, X ∈ a ↔ ∃ t : ℝ, X = t • d + V)
      (hf : ∀ X : Point, X ∈ b ↔ dot u (X-O) = 1) : dot u d ≠ 0 := by
    have hV : V ∈ a := (hp V).mpr ⟨0, by simp⟩
    obtain ⟨B, e, he, hb⟩ := line_param b
    have hB : B ∈ b := (hb B).mpr ⟨0, by simp⟩
    intro hz
    have hsub : a.1.direction ≤ b.1.direction := by
      intro w hw
      have hwa : w + V ∈ a := a.1.vadd_mem_of_mem_direction hw hV
      obtain ⟨t, ht⟩ := (hp (w+V)).mp hwa
      have hw' : w = t • d := add_right_cancel ht
      have hwb : w+B ∈ b := by
        apply (hf (w+B)).mpr
        have heq : w+B-O = w+(B-O) := by abel
        rw [heq, map_add, hw', map_smul, hz, smul_zero, zero_add]
        exact (hf B).mp hB
      exact (b.1.vadd_mem_iff_mem_direction w hB).mp hwb
    have hdir : a.1.direction = b.1.direction :=
      Submodule.eq_of_le_of_finrank_eq hsub (by
        rw [Module.rank_eq_one_iff_finrank_eq_one.mp a.2,
          Module.rank_eq_one_iff_finrank_eq_one.mp b.2])
    apply hnp
    apply AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot.mpr
    refine ⟨hdir, ?_⟩
    have ha0 : a.1 ≠ ⊥ := by
      intro hh
      have : V ∈ (⊥ : AffineSubspace ℝ Point) := hh ▸ hV
      exact this
    have hb0 : b.1 ≠ ⊥ := by
      intro hh
      have : B ∈ (⊥ : AffineSubspace ℝ Point) := hh ▸ hB
      exact this
    simp [ha0, hb0]
  have normalized_crossing (b : Line) (O u : Point)
      (hf : ∀ X : Point, X ∈ b ↔ dot u (X-O) = 1) (X : Point) :
      (∃ Y : Point, Sbtw ℝ O Y X ∧ Y ∈ b) ↔ 1 < dot u (X-O) := by
    have he (Y : Point) : Y ∈ b ↔ dot u Y = 1 + dot u O := by
      rw [hf, map_sub]
      constructor <;> intro h <;> linarith only [h]
    simp only [he]
    rw [crossing (dot u) (1+dot u O) O X (by linarith)]
    rw [map_sub]
    constructor <;> intro h <;> nlinarith only [h]
  have abs_quotient_lt (k r t : ℝ) (hk : 0 < k) (h : k < r*t) :
      |k/r| < |t| := by
    have hr : r ≠ 0 := by intro he; rw [he, zero_mul] at h; linarith
    rw [abs_div, abs_of_pos hk]
    apply (div_lt_iff₀ (abs_pos.mpr hr)).mpr
    have hh : r*t ≤ |r| * |t| := by rw [← abs_mul]; exact le_abs_self _
    nlinarith only [h, hh]
  have incident (q m : ℕ) (hqm : q+2 ≤ m) (L : Set Line)
      (hcard : L.encard = (m : ENat)) (hgp : GeneralPosition L)
      (O : Point) (hO : O.avoids L) :
      ∃ a ∈ L, ((q+1 : ℕ) : ENat) ≤
        (intersections L ∩ redPoints L q O ∩ (a.1 : Set Point)).encard := by
    have hfin : L.Finite := Set.encard_ne_top_iff.mp (by rw [hcard]; simp)
    have hnon : L.Nonempty := by
      apply Set.encard_pos.mp
      rw [hcard]
      exact_mod_cast (show 0 < m by omega)
    obtain ⟨a, ha, V, hV, hex⟩ := exposed L hfin hnon O hO
    obtain ⟨d, hd, hp⟩ := line_param_at a V hV
    let D : Set Line := L \ {a}
    have hDfin : D.Finite := hfin.subset Set.sdiff_subset
    letI : Fintype D := hDfin.fintype
    have hn : ∀ b : D, ∃ u : Point, u ≠ 0 ∧
        (∀ X : Point, X ∈ b.val ↔ dot u (X-O) = 1) ∧ dot u (V-O) < 1 :=
      fun b => hex b.val b.property.1 b.property.2
    choose u hu hf hlt using hn
    have hslope (b : D) : dot (u b) d ≠ 0 :=
      slope_nonzero a b.val (hgp.1 a ha b.val b.property.1
        (Ne.symm b.property.2)) V d O (u b) hd hp (hf b)
    let τ : D → ℝ := fun b => (1-dot (u b) (V-O)) / dot (u b) d
    let F : ℝ → Point := fun t => t • d + V
    have hFa (t : ℝ) : F t ∈ a := (hp (F t)).mpr ⟨t, rfl⟩
    have hFb (b : D) : F (τ b) ∈ b.val := by
      apply (hf b (F (τ b))).mpr
      have he : F (τ b)-O = τ b • d + (V-O) := by dsimp [F]; abel
      rw [he, map_add, map_smul]
      change τ b * dot (u b) d + dot (u b) (V-O) = 1
      dsimp [τ]
      rw [div_mul_cancel₀ _ (hslope b)]
      ring
    have hτ : Function.Injective τ := by
      intro b c he
      by_contra hne
      have hne' : b.val ≠ c.val := fun hh => hne (Subtype.ext hh)
      have hz := hgp.2 a ha b.val b.property.1 c.val c.property.1
        (Ne.symm b.property.2) (Ne.symm c.property.2) hne'
      have hm : F (τ b) ∈ (a.1 : Set Point) ∩ b.val.1 ∩ c.val.1 :=
        ⟨⟨hFa _, hFb b⟩, he ▸ hFb c⟩
      rw [hz] at hm
      exact hm
    have hF : Function.Injective F := by
      intro t s he
      have hsm : (t-s) • d = 0 := by
        rw [sub_smul, sub_eq_zero]
        exact add_right_cancel he
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsm).resolve_right hd)
    let S : Finset ℝ := Finset.univ.image τ
    have hScard : S.card = m-1 := by
      have hce : D.encard = ((m-1 : ℕ) : ENat) := by
        dsimp [D]
        rw [Set.encard_sdiff_singleton_of_mem ha, hcard]
        simp
      have hde : D.encard = (Fintype.card D : ENat) := by
        rw [Set.encard_eq_coe_toFinset_card]
        simp only [Set.toFinset_card]
      have hc : Fintype.card D = m-1 := by exact_mod_cast hde.symm.trans hce
      dsimp [S]
      rw [Finset.card_image_of_injective _ hτ, Finset.card_univ, hc]
    obtain ⟨T, hTS, hTc, hT⟩ := rank_selection q S 0
    have hTc' : T.card = q+1 := by rw [hTc, hScard, min_eq_left]; omega
    refine ⟨a, ha, ?_⟩
    have hsubset : (↑(T.image F) : Set Point) ⊆
        intersections L ∩ redPoints L q O ∩ (a.1 : Set Point) := by
      intro X hX
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨b, _, hbt⟩ := Finset.mem_image.mp (hTS ht)
      refine ⟨⟨?_, ?_⟩, hFa t⟩
      · refine ⟨a, ha, b.val, b.property.1, Ne.symm b.property.2, hFa _, ?_⟩
        rw [← hbt]; exact hFb b
      · let C : Set Line := {b ∈ L | ∃ Y : Point, Sbtw ℝ O Y (F t) ∧ Y ∈ b}
        have hCD : C ⊆ D := by
          intro b hb
          refine ⟨hb.1, ?_⟩
          intro he
          obtain ⟨w, hw, hwf⟩ := normalized a O (hO a ha)
          have hh := (normalized_crossing a O w hwf (F t)).mp (he ▸ hb.2)
          have hha := (hwf (F t)).mp (hFa t)
          linarith only [hh, hha]
        have hcross (b : C) : |τ ⟨b.val, hCD b.property⟩| < |t| := by
          let b' : D := ⟨b.val, hCD b.property⟩
          have hh := (normalized_crossing b.val O (u b') (hf b') (F t)).mp b.property.2
          have he : F t-O = t • d+(V-O) := by dsimp [F]; abel
          rw [he, map_add, map_smul] at hh
          apply abs_quotient_lt _ _ _ (sub_pos.mpr (hlt b'))
          change 1 < t * dot (u b') d + dot (u b') (V-O) at hh
          nlinarith only [hh]
        have hbound : C.encard ≤ (S.filter (fun y => |y| < |t|)).card := by
          rw [← Set.encard_coe_eq_coe_finsetCard]
          apply Set.encard_le_encard_of_injOn
            (f := fun b : Line => if hb : b ∈ D then τ ⟨b, hb⟩ else 0)
          · intro b hb
            simp only [Set.mem_preimage, Set.mem_setOf_eq, Finset.mem_coe,
              Finset.mem_filter]
            rw [dif_pos (hCD hb)]
            exact ⟨Finset.mem_image.mpr ⟨⟨b, hCD hb⟩, Finset.mem_univ _, rfl⟩,
              hcross ⟨b, hb⟩⟩
          · intro b hb c hc he
            simp only [dif_pos (hCD hb), dif_pos (hCD hc)] at he
            exact congrArg Subtype.val (hτ he)
        exact hbound.trans (by exact_mod_cast (by simpa using hT t ht))
    have hcnt : ((q+1 : ℕ) : ENat) = (↑(T.image F) : Set Point).encard := by
      rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hF, hTc']
    exact hcnt.trans_le (Set.encard_mono hsubset)
  have universal_lower := lower_of_incident incident
  apply root_of_bounds (universal_lower p n le)
  have mkline (A d : Point) (hd : d ≠ 0) : ∃ l : Line,
      l.1.direction = Submodule.span ℝ {d} ∧
      ∀ X : Point, X ∈ l ↔ ∃ t : ℝ, X = t • d + A := by
    let s := AffineSubspace.mk' A (Submodule.span ℝ {d})
    have hr : Module.rank ℝ s.direction = 1 := by
      rw [AffineSubspace.direction_mk']
      exact (Module.rank_eq_one_iff_finrank_eq_one).mpr
        (finrank_span_singleton hd)
    refine ⟨⟨s, hr⟩, AffineSubspace.direction_mk' _ _, ?_⟩
    intro X
    change X ∈ s ↔ _
    rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
    change (∃ t : ℝ, t • d = X-A) ↔ _
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [ht]; abel⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, by abel⟩
  let C : ℝ := (n : ℝ)^2+1
  have hC : 0 < C := by dsimp [C]; positivity
  let v : Fin n → Point := fun i => !₂[(i.val : ℝ), C+(i.val : ℝ)^2]
  let d : Fin n → Point := fun i => !₂[C+(i.val : ℝ)^2, -(i.val : ℝ)]
  let A : Fin n → Point := fun i => !₂[0, 1/(C+(i.val : ℝ)^2)]
  have hden (i : Fin n) : 0 < C+(i.val : ℝ)^2 := by positivity
  have hd (i : Fin n) : d i ≠ 0 := by
    intro he
    have hh : C+(i.val : ℝ)^2 = 0 := by simpa [d] using congrArg (fun X : Point => X 0) he
    linarith only [hh, hden i]
  choose ell hell_dir hell using fun i => mkline (A i) (d i) (hd i)
  have hell_eq (i : Fin n) (X : Point) : X ∈ ell i ↔ dot (v i) X = 1 := by
    rw [hell]
    constructor
    · rintro ⟨t, rfl⟩
      simp only [dot_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      change (i.val : ℝ) * (t*(C+(i.val : ℝ)^2)+0) +
        (C+(i.val : ℝ)^2)*(t*(-(i.val : ℝ))+1/(C+(i.val : ℝ)^2)) = 1
      field_simp
      <;> ring
    · intro he
      refine ⟨X 0 / (C+(i.val : ℝ)^2), ?_⟩
      have he' : (i.val : ℝ)*X 0 + (C+(i.val : ℝ)^2)*X 1 = 1 := he
      ext k
      fin_cases k
      · change X 0 = X 0/(C+(i.val : ℝ)^2)*(C+(i.val : ℝ)^2)+0
        rw [div_mul_cancel₀ _ (ne_of_gt (hden i)), add_zero]
      · change X 1 = X 0/(C+(i.val : ℝ)^2)*(-(i.val : ℝ))+1/(C+(i.val : ℝ)^2)
        field_simp
        nlinarith only [he']
  have hprod (i j : Fin n) : 0 < C-(i.val : ℝ)*(j.val : ℝ) := by
    have hi : (i.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt i.isLt)
    have hj : (j.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt j.isLt)
    have hh := mul_le_mul hi hj (Nat.cast_nonneg j.val) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    dsimp [C]
    nlinarith only [hh]
  have hcast_ne {i j : Fin n} (hij : i ≠ j) : (i.val : ℝ) ≠ (j.val : ℝ) := by
    intro he
    apply hij
    apply Fin.ext
    exact_mod_cast he
  have hdot_ne (i j : Fin n) (hij : i ≠ j) : dot (v j) (d i) ≠ 0 := by
    have he : dot (v j) (d i) = ((j.val : ℝ)-(i.val : ℝ))*(C-(i.val : ℝ)*(j.val : ℝ)) := by
      change (j.val : ℝ)*(C+(i.val : ℝ)^2) + (C+(j.val : ℝ)^2)*(-(i.val : ℝ)) = _
      ring
    rw [he]
    exact mul_ne_zero (sub_ne_zero.mpr (hcast_ne hij).symm) (ne_of_gt (hprod i j))
  have hdir_zero (i : Fin n) (w : Point) (hw : w ∈ (ell i).1.direction) : dot (v i) w = 0 := by
    have hA : A i ∈ ell i := (hell i (A i)).mpr ⟨0, by simp⟩
    have hwa : w+A i ∈ ell i := (ell i).1.vadd_mem_of_mem_direction hw hA
    have h1 := (hell_eq i _).mp hA
    have h2 := (hell_eq i _).mp hwa
    rw [map_add] at h2
    linarith only [h1, h2]
  have hparallel (i j : Fin n) (hij : i ≠ j) : ¬ (ell i).1 ∥ (ell j).1 := by
    intro he
    have heq := (AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot.mp he).1
    have hm : d i ∈ (ell i).1.direction := by
      rw [hell_dir]; exact Submodule.subset_span (Set.mem_singleton _)
    exact hdot_ne i j hij (hdir_zero j (d i) (heq ▸ hm))
  have hell_inj : Function.Injective ell := by
    intro i j he
    by_contra hij
    apply hparallel i j hij
    rw [he]
  let W : Fin n → Fin n → Point := fun i j =>
    !₂[-((i.val : ℝ)+(j.val : ℝ))/(C-(i.val : ℝ)*(j.val : ℝ)),
      1/(C-(i.val : ℝ)*(j.val : ℝ))]
  have heval (i j k : Fin n) : dot (v k) (W i j) =
      1 + (((k.val : ℝ)-(i.val : ℝ))*((k.val : ℝ)-(j.val : ℝ)))/
        (C-(i.val : ℝ)*(j.val : ℝ)) := by
    change (k.val : ℝ)*(-((i.val : ℝ)+(j.val : ℝ))/(C-(i.val : ℝ)*(j.val : ℝ))) +
      (C+(k.val : ℝ)^2)*(1/(C-(i.val : ℝ)*(j.val : ℝ))) = _
    field_simp [ne_of_gt (hprod i j)]
    <;> ring
  have hW_mem (i j k : Fin n) : W i j ∈ ell k ↔ k=i ∨ k=j := by
    rw [hell_eq, heval]
    have hne := ne_of_gt (hprod i j)
    constructor
    · intro he
      have hh : ((k.val : ℝ)-(i.val : ℝ))*((k.val : ℝ)-(j.val : ℝ)) = 0 := by
        have hz : (((k.val : ℝ)-(i.val : ℝ))*((k.val : ℝ)-(j.val : ℝ)))/
            (C-(i.val : ℝ)*(j.val : ℝ)) = 0 := by linarith only [he]
        exact (div_eq_zero_iff).mp hz |>.resolve_right hne
      rcases mul_eq_zero.mp hh with hh | hh
      · left; apply Fin.ext; exact_mod_cast sub_eq_zero.mp hh
      · right; apply Fin.ext; exact_mod_cast sub_eq_zero.mp hh
    · rintro (rfl | rfl) <;> simp
  have hW_unique (i j : Fin n) (hij : i ≠ j) (X : Point)
      (hi : X ∈ ell i) (hj : X ∈ ell j) : X = W i j := by
    have hi' : (i.val : ℝ)*X 0 + (C+(i.val : ℝ)^2)*X 1 = 1 := (hell_eq i X).mp hi
    have hj' : (j.val : ℝ)*X 0 + (C+(j.val : ℝ)^2)*X 1 = 1 := (hell_eq j X).mp hj
    have hh : ((i.val : ℝ)-(j.val : ℝ))*(X 0+((i.val : ℝ)+(j.val : ℝ))*X 1) = 0 := by
      linear_combination hi' - hj'
    have hx : X 0 = -((i.val : ℝ)+(j.val : ℝ))*X 1 := by
      have hh' := (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (hcast_ne hij))
      linarith only [hh']
    have hy : (C-(i.val : ℝ)*(j.val : ℝ))*X 1 = 1 := by
      rw [hx] at hi'
      nlinarith only [hi']
    have hy' : X 1 = 1/(C-(i.val : ℝ)*(j.val : ℝ)) :=
      (eq_div_iff (ne_of_gt (hprod i j))).mpr (by nlinarith only [hy])
    ext k
    fin_cases k
    · change X 0 = -((i.val : ℝ)+(j.val : ℝ))/(C-(i.val : ℝ)*(j.val : ℝ))
      rw [hx, hy']; ring
    · exact hy'
  let L : Set Line := Set.range ell
  have hLcard : L.encard = (n : ENat) := by
    have he : L = ((Finset.univ.image ell : Finset Line) : Set Line) := by
      ext a; simp [L]
    rw [he, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hell_inj]
    simp
  have hLgp : GeneralPosition L := by
    constructor
    · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ hij
      exact hparallel i j (fun he => hij (congrArg ell he))
    · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ c ⟨k, rfl⟩ hij hik hjk
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨⟨hi, hj⟩, hk⟩
      rw [hW_unique i j (fun he => hij (congrArg ell he)) X hi hj] at hk
      rcases (hW_mem i j k).mp hk with he | he
      · exact hik (congrArg ell he.symm)
      · exact hjk (congrArg ell he.symm)
  have havoid : (0 : Point).avoids L := by
    rintro a ⟨i, rfl⟩ he
    have hh := (hell_eq i 0).mp he
    simpa using hh
  have hcross (i j k : Fin n) (hij : i.val < j.val) :
      (∃ Y : Point, Sbtw ℝ 0 Y (W i j) ∧ Y ∈ ell k) ↔
        k.val < i.val ∨ j.val < k.val := by
    rw [normalized_crossing (ell k) 0 (v k) (by intro X; simpa using hell_eq k X), sub_zero, heval]
    have hiff : (0 : ℝ) < ((k.val : ℝ)-(i.val : ℝ))*((k.val : ℝ)-(j.val : ℝ)) ↔
        k.val < i.val ∨ j.val < k.val := by
      rw [mul_pos_iff]
      constructor
      · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
        · right; exact_mod_cast (sub_pos.mp hb)
        · left; exact_mod_cast (sub_neg.mp ha)
      · rintro (hk | hk)
        · right
          constructor
          · exact sub_neg.mpr (by exact_mod_cast hk)
          · exact sub_neg.mpr (by exact_mod_cast (lt_trans hk hij))
        · left
          constructor
          · exact sub_pos.mpr (by exact_mod_cast (lt_trans hij hk))
          · exact sub_pos.mpr (by exact_mod_cast hk)
    rw [← hiff]
    have hh := div_pos_iff_of_pos_right (a := ((k.val : ℝ)-(i.val : ℝ))*((k.val : ℝ)-(j.val : ℝ))) (hprod i j)
    constructor
    · intro he
      exact hh.mp (by linarith only [he])
    · intro he
      have hh' := hh.mpr he
      linarith only [hh']
  have hcount (i j : Fin n) (hij : i.val < j.val) :
      {a ∈ L | ∃ Y : Point, Sbtw ℝ 0 Y (W i j) ∧ Y ∈ a}.encard =
        ((i.val + (n-1-j.val) : ℕ) : ENat) := by
    let K : Finset (Fin n) := Finset.Iio i ∪ Finset.Ioi j
    have hK : Disjoint (Finset.Iio i) (Finset.Ioi j) := by
      apply Finset.disjoint_left.mpr
      intro k hk hk'
      have ha : k < i := Finset.mem_Iio.mp hk
      have hb : j < k := Finset.mem_Ioi.mp hk'
      have hc : i < j := hij
      exact (lt_irrefl k) (lt_trans ha (lt_trans hc hb))
    have he : {a ∈ L | ∃ Y : Point, Sbtw ℝ 0 Y (W i j) ∧ Y ∈ a} =
        ((K.image ell : Finset Line) : Set Line) := by
      ext a
      constructor
      · rintro ⟨⟨k, rfl⟩, hk⟩
        apply Finset.mem_image.mpr
        refine ⟨k, ?_, rfl⟩
        simpa [K] using (hcross i j k hij).mp hk
      · intro ha
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
        refine ⟨⟨k, rfl⟩, (hcross i j k hij).mpr ?_⟩
        simpa [K] using hk
    rw [he, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hell_inj]
    dsimp [K]
    rw [Finset.card_union_of_disjoint hK]
    simp
  have hred (i j : Fin n) (hij : i.val < j.val) :
      W i j ∈ redPoints L p 0 ↔ i.val+(n-1-j.val) ≤ p := by
    change {a ∈ L | ∃ Y : Point, Sbtw ℝ 0 Y (W i j) ∧ Y ∈ a}.encard ≤ (p : ENat) ↔ _
    rw [hcount i j hij]
    exact_mod_cast (Iff.rfl : i.val+(n-1-j.val) ≤ p ↔ i.val+(n-1-j.val) ≤ p)
  let P : Set (Fin n × Fin n) := {ij | ij.1.val < ij.2.val ∧ ij.1.val+(n-1-ij.2.val) ≤ p}
  let f : Fin n × Fin n → Point := fun ij => W ij.1 ij.2
  have hf : Set.InjOn f P := by
    intro x hx y hy he
    have h1 : x.1 = y.1 ∨ x.1 = y.2 := by
      apply (hW_mem y.1 y.2 x.1).mp
      change f y ∈ ell x.1
      rw [← he]
      exact (hW_mem x.1 x.2 x.1).mpr (Or.inl rfl)
    have h2 : x.2 = y.1 ∨ x.2 = y.2 := by
      apply (hW_mem y.1 y.2 x.2).mp
      change f y ∈ ell x.2
      rw [← he]
      exact (hW_mem x.1 x.2 x.2).mpr (Or.inr rfl)
    have h1' : x.1.val = y.1.val ∨ x.1.val = y.2.val := h1.imp (congrArg Fin.val) (congrArg Fin.val)
    have h2' : x.2.val = y.1.val ∨ x.2.val = y.2.val := h2.imp (congrArg Fin.val) (congrArg Fin.val)
    have hx' : x.1.val < x.2.val := hx.1
    have hy' : y.1.val < y.2.val := hy.1
    apply Prod.ext <;> apply Fin.ext <;> omega
  have himage : f '' P = intersections L ∩ redPoints L p 0 := by
    ext X
    constructor
    · rintro ⟨⟨i,j⟩, hij, rfl⟩
      refine ⟨?_, (hred i j hij.1).mpr hij.2⟩
      refine ⟨ell i, ⟨i, rfl⟩, ell j, ⟨j, rfl⟩, ?_, ?_, ?_⟩
      · intro he
        have he' := hell_inj he
        have hh : i.val < j.val := hij.1
        exact (ne_of_lt hh) (congrArg Fin.val he')
      · exact (hW_mem i j i).mpr (Or.inl rfl)
      · exact (hW_mem i j j).mpr (Or.inr rfl)
    · rintro ⟨⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, hij, hi, hj⟩, hr⟩
      have hne : i ≠ j := fun he => hij (congrArg ell he)
      rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with hij' | hji'
      · have he := hW_unique i j hne X hi hj
        refine ⟨(i,j), ⟨hij', ?_⟩, he.symm⟩
        exact (hred i j hij').mp (he ▸ hr)
      · have he := hW_unique j i hne.symm X hj hi
        refine ⟨(j,i), ⟨hji', ?_⟩, he.symm⟩
        exact (hred j i hji').mp (he ▸ hr)
  refine ⟨L, hLcard, hLgp, 0, havoid, ?_⟩
  rw [← himage, hf.encard_image]
  exact LeanFlow.PBBasic029.pair_count p n le

