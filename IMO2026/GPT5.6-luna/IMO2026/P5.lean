import Mathlib

/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

namespace IMO2026P5

notation "ℝ+" => Set.Ioi (0 : ℝ)

/-- The answer to be determined. -/
def answer : Set (ℝ+ → ℝ+) :=
  {f | ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ+, (f x : ℝ) = (x : ℝ) + c}

private theorem affine_mem (f : ℝ+ → ℝ+) {c : ℝ} (hc : 0 ≤ c)
    (hfc : ∀ x : ℝ+, (f x : ℝ) = (x : ℝ) + c) :
    ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2 := by
  intro x y
  have hx : (0 : ℝ) < (x : ℝ) := x.property
  have hy : (0 : ℝ) < (y : ℝ) := y.property
  constructor
  · rw [hfc x, hfc y]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg ((x : ℝ) - (y : ℝ) - c)]
  · rw [hfc x, hfc y]
    apply (Real.sqrt_le_iff).2
    constructor
    · nlinarith
    · nlinarith [sq_nonneg ((x : ℝ) - (y : ℝ) - c)]

private theorem comp_of_mem (f : ℝ+ → ℝ+) (hf : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
    √(x * f y) ≤ (f x + y) / 2) (y : ℝ+) :
    (f (f y) : ℝ) + (y : ℝ) = 2 * (f y : ℝ) := by
  have h := hf (f y) y
  have hsq1 : Real.sqrt (((f y : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) = (f y : ℝ) := by
    rw [show ((f y : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2 = (f y : ℝ) ^ 2 by ring]
    exact Real.sqrt_sq (le_of_lt (f y).property)
  have hsq2 : Real.sqrt ((f y : ℝ) * (f y : ℝ)) = (f y : ℝ) := by
    rw [← pow_two]
    exact Real.sqrt_sq (le_of_lt (f y).property)
  rw [hsq1, hsq2] at h
  nlinarith [h.1, h.2]

private theorem self_ge (f : ℝ+ → ℝ+) (z : ℝ+)
    (hcomp : ∀ w : ℝ+, (f (f w) : ℝ) + (w : ℝ) = 2 * (f w : ℝ)) :
    (z : ℝ) ≤ (f z : ℝ) := by
  by_contra hnot
  have hz : (f z : ℝ) < (z : ℝ) := lt_of_not_ge hnot
  let u : ℕ → ℝ+ := fun n => Nat.rec z (fun (_ : ℕ) (w : ℝ+) => f w) n
  have hu : ∀ n : ℕ, (u n).1 = (z : ℝ) + (n : ℝ) * ((f z : ℝ) - (z : ℝ)) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [u]
    | one => simp [u]
    | more n hn hn1 =>
      have h : (u (n + 2)).1 + (u n).1 = 2 * (u (n + 1)).1 := by
        change (f (f (u n))).1 + (u n).1 = 2 * (f (u n)).1
        exact hcomp _
      norm_num [Nat.cast_add, Nat.cast_one] at hn hn1 h ⊢
      nlinarith [hn, hn1, h]
  have hd : 0 < (z : ℝ) - (f z : ℝ) := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((z : ℝ) / ((z : ℝ) - (f z : ℝ)))
  have hn' : (z : ℝ) < (n : ℝ) * ((z : ℝ) - (f z : ℝ)) :=
    (div_lt_iff₀ hd).mp hn
  have hu_pos : 0 < (u n).1 := (u n).property
  have hu_formula := hu n
  norm_num [Nat.cast_add, Nat.cast_one] at hu_formula
  nlinarith [hu_formula, hn', hu_pos]

private lemma floor_bounds (a : ℝ) (ha : 0 ≤ a) :
    (Nat.floor a : ℝ) ≤ a ∧ a < (Nat.floor a : ℝ) + 1 := by
  exact ⟨Nat.floor_le ha, Nat.lt_floor_add_one a⟩

private lemma orbit_formula (f : ℝ+ → ℝ+) (y : ℝ+)
    (hcomp : ∀ w : ℝ+, (f (f w) : ℝ) + (w : ℝ) = 2 * (f w : ℝ)) :
    ∀ n : ℕ, ((f^[n]) y : ℝ) = (y : ℝ) + (n : ℝ) * ((f y : ℝ) - (y : ℝ)) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hn1 =>
      have h : ((f^[n + 2]) y : ℝ) + ((f^[n]) y : ℝ) =
          2 * ((f^[n + 1]) y : ℝ) := by
        simpa [Function.iterate_succ_apply'] using hcomp ((f^[n]) y)
      norm_num [Nat.cast_add, Nat.cast_one] at hn hn1 h ⊢
      nlinarith [hn, hn1, h]

private lemma orbit_pair_ineq (f : ℝ+ → ℝ+)
    (hf : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2)
    (hcomp : ∀ w : ℝ+, (f (f w) : ℝ) + (w : ℝ) = 2 * (f w : ℝ))
    (x y : ℝ+) (n m : ℕ) :
    (((f^[n]) x : ℝ) + ((f^[m]) y : ℝ) + ((f x : ℝ) - (x : ℝ))) ^ 2 ≤
      2 * ((((f^[n]) x : ℝ) ^ 2) +
        (((f^[m]) y : ℝ) + ((f y : ℝ) - (y : ℝ))) ^ 2) := by
  have h := (hf ((f^[n]) x) ((f^[m]) y)).1
  have hnonneg : 0 ≤ (((f^[n]) x : ℝ) ^ 2 + ((f ((f^[m]) y)) : ℝ) ^ 2) / 2 := by
    nlinarith [sq_nonneg ((f^[n]) x : ℝ), sq_nonneg (f ((f^[m]) y) : ℝ)]
  have hfxpos : (0 : ℝ) < (f ((f^[n]) x) : ℝ) := (f ((f^[n]) x)).property
  have hmpos : (0 : ℝ) < ((f^[m]) y : ℝ) := ((f^[m]) y).property
  have hleft : 0 ≤ (((f ((f^[n]) x)) : ℝ) + ((f^[m]) y : ℝ)) / 2 := by
    nlinarith
  have hsquare := ((Real.le_sqrt hleft) hnonneg).mp h
  have hsq : (((f ((f^[n]) x)) : ℝ) + ((f^[m]) y)) ^ 2 ≤
      2 * (((f^[n]) x : ℝ) ^ 2 + ((f ((f^[m]) y)) : ℝ) ^ 2) := by
    nlinarith [hsquare]
  have hfx : (f ((f^[n]) x) : ℝ) = ((f^[n+1]) x : ℝ) := by
    simp [Function.iterate_succ_apply']
  have hfy : (f ((f^[m]) y) : ℝ) = ((f^[m+1]) y : ℝ) := by
    simp [Function.iterate_succ_apply']
  have hx := orbit_formula f x hcomp n
  have hx1 := orbit_formula f x hcomp (n + 1)
  have hy := orbit_formula f y hcomp m
  have hy1 := orbit_formula f y hcomp (m + 1)
  rw [hfx, hfy] at hsq
  rw [hx, hx1, hy, hy1] at hsq
  rw [hx, hy] at ⊢
  norm_num [Nat.cast_add, Nat.cast_one] at hsq ⊢
  nlinarith

private lemma positive_difference_le (f : ℝ+ → ℝ+)
    (hf : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2)
    (hcomp : ∀ w : ℝ+, (f (f w) : ℝ) + (w : ℝ) = 2 * (f w : ℝ))
    (hge : ∀ z : ℝ+, (z : ℝ) ≤ (f z))
    (x y : ℝ+) (hq : 0 < (f y : ℝ) - (y : ℝ)) :
    (f x : ℝ) - (x : ℝ) ≤ (f y : ℝ) - (y : ℝ) := by
  have hp : 0 ≤ (f x : ℝ) - (x : ℝ) := by
    exact sub_nonneg.mpr (hge x)
  have hq0 : 0 ≤ (f y : ℝ) - (y : ℝ) := le_of_lt hq
  by_contra hnot
  have hpgt : (f y : ℝ) - (y : ℝ) < (f x : ℝ) - (x : ℝ) := by
    linarith
  let p : ℝ := (f x : ℝ) - (x : ℝ)
  let q : ℝ := (f y : ℝ) - (y : ℝ)
  have hp' : 0 < p := by dsimp [p]; linarith
  have hq' : 0 < q := by dsimp [q]; exact hq
  have hpq : 0 < p - q := by dsimp [p, q]; linarith
  let M : ℝ := max (((x : ℝ) - (y : ℝ)) / q)
      ((p ^ 2 + q ^ 2) / (2 * q * (p - q)))
  obtain ⟨m, hm⟩ := exists_nat_gt M
  have hm1 : ((x : ℝ) - (y : ℝ)) / q < (m : ℝ) := by
    exact lt_of_le_of_lt (le_max_left _ _) hm
  have hden : 0 < 2 * q * (p - q) := by positivity
  have hm2 : (p ^ 2 + q ^ 2) / (2 * q * (p - q)) < (m : ℝ) := by
    exact lt_of_le_of_lt (le_max_right _ _) hm
  have hm2' : p ^ 2 + q ^ 2 < 2 * q * (p - q) * (m : ℝ) := by
    have ht := (div_lt_iff₀ hden).mp hm2
    nlinarith only [ht]
  have hYm : (x : ℝ) ≤ (y : ℝ) + (m : ℝ) * q := by
    have := (div_lt_iff₀ hq').mp hm1
    linarith
  have hypos : (0 : ℝ) < (y : ℝ) := y.property
  have hyterm : 0 < 4 * (p - q) * (y : ℝ) := by
    exact mul_pos (mul_pos (by norm_num) hpq) hypos
  have hlarge : 2 * (p ^ 2 + q ^ 2) < 4 * (p - q) * ((y : ℝ) + (m : ℝ) * q) := by
    nlinarith only [hm2', hyterm]
  let n : ℕ := Nat.floor (((y : ℝ) + (m : ℝ) * q - (x : ℝ)) / p)
  have harg : 0 ≤ ((y : ℝ) + (m : ℝ) * q - (x : ℝ)) / p := by
    exact div_nonneg (by linarith) (le_of_lt hp')
  have hn := floor_bounds (((y : ℝ) + (m : ℝ) * q - (x : ℝ)) / p) harg
  have hn0 : (n : ℝ) * p ≤ (y : ℝ) + (m : ℝ) * q - (x : ℝ) := by
    dsimp [n]
    exact (le_div_iff₀ hp').mp hn.1
  have hn1 : (y : ℝ) + (m : ℝ) * q - (x : ℝ) < ((n : ℝ) + 1) * p := by
    dsimp [n]
    exact (div_lt_iff₀ hp').mp hn.2
  have hXY0 : 0 ≤ (y : ℝ) + (m : ℝ) * q - ((x : ℝ) + (n : ℝ) * p) := by
    linarith
  have hXY1 : (y : ℝ) + (m : ℝ) * q - ((x : ℝ) + (n : ℝ) * p) < p := by
    linarith
  have hpair := orbit_pair_ineq f hf hcomp x y n m
  have hE : 0 ≤
      (((x : ℝ) + (n : ℝ) * p) - ((y : ℝ) + (m : ℝ) * q)) ^ 2
        - 2 * p * ((x : ℝ) + (n : ℝ) * p)
        + (4 * q - 2 * p) * ((y : ℝ) + (m : ℝ) * q)
        + 2 * q ^ 2 - p ^ 2 := by
    have hxn := orbit_formula f x hcomp n
    have hym := orbit_formula f y hcomp m
    dsimp [p, q] at hpair ⊢
    rw [hxn, hym] at hpair
    nlinarith only [hpair]
  have hDsq :
      (((y : ℝ) + (m : ℝ) * q) - ((x : ℝ) + (n : ℝ) * p)) ^ 2 < p ^ 2 := by
    nlinarith only [hXY0, hXY1, hp',
      sq_nonneg (p - (((y : ℝ) + (m : ℝ) * q) -
        ((x : ℝ) + (n : ℝ) * p)))]
  have hmul := mul_lt_mul_of_pos_left hXY1 hp'
  have hDp : 2 * p * (((y : ℝ) + (m : ℝ) * q) -
      ((x : ℝ) + (n : ℝ) * p)) < 2 * p ^ 2 := by
    nlinarith only [hmul]
  have hupper :
      (((x : ℝ) + (n : ℝ) * p) - ((y : ℝ) + (m : ℝ) * q)) ^ 2
        - 2 * p * ((x : ℝ) + (n : ℝ) * p)
        + (4 * q - 2 * p) * ((y : ℝ) + (m : ℝ) * q)
        + 2 * q ^ 2 - p ^ 2 <
      2 * (p ^ 2 + q ^ 2) - 4 * (p - q) * ((y : ℝ) + (m : ℝ) * q) := by
    nlinarith only [hDsq, hDp]
  nlinarith

private lemma fixed_point_pair_separation (f : ℝ+ → ℝ+)
    (hf : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2)
    {a b : ℝ+} (hda : 0 < (f a : ℝ) - (a : ℝ))
    (hdb : (f b : ℝ) - (b : ℝ) = 0) :
    ((a : ℝ) - (b : ℝ)) ^ 2 > ((f a : ℝ) - (a : ℝ)) ^ 2 := by
  have h := (hf a b).1
  have hfb : (f b : ℝ) = (b : ℝ) := by linarith
  rw [hfb] at h
  have hnonneg : 0 ≤ ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / 2 := by
    nlinarith [sq_nonneg (a : ℝ), sq_nonneg (b : ℝ)]
  have hleft : 0 ≤ ((f a : ℝ) + (b : ℝ)) / 2 := by
    have hfa : (0 : ℝ) < (f a : ℝ) := (f a).property
    have hb : (0 : ℝ) < (b : ℝ) := b.property
    nlinarith
  have hsquare := ((Real.le_sqrt hleft) hnonneg).mp h
  have ha : (0 : ℝ) < (a : ℝ) := a.property
  have hb : (0 : ℝ) < (b : ℝ) := b.property
  nlinarith

private lemma increment_eq_of_close (f : ℝ+ → ℝ+)
    (hf : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2)
    {p : ℝ} (hp : 0 < p) {a b : ℝ+}
    (ha : (f a : ℝ) - (a : ℝ) = 0 ∨ (f a : ℝ) - (a : ℝ) = p)
    (hb : (f b : ℝ) - (b : ℝ) = 0 ∨ (f b : ℝ) - (b : ℝ) = p)
    (hab : ((a : ℝ) - (b : ℝ)) ^ 2 < p ^ 2) :
    (f a : ℝ) - (a : ℝ) = (f b : ℝ) - (b : ℝ) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · linarith
  · have hs := fixed_point_pair_separation f hf (a := b) (b := a) (by
      rw [hb]
      exact hp) ha
    nlinarith
  · have hs := fixed_point_pair_separation f hf (a := a) (b := b) (by
      rw [ha]
      exact hp) hb
    nlinarith
  · linarith

private lemma no_positive_with_fixed (f : ℝ+ → ℝ+)
    (hf : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2)
    (hcomp : ∀ w : ℝ+, (f (f w) : ℝ) + (w : ℝ) = 2 * (f w : ℝ))
    (hge : ∀ z : ℝ+, (z : ℝ) ≤ (f z))
    (x y : ℝ+) (hp : 0 < (f x : ℝ) - (x : ℝ))
    (hy : (f y : ℝ) - (y : ℝ) = 0) : False := by
  let p : ℝ := (f x : ℝ) - (x : ℝ)
  have hp' : 0 < p := by
    dsimp [p]
    exact hp
  have hstate : ∀ z : ℝ+, (f z : ℝ) - (z : ℝ) = 0 ∨
      (f z : ℝ) - (z : ℝ) = p := by
    intro z
    have hznonneg : 0 ≤ (f z : ℝ) - (z : ℝ) :=
      sub_nonneg.mpr (hge z)
    by_cases hz0 : (f z : ℝ) - (z : ℝ) = 0
    · exact Or.inl hz0
    · right
      have hzpos : 0 < (f z : ℝ) - (z : ℝ) :=
        lt_of_le_of_ne hznonneg (Ne.symm hz0)
      have hzx := positive_difference_le f hf hcomp hge x z hzpos
      have hxx := positive_difference_le f hf hcomp hge z x hp
      dsimp [p]
      linarith
  have hchain_eq : ∀ a b : ℝ+, (a : ℝ) ≤ (b : ℝ) →
      (f a : ℝ) - (a : ℝ) = (f b : ℝ) - (b : ℝ) := by
    intro a b hab
    obtain ⟨N, hN⟩ := exists_nat_gt
      (((b : ℝ) - (a : ℝ)) / p)
    have hratio : 0 ≤ ((b : ℝ) - (a : ℝ)) / p := by
      exact div_nonneg (by linarith) (le_of_lt hp')
    have hNpos : 0 < (N : ℝ) := by
      nlinarith
    have hNmul : (b : ℝ) - (a : ℝ) < (N : ℝ) * p := by
      have ht := (div_lt_iff₀ hp').mp hN
      nlinarith
    let delta : ℝ := ((b : ℝ) - (a : ℝ)) / (N : ℝ)
    have hdelta : 0 ≤ delta := by
      dsimp [delta]
      exact div_nonneg (by linarith) (le_of_lt hNpos)
    have hdeltalt : delta < p := by
      dsimp [delta]
      apply (div_lt_iff₀ hNpos).2
      nlinarith [hNmul]
    let z : ℕ → ℝ+ := fun k =>
      ⟨(a : ℝ) + (k : ℝ) * delta, by
        have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        have hmul : 0 ≤ (k : ℝ) * delta := mul_nonneg hk hdelta
        exact add_pos_of_pos_of_nonneg a.property hmul⟩
    have hzstep (k : ℕ) :
        (z (k + 1) : ℝ) - (z k : ℝ) = delta := by
      dsimp [z]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    have hzclose (k : ℕ) :
        ((z k : ℝ) - (z (k + 1) : ℝ)) ^ 2 < p ^ 2 := by
      have hsum : 0 < p + delta := by nlinarith
      have hprod : 0 < (p - delta) * (p + delta) :=
        mul_pos (sub_pos.mpr hdeltalt) hsum
      have hsq : delta ^ 2 < p ^ 2 := by nlinarith [hprod]
      nlinarith [hzstep k, hsq]
    have hzsame (k : ℕ) (hk : k < N) :
        (f (z k) : ℝ) - (z k : ℝ) =
          (f (z (k + 1)) : ℝ) - (z (k + 1) : ℝ) := by
      exact increment_eq_of_close f hf hp' (hstate (z k))
        (hstate (z (k + 1))) (hzclose k)
    have hconst : ∀ k : ℕ, k ≤ N →
        (f (z k) : ℝ) - (z k : ℝ) =
          (f (z 0) : ℝ) - (z 0 : ℝ) := by
      intro k
      induction k with
      | zero => intro; rfl
      | succ k ih =>
          intro hk
          calc
            (f (z (k + 1)) : ℝ) - (z (k + 1) : ℝ) =
                (f (z k) : ℝ) - (z k : ℝ) :=
              (hzsame k (Nat.lt_of_succ_le hk)).symm
            _ = (f (z 0) : ℝ) - (z 0 : ℝ) :=
              ih (Nat.le_trans (Nat.le_succ k) hk)
    have hz0 : z 0 = a := by
      apply Subtype.ext
      dsimp [z]
      norm_num
    have hzN : z N = b := by
      apply Subtype.ext
      dsimp [z, delta]
      field_simp
      ring
    have hc := hconst N (le_refl N)
    rw [hzN, hz0] at hc
    exact hc.symm
  have hxy : (x : ℝ) ≤ (y : ℝ) ∨ (y : ℝ) ≤ (x : ℝ) :=
    le_total (x : ℝ) (y : ℝ)
  rcases hxy with hxy | hyx
  · have hc := hchain_eq x y hxy
    linarith [hc, hp, hy]
  · have hc := hchain_eq y x hyx
    linarith [hc, hp, hy]

private lemma difference_le (f : ℝ+ → ℝ+)
    (hf : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2)
    (hcomp : ∀ w : ℝ+, (f (f w) : ℝ) + (w : ℝ) = 2 * (f w : ℝ))
    (hge : ∀ z : ℝ+, (z : ℝ) ≤ (f z : ℝ))
    (x y : ℝ+) :
    (f x : ℝ) - (x : ℝ) ≤ (f y : ℝ) - (y : ℝ) := by
  by_cases hq : 0 < (f y : ℝ) - (y : ℝ)
  · exact positive_difference_le f hf hcomp hge x y hq
  · have hy_nonneg : 0 ≤ (f y : ℝ) - (y : ℝ) :=
      sub_nonneg.mpr (hge y)
    have hy_zero : (f y : ℝ) - (y : ℝ) = 0 := by
      linarith
    by_contra hnot
    have hx_pos : 0 < (f x : ℝ) - (x : ℝ) := by
      have hlt := lt_of_not_ge hnot
      linarith
    exact (no_positive_with_fixed f hf hcomp hge x y hx_pos hy_zero).elim

private lemma constant_difference (f : ℝ+ → ℝ+)
    (hf : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2)
    (hcomp : ∀ w : ℝ+, (f (f w) : ℝ) + (w : ℝ) = 2 * (f w : ℝ))
    (hge : ∀ z : ℝ+, (z : ℝ) ≤ (f z : ℝ))
    (x y : ℝ+) :
    (f x : ℝ) - (x : ℝ) = (f y : ℝ) - (y : ℝ) := by
  have hxy := difference_le f hf hcomp hge x y
  have hyx := difference_le f hf hcomp hge y x
  linarith

private lemma affine_witness (f : ℝ+ → ℝ+)
    (hf : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ+, (f x : ℝ) = (x : ℝ) + c := by
  have hcomp : ∀ w : ℝ+, (f (f w) : ℝ) + (w : ℝ) = 2 * (f w : ℝ) := by
    intro w
    exact comp_of_mem f hf w
  have hge : ∀ z : ℝ+, (z : ℝ) ≤ (f z) := by
    intro z
    exact self_ge f z hcomp
  let u : ℝ+ := ⟨1, by norm_num⟩
  let c : ℝ := (f u : ℝ) - (u : ℝ)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact sub_nonneg.mpr (hge u)
  refine ⟨c, hc, ?_⟩
  intro x
  have hconst := constant_difference f hf hcomp hge x u
  dsimp [c]
  linarith

private lemma predicate_iff_affine (f : ℝ+ → ℝ+) :
    (∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2) ↔
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ+, (f x : ℝ) = (x : ℝ) + c := by
  constructor
  · exact affine_witness f
  · rintro ⟨c, hc, hfc⟩
    exact affine_mem f hc hfc

theorem result : {f : ℝ+ → ℝ+ | ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
    √(x * f y) ≤ (f x + y) / 2} = answer := by
  ext f
  constructor
  · intro hf
    change ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2 at hf
    change ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ+, (f x : ℝ) = (x : ℝ) + c
    exact (predicate_iff_affine f).mp hf
  · intro hf
    change ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ+, (f x : ℝ) = (x : ℝ) + c at hf
    rcases hf with ⟨c, hc, hfc⟩
    change ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2
    exact affine_mem f hc hfc

end IMO2026P5
