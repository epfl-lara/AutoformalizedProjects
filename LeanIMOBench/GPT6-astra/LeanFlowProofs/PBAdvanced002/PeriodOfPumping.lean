import Mathlib

theorem LeanFlowPB002.period_of_pumping {V : Type*} (R : V → V → Prop)
    (T P : ℕ) (hP : 0 < P) :
  let F : Set V → Set V := fun A => {y : V | ∃ x ∈ A, R x y}
  (∀ (k : ℕ) (x y : V), T ≤ k → y ∈ F^[k] ({x} : Set V) →
    ∃ h : ℕ, h < T ∧ h % P = k % P ∧
      (∀ j : ℕ, y ∈ F^[h + j * P] ({x} : Set V))) →
  ∀ (A : Set V) (k : ℕ), T ≤ k → F^[k + P] A = F^[k] A := by 
  dsimp only
  intro hpump
  let F : Set V → Set V := fun A => {y : V | ∃ x ∈ A, R x y}
  have hmem : ∀ (n : ℕ) (A : Set V) (y : V),
      y ∈ F^[n] A ↔ ∃ x ∈ A, y ∈ F^[n] ({x} : Set V) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro A y
      simp only [Function.iterate_succ_apply']
      change (∃ z ∈ F^[n] A, R z y) ↔
        ∃ x ∈ A, ∃ z ∈ F^[n] ({x} : Set V), R z y
      constructor
      · rintro ⟨z, hz, hzy⟩
        obtain ⟨x, hx, hxz⟩ := (ih A z).mp hz
        exact ⟨x, hx, z, hxz, hzy⟩
      · rintro ⟨x, hx, z, hxz, hzy⟩
        exact ⟨z, (ih A z).mpr ⟨x, hx, hxz⟩, hzy⟩
  have harith : ∀ h n : ℕ, h ≤ n → h % P = n % P →
      ∃ j : ℕ, h + j * P = n := by
    intro h n hle hmod
    refine ⟨n / P - h / P, ?_⟩
    have hn := Nat.mod_add_div n P
    have hh := Nat.mod_add_div h P
    rw [Nat.sub_mul]
    rw [Nat.mul_comm P (n / P)] at hn
    rw [Nat.mul_comm P (h / P)] at hh
    omega
  intro A k hk
  apply Set.ext
  intro y
  rw [hmem, hmem]
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨h, ht, hm, hall⟩ := hpump (k + P) x y (by omega) hxy
    obtain ⟨j, hj⟩ := harith h k (by omega) (by simpa using hm)
    exact ⟨x, hx, by simpa only [hj] using hall j⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨h, ht, hm, hall⟩ := hpump k x y hk hxy
    obtain ⟨j, hj⟩ := harith h (k + P) (by omega) (by simpa using hm)
    exact ⟨x, hx, by simpa only [hj] using hall j⟩
