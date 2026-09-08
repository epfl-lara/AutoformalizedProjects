import Mathlib

theorem LeanFlowPB002.lift_mutual_reachability {V : Type*} (R : V → V → Prop)
    (P : ℕ) (hP : 0 < P) :
  let F : Set V → Set V := fun A => {y : V | ∃ x ∈ A, R x y}
  let G : Set (V × Fin P) → Set (V × Fin P) :=
    fun A => {q : V × Fin P | ∃ p ∈ A,
      R p.1 q.1 ∧ q.2.val = (p.2.val + 1) % P}
  ∀ (v w : V) (r : Fin P),
    (∃ a : ℕ, w ∈ F^[a] ({v} : Set V)) →
    (∃ b : ℕ, v ∈ F^[b] ({w} : Set V)) →
    ∃ s : Fin P,
      (∃ a : ℕ, (w, s) ∈ G^[a] ({(v, r)} : Set (V × Fin P))) ∧
      (∃ b : ℕ, (v, r) ∈ G^[b] ({(w, s)} : Set (V × Fin P))) := by 
  dsimp only
  let F : Set V → Set V := fun A => {y | ∃ x ∈ A, R x y}
  let G : Set (V × Fin P) → Set (V × Fin P) := fun A =>
    {q | ∃ p ∈ A, R p.1 q.1 ∧ q.2.val = (p.2.val + 1) % P}
  change ∀ v w r, (∃ a, w ∈ F^[a] {v}) → (∃ b, v ∈ F^[b] {w}) →
    ∃ s, (∃ a, (w,s) ∈ G^[a] {(v,r)}) ∧ (∃ b, (v,r) ∈ G^[b] {(w,s)})
  have cat : ∀ (n m : ℕ) (x y z : V), y ∈ F^[n] {x} →
      z ∈ F^[m] {y} → z ∈ F^[n+m] {x} := by
    intro n m
    induction m with
    | zero =>
      intro x y z h hz
      simp only [Function.iterate_zero, id_eq, Set.mem_singleton_iff] at hz
      subst z
      simpa using h
    | succ m ih =>
      intro x y z h hz
      rw [Function.iterate_succ_apply'] at hz
      obtain ⟨u, hu, huz⟩ := hz
      rw [Nat.add_succ, Function.iterate_succ_apply']
      exact ⟨u, ih x y u h hu, huz⟩
  have lift : ∀ (n : ℕ) (x y : V) (r : Fin P), y ∈ F^[n] {x} →
      (y, (⟨(r.val+n)%P, Nat.mod_lt _ hP⟩ : Fin P)) ∈ G^[n] {(x,r)} := by
    intro n
    induction n with
    | zero =>
      intro x y r h
      simp only [Function.iterate_zero, id_eq, Set.mem_singleton_iff] at h
      subst y
      simp only [Function.iterate_zero, id_eq, Set.mem_singleton_iff, Prod.mk.injEq, true_and, Nat.add_zero]
      apply Fin.ext
      exact Nat.mod_eq_of_lt r.isLt
    | succ n ih =>
      intro x y r h
      rw [Function.iterate_succ_apply'] at h
      obtain ⟨z, hz, hzy⟩ := h
      rw [Function.iterate_succ_apply']
      refine ⟨(z, (⟨(r.val+n)%P, Nat.mod_lt _ hP⟩ : Fin P)), ih x z r hz, hzy, ?_⟩
      dsimp
      rw [Nat.mod_add_mod]
      rw [Nat.add_assoc]
  intro v w r ha hb
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have loop := cat a b v w v ha hb
  have loops : ∀ k : ℕ, v ∈ F^[k*(a+b)] {v} := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul]
      exact cat _ _ v v v ih loop
  let s : Fin P := ⟨(r.val+a)%P, Nat.mod_lt _ hP⟩
  refine ⟨s, ⟨a, lift a v w r ha⟩, ?_⟩
  let d := b + (P-1)*(a+b)
  have ret : v ∈ F^[d] {w} := cat _ _ w v v hb (loops (P-1))
  have eqr : (⟨(s.val+d)%P, Nat.mod_lt _ hP⟩ : Fin P) = r := by
    apply Fin.ext
    dsimp [s, d]
    rw [Nat.mod_add_mod]
    have he : r.val + a + (b + (P-1)*(a+b)) = r.val + P*(a+b) := by
      have hp : P = (P-1)+1 := by omega
      have hm := congrArg (fun t : ℕ => t * (a+b)) hp
      nlinarith
    rw [he]
    simp [Nat.mod_eq_of_lt r.isLt]
  refine ⟨d, ?_⟩
  simpa only [eqr] using lift d w v s ret

