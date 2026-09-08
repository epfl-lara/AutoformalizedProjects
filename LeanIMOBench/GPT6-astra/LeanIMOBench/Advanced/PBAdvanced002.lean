import LeanFlowProofs.PB002CycleWitnesses
import LeanFlowProofs.PB002EventualPeriodConfigurationBound
import LeanFlowProofs.PB002LongIteratePumpable
import LeanFlowProofs.PB002PeriodOfPumping
import LeanFlowProofs.PB002SmallCommonMultiple120
import Mathlib

/--
  M(f) is the maximum possible number of distinct subsets A_1, ..., A_t
  such that any pair has a lovely relationship, where f is derived from the love relation L on S.
  This definition is made robust by taking S and L as explicit parameters,
  and defining all intermediate concepts (f, LovelyRelationship, Configuration) locally.
-/
noncomputable
def M_func (S : Type) [Fintype S] (L : S → S → Prop) : ℕ :=
  -- 1. Define f: The function that maps a set X to the set of students loved by someone in X.
  let f : Set S → Set S := fun X => {y : S | ∃ x ∈ X, L x y}

  -- 2. Define Lovely Relationship (reachability)
  let LovelyRelationship (A B : Set S) : Prop := ∃ k : ℕ, f^[k] A = B

  -- 3. Define Mutually Lovely Relationship (symmetric reachability)
  let MutuallyLovelyRelationship (A B : Set S) : Prop :=
    LovelyRelationship A B ∨ LovelyRelationship B A

  -- 4. Type for indexed collection of subsets
  let Configuration (t : ℕ) := Fin t → Set S

  -- 5. Define the predicate for a Lovely Configuration
  let IsLovelyConfiguration (t : ℕ) (A : Configuration t) : Prop :=
    -- Distinctness condition
    (∀ i j : Fin t, i ≠ j → A i ≠ A j) ∧
    -- Mutually related condition
    (∀ i j : Fin t, i ≠ j → MutuallyLovelyRelationship (A i) (A j))

  -- 6. M is the supremum of possible sizes t
  sSup {t : ℕ | ∃ (A : Configuration t), IsLovelyConfiguration t A}

-- The main claim: M(f) <= 2^70 when the number of students is 120.
theorem PBAdvanced002 {S : Type} [Fintype S] {L : S → S → Prop} (h_card : Fintype.card S = 120) :
  M_func S L ≤ 2^70 := by classical
  obtain ⟨m, w, c, hc, hsum, hcover⟩ := LeanFlowPB002.cycle_witnesses L
  obtain ⟨P, hP, hdvd, hbound⟩ := LeanFlowPB002.small_common_multiple_120 m c
    (fun i => (hc i).1) (by simpa [h_card] using hsum)
  let F : Set S → Set S := fun A => {y : S | ∃ x ∈ A, L x y}
  let T := 2 * Fintype.card S * P
  have hlarge : Fintype.card S ≤ T := by
    dsimp [T]
    rw [h_card]
    omega
  have hpump : ∀ (k : ℕ) (x y : S), T ≤ k → y ∈ F^[k] ({x} : Set S) →
      ∃ h : ℕ, h < T ∧ h % P = k % P ∧
        (∀ j : ℕ, y ∈ F^[h + j * P] ({x} : Set S)) := by
    intro k x y hk hy
    exact LeanFlowPB002.long_iterate_pumpable L P hP m w c hc hdvd hcover
      k x y (hlarge.trans hk) hy
  have hperiod : ∀ (A : Set S) (k : ℕ), T ≤ k → F^[k + P] A = F^[k] A :=
    LeanFlowPB002.period_of_pumping L T P hP hpump
  have hnum : T + P ≤ 2^70 := by
    dsimp [T]
    rw [h_card]
    norm_num at hbound ⊢
    omega
  unfold M_func
  apply csSup_le
  · exact ⟨0, (fun i => Fin.elim0 i), (by simp), (by simp)⟩
  · rintro t ⟨A, hdist, hcomp⟩
    have hinj : Function.Injective A := by
      intro i j hij
      by_contra hne
      exact hdist i j hne hij
    exact (LeanFlowPB002.eventual_period_configuration_bound F T P hP hperiod
      t A hinj hcomp).trans hnum
