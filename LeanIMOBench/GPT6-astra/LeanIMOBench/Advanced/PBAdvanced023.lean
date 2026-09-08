import LeanFlowProofs.PBAdvanced023.BoundaryRecovery
import LeanFlowProofs.PBAdvanced023.InteriorRoutes
import LeanFlowProofs.PBAdvanced023.RowTwoSweep
import LeanFlowProofs.PBAdvanced023.TwoPathAdversary
import Mathlib

/-
On a table of size $3002\times3001$, a stone is placed on the leftmost cell of the first row. James and Peter play a game on this table. Peter selects $3000$ cells, under the rule that he must choose one from each row except the first and last rows (i.e., the $1$st and $3002$th row), and there must be at most one selected cell in each column. James knows this rule too, but he doesn't know which cells Peter selected. The goal of James is to move the stone to the last row, avoiding the cells selected by Peter. The stone can only move to adjacent cells on the table. If the stone enters a cell selected by Peter, James receives a penalty of 1 point, and the stone returns to its initial position (i.e., the leftmost cell). Find the smallest positive integer $n$ such that there exists a method for James to achieve his goal before receiving a penalty of $n$ points.

Answer: 3
-/
open Classical

-- Game Constants
def R_rows : ℕ := 3002
def C_cols : ℕ := 3001
abbrev Cell : Type := ℕ × ℕ

-- Location definitions
/-- A cell is on the table if its indices are within [1, R_rows] x [1, C_cols]. -/
def IsOnTable (c : Cell) : Prop :=
  c.fst > 0 ∧ c.fst ≤ R_rows ∧ c.snd > 0 ∧ c.snd ≤ C_cols

def start_cell : Cell := (1, 1)
/-- The goal is to reach any cell in the last row. -/
def target_row : Set Cell := { (r, c) | r = R_rows ∧ IsOnTable (r, c) }

-- Adjacency: orthogonal movement within bounds
/-- A move from c₁ to c₂ is adjacent if they are orthogoanlly next to each other and c₂ is on the table. -/
def IsAdjacentMove (c₁ c₂ : Cell) : Prop :=
  IsOnTable c₂ ∧
  (abs ((c₁.fst : ℤ) - (c₂.fst : ℤ)) + abs ((c₁.snd : ℤ) - (c₂.snd : ℤ)) = 1)

-- Peter's Constraints
/-- The set of rows Peter must choose one blocking cell from: {2, 3, ..., R_rows - 1}. -/
def PeterRows : Set ℕ := {r : ℕ | 2 ≤ r ∧ r ≤ R_rows - 1}
/-- The set of valid columns. -/
def Columns : Set ℕ := {c : ℕ | 1 ≤ c ∧ c ≤ C_cols}

/-- A set of selected cells S that satisfies Peter's rules: one cell per row \{2, ..., R-1\}, at most one cell per column {1, ..., C}. -/
def IsPeterSelection (S : Set Cell) : Prop :=
  -- 1. Cells are valid and within Peter's designated rows/columns
  (∀ (r c : ℕ), (r, c) ∈ S → r ∈ PeterRows ∧ c ∈ Columns) ∧
  -- 2. Exactly one selected cell per Peter row
  (∀ r ∈ PeterRows, ∃! c : ℕ, (r, c) ∈ S) ∧
  -- 3. At most one selected cell per column (injectivity)
  (∀ (r₁ c₁ r₂ c₂ : ℕ), (r₁, c₁) ∈ S → (r₂, c₂) ∈ S → c₁ = c₂ → r₁ = r₂)

def PeterSelections : Set (Set Cell) := {S : Set Cell | IsPeterSelection S}

/--
A valid path is a list of cells that starts at the start cell,
finishes at the target row, and consists of adjacent, on-table moves. -/
def IsValidPath (P : List Cell) : Prop :=
  P.head? = some start_cell ∧
  (∃ c ∈ target_row, P.getLast? = some c) ∧
  (∀ c : Cell, c ∈ P → IsOnTable c) ∧
  P.Chain' IsAdjacentMove

/-- A path is winning against a selection S if it is valid, avoids S entirely, and ends on the target row. -/
noncomputable
def pathFirstHit (P : List Cell) (S : Set Cell) : Option (Fin P.length) :=
  P.findFinIdx? (fun c ↦ c ∈ S)

def PathIsWinning (P : List Cell) (S : Set Cell) : Prop :=
  IsValidPath P ∧
  (∀ c : Cell, c ∈ P → c ∉ S)

/--
James' strategy is a finite tree of choosing paths.
Every time James tries a path, this path either succeeds, or James gets an information about
at which step it failed. This equals to the maximum possible penalty a strategy can get.
-/
inductive JamesStrategy
| giveUp
| tryPath (P : List Cell) (hP : IsValidPath P)
  (next : (i : ℕ) → i < P.length → JamesStrategy)

/-- The maximal number of steps a strategy can take -/
noncomputable
def JamesStrategy.depth : JamesStrategy → ℕ
| giveUp => 0
| tryPath P _ next => sSup { (next i.val i.isLt).depth | (i : Fin P.length) } + 1

def JamesStrategy.winsOn (S : Set Cell) : JamesStrategy → Prop
| giveUp => False
| tryPath P _ next =>
  match pathFirstHit P S with
  | some i => (next i.val i.isLt).winsOn S
  | none => True

/-- A given strategy always wins regardless of Peter's selection of cells. -/
def JamesStrategy.wins (strategy : JamesStrategy) : Prop :=
  ∀ S ∈ PeterSelections, strategy.winsOn S

/-- The property that there exists a strategy of length n that guarantees a win before n penalties. -/
def HasWinningStrategyBeforeNPenalties (n : ℕ) : Prop :=
  n > 0 ∧
  ∃ strategy : JamesStrategy, strategy.wins ∧ strategy.depth ≤ n

/-- The smallest positive integer n such that there exists a method for James to achieve his goal before receiving a penalty of n points. -/
noncomputable
def SmallestWinningPenaltyBound : ℕ :=
  sInf {n : ℕ | HasWinningStrategyBeforeNPenalties n}

-- Formalization of the Claim provided in the problem statement
theorem PBAdvanced023 : SmallestWinningPenaltyBound = 3 := by classical
  let First := fun (P : List Cell) (S : Set Cell) (i : Fin P.length) =>
    P.get i ∈ S ∧ ∀ j : Fin P.length, j.val < i.val → P.get j ∉ S
  have hit (P : List Cell) (S : Set Cell) (i : Fin P.length) :
      pathFirstHit P S = some i ↔ First P S i := by
    simpa only [pathFirstHit, List.findFinIdx?_eq_some_iff, decide_eq_true_eq,
      First, List.get_eq_getElem, Fin.getElem_fin, Fin.lt_def]
  have nohit (P : List Cell) (S : Set Cell) :
      pathFirstHit P S = none ↔ ∀ x ∈ P, x ∉ S := by
    simp [pathFirstHit, List.findFinIdx?_eq_none_iff]
  have sweep : ∃ P, IsValidPath P ∧ ∀ S, IsPeterSelection S →
      ∃ i : Fin P.length, First P S i ∧ (P.get i).1 = 2 := by
    exact LeanFlow.PB023.rowTwoSweep 3001 (by norm_num)
  have adversary : ∀ P, IsValidPath P → ∃ i : Fin P.length,
      ∀ Q, IsValidPath Q → ∃ S, IsPeterSelection S ∧ First P S i ∧
        ∃ j : Fin Q.length, Q.get j ∈ S := by
    exact LeanFlow.PB023.twoPathAdversary 3001 (by norm_num)
  have interior : ∀ c : ℕ, 1 < c → c < 3001 →
      ∃ P Q, IsValidPath P ∧ IsValidPath Q ∧
      ∀ S, IsPeterSelection S → (2,c) ∈ S →
        (∀ x ∈ P, x ∉ S) ∨ (∀ x ∈ Q, x ∉ S) := by
    exact LeanFlow.PB023.interiorRoutes 3001 (by norm_num)
  have boundary : ∀ c : ℕ, (c = 1 ∨ c = 3001) →
      ∃ P, IsValidPath P ∧ ∀ i : Fin P.length,
      ∃ Q, IsValidPath Q ∧ ∀ S, IsPeterSelection S → (2,c) ∈ S →
        First P S i → ∀ x ∈ Q, x ∉ S := by
    exact LeanFlow.PB023.boundaryRecovery 3001 (by norm_num)
  have recovery : ∀ c : ℕ, 1 ≤ c → c ≤ 3001 →
      ∃ P, IsValidPath P ∧ ∀ i : Fin P.length,
      ∃ Q, IsValidPath Q ∧ ∀ S, IsPeterSelection S → (2,c) ∈ S →
        First P S i → ∀ x ∈ Q, x ∉ S := by
    intro c hc hC
    by_cases hb : c = 1 ∨ c = 3001
    · exact boundary c hb
    · obtain ⟨P,Q,hP,hQ,hs⟩ := interior c (by omega) (by omega)
      refine ⟨P,hP,fun i => ⟨Q,hQ,?_⟩⟩
      intro S hS hcS hi
      rcases hs S hS hcS with hp | hq
      · exact False.elim (hp (P.get i) (List.get_mem P i) hi.1)
      · exact hq
  have depth_bound (P : List Cell) (hP : IsValidPath P)
      (next : (i : ℕ) → i < P.length → JamesStrategy) (n : ℕ)
      (hn : ∀ i h, (next i h).depth ≤ n) :
      (JamesStrategy.tryPath P hP next).depth ≤ n+1 := by
    apply Nat.add_le_add_right
    apply csSup_le
    · have hp : 0 < P.length := by
        cases P with
        | nil => simpa [IsValidPath] using hP
        | cons x xs => simp
      exact ⟨(next 0 hp).depth, ⟨⟨0,hp⟩,rfl⟩⟩
    · rintro _ ⟨i,rfl⟩
      exact hn i.val i.isLt
  have child_depth (P : List Cell) (hP : IsValidPath P)
      (next : (i : ℕ) → i < P.length → JamesStrategy) (i : Fin P.length) :
      (next i.val i.isLt).depth + 1 ≤ (JamesStrategy.tryPath P hP next).depth := by
    apply Nat.add_le_add_right
    apply le_csSup
    · exact Set.finite_range (fun i : Fin P.length => (next i.val i.isLt).depth) |>.bddAbove
    · exact ⟨i,rfl⟩
  let lastTry := fun (P : List Cell) (hP : IsValidPath P) =>
    JamesStrategy.tryPath P hP (fun _ _ => JamesStrategy.giveUp)
  have last_depth (P : List Cell) (hP : IsValidPath P) : (lastTry P hP).depth ≤ 1 :=
    depth_bound P hP _ 0 (by intros; exact Nat.le_refl 0)
  have last_wins (P : List Cell) (hP : IsValidPath P) (S : Set Cell)
      (hs : ∀ x ∈ P, x ∉ S) : (lastTry P hP).winsOn S := by
    simp only [lastTry, JamesStrategy.winsOn, (nohit P S).2 hs]
  have recoverStrategy (c : ℕ) (hc : 1 ≤ c) (hC : c ≤ 3001) :
      ∃ t : JamesStrategy, t.depth ≤ 2 ∧
        ∀ S, IsPeterSelection S → (2,c) ∈ S → t.winsOn S := by
    obtain ⟨P,hP,hr⟩ := recovery c hc hC
    choose Q hQ hsafe using hr
    let t := JamesStrategy.tryPath P hP (fun i hi => lastTry (Q ⟨i,hi⟩) (hQ ⟨i,hi⟩))
    refine ⟨t, depth_bound P hP _ 1 (fun i hi => last_depth _ _), ?_⟩
    intro S hS hcS
    simp only [t, JamesStrategy.winsOn]
    cases hh : pathFirstHit P S with
    | none => trivial
    | some i => exact last_wins _ _ S (hsafe i S hS hcS ((hit P S i).1 hh))
  obtain ⟨P₀,hP₀,hsweep⟩ := sweep
  have upper : HasWinningStrategyBeforeNPenalties 3 := by
    have branches (i : Fin P₀.length) : ∃ t : JamesStrategy, t.depth ≤ 2 ∧
        ∀ S, IsPeterSelection S → First P₀ S i → (P₀.get i).1 = 2 → t.winsOn S := by
      have hb := hP₀.2.2.1 (P₀.get i) (List.get_mem P₀ i)
      obtain ⟨t,ht,hw⟩ := recoverStrategy (P₀.get i).2 hb.2.2.1 hb.2.2.2
      refine ⟨t,ht,?_⟩
      intro S hS hi hr
      apply hw S hS
      have he : (2,(P₀.get i).2) = P₀.get i := by
        exact Prod.ext hr.symm rfl
      rw [he]
      exact hi.1
    choose t ht hw using branches
    refine ⟨by norm_num, JamesStrategy.tryPath P₀ hP₀ (fun i hi => t ⟨i,hi⟩), ?_, ?_⟩
    · intro S hS
      obtain ⟨i,hi,hr⟩ := hsweep S hS
      rw [JamesStrategy.winsOn, (hit P₀ S i).2 hi]
      exact hw i S hS hi hr
    · exact depth_bound P₀ hP₀ _ 2 (fun i hi => ht ⟨i,hi⟩)
  have zero_loses (t : JamesStrategy) (ht : t.depth = 0) (S : Set Cell) : ¬t.winsOn S := by
    cases t with
    | giveUp => simp [JamesStrategy.winsOn]
    | tryPath P hP next => simp [JamesStrategy.depth] at ht
  have one_loses (Q : List Cell) (hQ : IsValidPath Q)
      (next : (i : ℕ) → i < Q.length → JamesStrategy)
      (ht : (JamesStrategy.tryPath Q hQ next).depth ≤ 1)
      (S : Set Cell) (hj : ∃ j : Fin Q.length, Q.get j ∈ S) :
      ¬(JamesStrategy.tryPath Q hQ next).winsOn S := by
    rw [JamesStrategy.winsOn]
    cases hh : pathFirstHit Q S with
    | none =>
      obtain ⟨j,hj⟩ := hj
      exact False.elim ((nohit Q S).1 hh (Q.get j) (List.get_mem Q j) hj)
    | some i =>
      have hd := child_depth Q hQ next i
      exact zero_loses _ (by omega) S
  have nonempty : ∃ S, IsPeterSelection S := by
    obtain ⟨i,hi⟩ := adversary P₀ hP₀
    obtain ⟨S,hS,_⟩ := hi P₀ hP₀
    exact ⟨S,hS⟩
  have lower (t : JamesStrategy) (ht : t.wins) : 3 ≤ t.depth := by
    by_contra h
    have hd : t.depth ≤ 2 := by omega
    cases t with
    | giveUp =>
      obtain ⟨S,hS⟩ := nonempty
      exact ht S hS
    | tryPath P hP next =>
      obtain ⟨i,hi⟩ := adversary P hP
      have hd' := child_depth P hP next i
      have hdchild : (next i.val i.isLt).depth ≤ 1 := by omega
      cases he : next i.val i.isLt with
      | giveUp =>
        obtain ⟨S,hS,hfirst,_⟩ := hi P hP
        have hw := ht S hS
        rw [JamesStrategy.winsOn, (hit P S i).2 hfirst] at hw
        change (next i.val i.isLt).winsOn S at hw
        rw [he] at hw
        exact hw
      | tryPath Q hQ nextQ =>
        obtain ⟨S,hS,hfirst,hj⟩ := hi Q hQ
        have hw := ht S hS
        rw [JamesStrategy.winsOn, (hit P S i).2 hfirst] at hw
        change (next i.val i.isLt).winsOn S at hw
        rw [he] at hw
        apply one_loses Q hQ nextQ (by simpa only [he] using hdchild) S hj hw
  have minimal (n : ℕ) (hn : HasWinningStrategyBeforeNPenalties n) : 3 ≤ n := by
    obtain ⟨_,t,hw,hd⟩ := hn
    exact le_trans (lower t hw) hd
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) upper
  · exact le_csInf ⟨3,upper⟩ (fun n hn => minimal n hn)
