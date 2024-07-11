import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/- You can search for theorems in mathlib using:
   1. The official documentation: https://leanprover-community.github.io/mathlib4_docs/index.html
   2. The pattern search engine Loogle: https://loogle.lean-lang.org/
-/


/- Proving an `∃n, p n` statement: The `use x` tactic tells lean that you
   will use x and show that p x holds. -/
theorem example_proving_exists : ∃ n:ℕ, 2*n+3 = 7 := by
  use 2

/- Using a `∃n, p n` statement: You can obtain an element x and the assumption
   p x by writing `have ⟨x, hx⟩ := h_exists` -/
theorem example_using_exists2
    (h_exists: ∃n:ℕ, 2*n+3 = 7)
    : ∃n:ℕ, n-1 = 6 := by
  have ⟨x, hx⟩ := h_exists
  use (2*x+3)
  simp [hx]

/- Proving a `∀n, p n` statement: The `intro n` tactic adds an arbitrary
   n to your tactic state and you need to show that p n holds. -/
theorem example_proving_for_all: ∀ n:ℕ, n-n = 0 := by
  intro n
  simp

/- Using a `∀n, p n` statement: You can apply the `h_for_all` assumption as
   if it were a function. So pass in a specific value of `n` and you get a
   proof that `p n` holds for that value of n. -/
theorem example_using_for_all
    (h_for_all: ∀ n:ℕ, (n+1)*(n-1) = n^2-1)
    : (8+1)*(8-1) + 1 = 8^2 := by
  have h_8 : (8+1)*(8-1) = 8^2-1 := by exact h_for_all 8
  rw [h_8]
  simp

/- Induction proofs: Use
   ```
   induction n with
   | zero => <proof of base case>
   | succ n ih => <proof of inductive step, with ih as the inductive hypothesis>
   ```
-/
theorem example_induction: ∀n:ℕ, 0 < 1+n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp [ih]

/- Using a `p ∨ q` statement: Use the syntax
  ```
  cases h_or with
  | inl h_left => <proof assuming p>
  | inl h_right => <proof assuming q>
  ```
-/
theorem example_using_or
    (n: ℕ) (h_or : n = 8 ∨ n = 11)
    : ∃ k:ℕ, 3*k = n+1 := by
  cases h_or with
  | inl h_left =>
    use 3
    rw [h_left]
  | inr h_right =>
    use 4
    rw [h_right]


/- Proving a `p ∨ q` statement: Use the `left` tactic if you can show p,
   or the `right` tactic if you can show q. Usually you will need to have
   an "or" statement in your hypothesis so you can split based on cases
   there.

   Another way to prove `p ∨ q` is to use
   `apply Classical.or_iff_not_imp_left.mpr`
   which transforms the goal to proving `¬p → q`. Then you can use
   `intro h_np` to assume `¬p` and use that to prove `q`.
-/
theorem example_odd_or_even: ∀n:ℕ, ∃k:ℕ, n=2*k ∨ n=2*k+1 := by
  intro n
  induction n with
  | zero =>
    use 0
    simp
  | succ n ih =>
    have ⟨k, h_or⟩ := ih
    cases h_or with
    | inl h_left =>
      use k
      right
      rw [h_left]
    | inr h_right =>
      use (k+1)
      left
      rw [h_right]
      ring

/- Proving a `p ∧ q` statement: Create a proof `hp` of `p` and a proof `hq` of
  `q` in your tactic state, then use `exact ⟨hp, hq⟩`.
-/
theorem example_proving_and : ∀n:ℕ, 0 < 1 + n ∧ n - n = 0 := by
  intro n
  have hp : 0 < 1 + n := by exact example_induction n
  have hq : n - n = 0 := by exact example_proving_for_all n
  exact ⟨hp, hq⟩

/- Using a `p ∧ q` statement: You can use the syntax
  ```
  have ⟨h_left, h_right⟩ := h_and
  ```
  so that `h_left` is a proof of `p` and `h_right` is a proof of `q`.
-/
theorem example_using_and (n:ℕ) (h_and : n < 5 ∧ 2 < n) : n = 3 ∨ n = 4 := by
  apply Classical.or_iff_not_imp_left.mpr
  intro h_ne_3
  have ⟨h_left, h_right⟩ := h_and
  have h_3_ne : 3 ≠ n := by exact ne_comm.mp h_ne_3
  have h_3_le : 3 ≤ n := by exact Nat.add_one_le_of_lt h_right
  have h_3_lt : 3 < n := by exact Nat.lt_iff_le_and_ne.mpr ⟨h_3_le, h_3_ne⟩
  linarith
