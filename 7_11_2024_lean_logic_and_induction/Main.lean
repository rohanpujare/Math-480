import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

/- Supply proofs for 2 out of the 3 assignments.
   Do all 3 for 5 points of extra credit.

   All assignments can be proven through induction and appropriate use of library functions and logic operations.
-/

-- Assignment 1: Show that 2^n % 7 = 1, 2, or 4 for all n.
theorem assignment1 : ∀ n : ℕ, 2^n % 7 = 1 ∨ 2^n % 7 = 2 ∨ 2^n % 7 = 4 := by
  intro n
  induction n with
  | zero =>
    left
    rw [pow_zero]
    norm_num
  | succ k ih =>
    cases ih with
    | inl h =>
      rw [pow_succ, h]
      norm_num
    | inr h' =>
      cases h' with
      | inl h =>
        rw [pow_succ, h]
        norm_num
      | inr h =>
        rw [pow_succ, h]
        norm_num

-- Assignment 2: Show that (1-x)*(1+x+x^2+...+x^{n-1}) = (1-x^n)
theorem assignment2
    (x:ℝ)
    : ∀ n:ℕ, (1-x)*(∑ i ∈ Finset.range n, x^i) = 1-x^n := by
  intro n
  induction n with
  | zero =>
    simp [Finset.range, Finset.sum]
  | succ k ih =>
    calc
      (1 - x) * (∑ i in Finset.range (k + 1), x^i)
          = (1 - x) * (∑ i in Finset.range k, x^i + x^k) := by rw [Finset.sum_range_succ]
      _ = (1 - x) * (∑ i in Finset.range k, x^i) + (1 - x) * x^k := by ring
      _ = (1 - x^k) + (x^k - x^(k + 1)) := by rw [ih]; ring
      _ = 1 - x^(k + 1) := by ring

-- Assignment 3: Show that if a_0 = 0, a_{n+1} = 2*a_n+1 then a_n = 2^n-1.
theorem assignment3
    (a: ℕ → ℝ) (h_zero: a 0 = 0) (h_rec: ∀ n:ℕ, a (n+1) = 2 * (a n) + 1)
    : ∀ n:ℕ, a n = 2^n - 1 := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero, h_zero]
    norm_num
  | succ k ih =>
    rw [h_rec, ih]
    have h : 2 * (2^k - 1) + 1 = 2 * 2^k - 2 + 1 := by ring_nf
    rw [h]
    rw [pow_succ]
    norm_num
