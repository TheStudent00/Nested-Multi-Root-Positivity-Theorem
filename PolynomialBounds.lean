import Mathlib

noncomputable section

/-!
# Polynomial Binomial Bounds

This file defines the polynomial factor sequence `P` and proves its algebraic properties.
`P` is defined as:
  P(a, n, j) = ∏_{i=0}^{n-1} (1 + a / (a*j - i))

We prove two main lemmas:
1. `P_pos`: For j > n/a, P is strictly positive.
2. `P_decreasing`: For j > n/a, P(j+1) < P(j).
-/

open Finset

/-- 
  The polynomial factor P(j) = |binom(a(j+1), n) / binom(aj, n)|.
  For j > n/a, this is known to be strictly monotonically decreasing.
-/
def P (a : ℝ) (n j : ℕ) : ℝ :=
  (range n).prod (fun i => 1 + a / (a * j - (i : ℝ)))

/-- P is strictly positive for sufficiently large j. -/
lemma P_pos (a : ℝ) (n j : ℕ) (ha_pos : a > 0) (h_tail : (j : ℝ) > (n : ℝ) / a) : 
    P a n j > 0 := by
  dsimp [P]
  apply Finset.prod_pos
  intro i hi
  have h_i_lt_n : i < n := Finset.mem_range.mp hi
  have h_i_lt_n_real : (i : ℝ) < (n : ℝ) := Nat.cast_lt.mpr h_i_lt_n
  have h_n_lt_aj : (n : ℝ) < (j : ℝ) * a := (div_lt_iff₀ ha_pos).mp h_tail
  have h_denom_pos : a * (j : ℝ) - (i : ℝ) > 0 := by linarith
  have h_frac_pos : a / (a * (j : ℝ) - (i : ℝ)) > 0 := div_pos ha_pos h_denom_pos
  linarith

lemma prod_strict_mono (n : ℕ) (hn_pos : n > 0) (f g : ℕ → ℝ) 
    (h_pos_f : ∀ i < n, 0 < f i) 
    (h_pos_g : ∀ i < n, 0 < g i) 
    (h_lt : ∀ i < n, f i < g i) : 
    (range n).prod f < (range n).prod g := by
  induction' n with k ih
  · contradiction
  · by_cases hk : k = 0
    · subst hk
      simp
      exact h_lt 0 (by linarith)
    · rw [prod_range_succ, prod_range_succ]
      have hk_pos : k > 0 := Nat.pos_of_ne_zero hk
      have h1 : (range k).prod f < (range k).prod g := by
        apply ih hk_pos
        · intro i hi; exact h_pos_f i (lt_trans hi (by linarith))
        · intro i hi; exact h_pos_g i (lt_trans hi (by linarith))
        · intro i hi; exact h_lt i (lt_trans hi (by linarith))
      have h2 : f k < g k := h_lt k (by linarith)
      have h3 : 0 < f k := h_pos_f k (by linarith)
      have h4 : 0 ≤ (range k).prod g := by
        apply le_of_lt
        apply prod_pos
        intro i hi
        have hi_lt : i < k := mem_range.mp hi
        exact h_pos_g i (lt_trans hi_lt (by linarith))
      exact mul_lt_mul h1 (le_of_lt h2) h3 h4

/-- 
  The polynomial factor P is strictly monotonically decreasing for large j.
-/
lemma P_decreasing (a : ℝ) (n j : ℕ) (ha_pos : a > 0) (hn_pos : n > 0) (h_tail : (j : ℝ) > (n : ℝ) / a) : 
    P a n (j+1) < P a n j := by
  dsimp [P]
  have h_n_lt_aj : (n : ℝ) < (j : ℝ) * a := (div_lt_iff₀ ha_pos).mp h_tail
  apply prod_strict_mono n hn_pos
  · intro i hi
    have : (i : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hi
    have h_denom : a * ((j + 1 : ℕ) : ℝ) - (i : ℝ) > 0 := by push_cast; linarith
    have h_frac : a / (a * ((j + 1 : ℕ) : ℝ) - (i : ℝ)) > 0 := div_pos ha_pos h_denom
    linarith
  · intro i hi
    have : (i : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hi
    have h_denom : a * (j : ℝ) - (i : ℝ) > 0 := by linarith
    have h_frac : a / (a * (j : ℝ) - (i : ℝ)) > 0 := div_pos ha_pos h_denom
    linarith
  · intro i hi
    have : (i : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hi
    have h_denom_pos : a * (j : ℝ) - (i : ℝ) > 0 := by linarith
    have h_denom_next : a * ((j + 1 : ℕ) : ℝ) - (i : ℝ) > 0 := by push_cast; linarith
    have h_denom_lt : a * (j : ℝ) - (i : ℝ) < a * ((j + 1 : ℕ) : ℝ) - (i : ℝ) := by push_cast; linarith
    have h_inv : 1 / (a * ((j + 1 : ℕ) : ℝ) - (i : ℝ)) < 1 / (a * (j : ℝ) - (i : ℝ)) := one_div_lt_one_div_of_lt h_denom_pos h_denom_lt
    have h_mul : a * (1 / (a * ((j + 1 : ℕ) : ℝ) - (i : ℝ))) < a * (1 / (a * (j : ℝ) - (i : ℝ))) := mul_lt_mul_of_pos_left h_inv ha_pos
    have h_left : 1 + a / (a * ((j + 1 : ℕ) : ℝ) - (i : ℝ)) = 1 + a * (1 / (a * ((j + 1 : ℕ) : ℝ) - (i : ℝ))) := by ring
    have h_right : 1 + a / (a * (j : ℝ) - (i : ℝ)) = 1 + a * (1 / (a * (j : ℝ) - (i : ℝ))) := by ring
    linarith
