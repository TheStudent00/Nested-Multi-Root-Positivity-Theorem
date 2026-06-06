import Mathlib
import Paper9.PolynomialBounds
import Paper9.QDefinitionAxioms

noncomputable section

/-!
# The General-k Phase-Tracking Theorem

This file formalizes the algebraic skeleton of the multi-root phase-tracking floor theorem.
It proves that the term magnitude ratio `r_j` is permanently bounded below 1 
past a finite algebraic cutoff `j_upper`. 

The proof relies on two foundational analytic combinatorial facts:
1. The structural Maclaurin coefficient ratio `Q` is strictly increasing towards a geometric limit `rho` (due to log-convexity of the coefficients).
2. The binomial polynomial ratio `P` is strictly monotonically decreasing.

We formalize these foundational facts as sorried axioms, and then rigorously prove the 
top-level theorem combining them.
-/

/-- The full term magnitude ratio r_j = Q_j * P_j -/
def r (c1 a : ℝ) (n k j : ℕ) : ℝ := Q' c1 k j * P a n j

/-- The strictly decaying global ceiling U_j = (rho' + epsilon_j) * P_j -/
def U (c1 a : ℝ) (epsilon : ℕ → ℝ) (n j : ℕ) : ℝ := (rho' c1 + epsilon j) * P a n j

/-! ## The Analytic "Trust-Me" Lemmas 

  Mathlib currently lacks the continuous measure theory, Beta integrals,
  and Kaluza's theorem required to mechanize the log-convexity preservation 
  directly. Therefore, we isolate the core composition step and the limit 
  as documented axioms. Everything else builds mechanically from these.
-/

/-- 
  The structural sequence is bounded by the geometric limit plus a decaying envelope.
-/
lemma Q_bounded_envelope (c1 : ℝ) (hc1 : 0 < c1 ∧ c1 < 1/2) (epsilon : ℕ → ℝ) (heps_pos : ∀ j, epsilon j ≥ 0) (k j : ℕ) (hj : 1 ≤ j) : Q' c1 k j < rho' c1 + epsilon j := by
  have h1 : Q' c1 k j < rho' c1 := Q'_bounded c1 hc1 k j hj
  have h2 : rho' c1 ≤ rho' c1 + epsilon j := by linarith [heps_pos j]
  exact lt_of_lt_of_le h1 h2

/-- rho is strictly positive for c1 in (0, 1/2). -/
lemma rho_pos (c1 : ℝ) (hc1_pos : c1 > 0) (hc1_lt : c1 < 1/2) : rho' c1 > 0 := by
  dsimp [rho']
  have h1 : 1 - c1 > 0 := by linarith
  exact div_pos hc1_pos h1

/-! ## The Provable Skeleton -/

/-- The ceiling U_j is strictly decreasing past the cutoff. -/
lemma U_decreasing (c1 a : ℝ) (epsilon : ℕ → ℝ) (n j : ℕ) 
    (ha_pos : a > 0) (hn_pos : n > 0) (h_tail : (j : ℝ) > (n : ℝ) / a) 
    (hc1_pos : c1 > 0) (hc1_lt : c1 < 1/2) 
    (heps_pos : ∀ j, epsilon j ≥ 0)
    (heps_dec : ∀ j, epsilon (j+1) ≤ epsilon j) : 
    U c1 a epsilon n (j+1) < U c1 a epsilon n j := by
  dsimp [U]
  have hr : rho' c1 > 0 := rho_pos c1 hc1_pos hc1_lt
  have hp : P a n (j+1) < P a n j := P_decreasing a n j ha_pos hn_pos h_tail
  have hp_pos : P a n j > 0 := P_pos a n j ha_pos h_tail
  have hp_pos_next : P a n (j+1) > 0 := by
    apply P_pos a n (j+1) ha_pos
    push_cast
    linarith
  have he1 : rho' c1 + epsilon (j+1) ≤ rho' c1 + epsilon j := by linarith [heps_dec j]
  have he2 : rho' c1 + epsilon (j+1) > 0 := by 
    have : epsilon (j+1) ≥ 0 := heps_pos (j+1)
    linarith
  have step1 : (rho' c1 + epsilon (j+1)) * P a n (j+1) < (rho' c1 + epsilon (j+1)) * P a n j := mul_lt_mul_of_pos_left hp he2
  have step2 : (rho' c1 + epsilon (j+1)) * P a n j ≤ (rho' c1 + epsilon j) * P a n j := mul_le_mul_of_nonneg_right he1 (le_of_lt hp_pos)
  exact lt_of_lt_of_le step1 step2

/-- The full ratio r_j is globally bounded by the ceiling U_j. -/
lemma r_bound (c1 a : ℝ) (hc1 : 0 < c1 ∧ c1 < 1/2) (epsilon : ℕ → ℝ) (heps_pos : ∀ j, epsilon j ≥ 0) (n k j : ℕ) (hj : 1 ≤ j) (ha_pos : a > 0) (h_tail : (j : ℝ) > (n : ℝ) / a) : r c1 a n k j < U c1 a epsilon n j := by
  dsimp [r, U]
  have hq : Q' c1 k j < rho' c1 + epsilon j := Q_bounded_envelope c1 hc1 epsilon heps_pos k j hj
  have hp : P a n j > 0 := P_pos a n j ha_pos h_tail
  exact mul_lt_mul_of_pos_right hq hp

/-- Since U is strictly decreasing, it is monotonically decreasing for j ≥ j_upper. -/
lemma U_decreasing_le (c1 a : ℝ) (epsilon : ℕ → ℝ) (n : ℕ) {j_upper j : ℕ} (ha_pos : a > 0) (hn_pos : n > 0)
    (h_tail : (j_upper : ℝ) > (n : ℝ) / a) 
    (hc1_pos : c1 > 0) (hc1_lt : c1 < 1/2) 
    (heps_pos : ∀ j, epsilon j ≥ 0)
    (heps_dec : ∀ j, epsilon (j+1) ≤ epsilon j)
    (h_j : j ≥ j_upper) : U c1 a epsilon n j ≤ U c1 a epsilon n j_upper := by
  induction' h_j with k hk ih
  · exact le_rfl
  · have hk_tail : (k : ℝ) > (n : ℝ) / a := by
      have hk_cast : (k : ℝ) ≥ (j_upper : ℝ) := Nat.cast_le.mpr hk
      linarith
    have h_dec : U c1 a epsilon n (k + 1) < U c1 a epsilon n k := U_decreasing c1 a epsilon n k ha_pos hn_pos hk_tail hc1_pos hc1_lt heps_pos heps_dec
    exact le_trans (le_of_lt h_dec) ih

/-- 
  The Keystone Theorem: Monotonic Non-Return (Conditional on the Validity Region).
  For parameter sets within the explicit validity region, 
  the geometric margin dominates the polynomial excess over the entire tail.
  Therefore, the true ratio `r_j` stays strictly bounded below 1 past the algebraic cutoff.
-/
theorem post_cutoff_non_return 
    (c1 a : ℝ) 
    (epsilon : ℕ → ℝ)
    (n k j_upper j : ℕ) 
    (ha_pos : a > 0)
    (hn_pos : n > 0)
    (h_tail : (j_upper : ℝ) > (n : ℝ) / a)
    (hc1_pos : c1 > 0) 
    (hc1_lt : c1 < 1/2)
    (heps_pos : ∀ j, epsilon j ≥ 0)
    (heps_dec : ∀ j, epsilon (j+1) ≤ epsilon j)
    (h_valid_region : (rho' c1 + epsilon j_upper) * P a n j_upper ≤ 1) 
    (hj_ge1 : 1 ≤ j_upper)
    (h_j : j ≥ j_upper) : 
    r c1 a n k j < 1 := by
  have h_cutoff : U c1 a epsilon n j_upper ≤ 1 := h_valid_region

  have h1 : U c1 a epsilon n j ≤ U c1 a epsilon n j_upper := U_decreasing_le c1 a epsilon n ha_pos hn_pos h_tail hc1_pos hc1_lt heps_pos heps_dec h_j
  have h2 : U c1 a epsilon n j ≤ 1 := le_trans h1 h_cutoff
  have h_j_tail : (j : ℝ) > (n : ℝ) / a := by 
    have hj_cast : (j : ℝ) ≥ (j_upper : ℝ) := Nat.cast_le.mpr h_j
    linarith
  have hj1 : 1 ≤ j := le_trans hj_ge1 h_j
  have h3 : r c1 a n k j < U c1 a epsilon n j := r_bound c1 a ⟨hc1_pos, hc1_lt⟩ epsilon heps_pos n k j hj1 ha_pos h_j_tail
  exact lt_of_lt_of_le h3 h2
