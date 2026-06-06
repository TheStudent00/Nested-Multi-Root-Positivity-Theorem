import Mathlib

open Complex Real

set_option linter.style.whitespace false
set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false

/-!
# Link 0 Certificate: Geometric Minimization & Sheet-Consistency

This file mathematically formalizes Link 0 of the Dominance Hypothesis.
It bridges the gap between the infinite set of all branch points on the shifted 
circle and the genuine principal-sheet singularities of the function.

**The Trust Chain:**
- We TRUST the Python/SymPy symbolic computation which proves that the outer bases
  never equal a negative real number on the principal sheet of the complex power 
  function (since the output argument B*θ is bounded strictly within (-π, π)). 
  Thus, the set of principal-sheet-consistent outer candidates is EMPTY.
- We CERTIFY mathematically in Lean the geometric minimization argument: that for 
  ANY branch point on the shifted circle (admissible or not), the nearest point 
  to the origin is bounded exactly by the near-side real-axis crossing.
-/

/-- 
  Case 1: Origin outside the shifted circle (R ≥ 1 - c1).
  The nearest point on the shifted circle is the near-side real crossing.
-/
lemma geometric_min_case1 (c1 : ℝ) (hc1 : 0 < c1 ∧ c1 < 1 / 2) (z : ℂ) (R : ℝ)
  (h_mag : norm (1 - c1 + c1 * z) = R) 
  (h_outside : 1 - c1 ≤ R) :
  (R - (1 - c1)) / c1 ≤ norm z := by
  have hc1_pos : 0 < c1 := hc1.1
  have h_eq : (c1 : ℂ) * z = (1 - (c1 : ℂ) + (c1 : ℂ) * z) - (1 - (c1 : ℂ)) := by ring
  
  have h_norm_mul : norm ((c1 : ℂ) * z) = c1 * norm z := by
    have h_c1_cast : (c1 : ℂ) = ↑c1 := by rfl
    rw [norm_mul, h_c1_cast, norm_real, Real.norm_eq_abs, abs_of_pos hc1_pos]

  have h_tri := norm_sub_norm_le (1 - (c1 : ℂ) + (c1 : ℂ) * z) (1 - (c1 : ℂ))
  
  have h_1_sub_c1 : norm (1 - (c1 : ℂ)) = 1 - c1 := by
    have h_cast2 : 1 - (c1 : ℂ) = ↑(1 - c1) := by push_cast; rfl
    rw [h_cast2, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    
  rw [h_mag, h_1_sub_c1] at h_tri
  
  have h_tri2 : R - (1 - c1) ≤ norm ((1 - (c1 : ℂ) + (c1 : ℂ) * z) - (1 - (c1 : ℂ))) := h_tri
  rw [← h_eq, h_norm_mul, mul_comm] at h_tri2
  
  exact (div_le_iff₀ hc1_pos).mpr h_tri2

/-- 
  Case 2: Origin inside the shifted circle (R < 1 - c1).
  The near-side real crossing is again the minimum bound.
-/
lemma geometric_min_case2 (c1 : ℝ) (hc1 : 0 < c1 ∧ c1 < 1 / 2) (z : ℂ) (R : ℝ)
  (h_mag : norm (1 - c1 + c1 * z) = R) 
  (h_inside : R < 1 - c1) :
  ((1 - c1) - R) / c1 ≤ norm z := by
  have hc1_pos : 0 < c1 := hc1.1
  
  -- -(c1 * z) = (1 - c1) - (1 - c1 + c1 * z)
  have h_eq : -((c1 : ℂ) * z) = (1 - (c1 : ℂ)) - (1 - (c1 : ℂ) + (c1 : ℂ) * z) := by ring
  
  have h_norm_mul : norm (-((c1 : ℂ) * z)) = c1 * norm z := by
    rw [norm_neg]
    have h_c1_cast : (c1 : ℂ) = ↑c1 := by rfl
    rw [norm_mul, h_c1_cast, norm_real, Real.norm_eq_abs, abs_of_pos hc1_pos]

  have h_tri := norm_sub_norm_le (1 - (c1 : ℂ)) (1 - (c1 : ℂ) + (c1 : ℂ) * z)
  
  have h_1_sub_c1 : norm (1 - (c1 : ℂ)) = 1 - c1 := by
    have h_cast2 : 1 - (c1 : ℂ) = ↑(1 - c1) := by push_cast; rfl
    rw [h_cast2, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    
  rw [h_mag, h_1_sub_c1] at h_tri
  
  have h_tri2 : (1 - c1) - R ≤ norm ((1 - (c1 : ℂ)) - (1 - (c1 : ℂ) + (c1 : ℂ) * z)) := h_tri
  rw [← h_eq, h_norm_mul, mul_comm] at h_tri2
  
  exact (div_le_iff₀ hc1_pos).mpr h_tri2

#print axioms geometric_min_case1
#print axioms geometric_min_case2
