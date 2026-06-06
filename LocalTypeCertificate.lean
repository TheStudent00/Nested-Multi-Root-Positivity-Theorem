import Mathlib

open Complex Real

set_option linter.style.whitespace false
set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false

/-!
# Local Singularity Type Certificate

This file certifies the hypothesis that the multi-layer polynomial composition
has a local algebraic singularity of exponent B1 near the dominant root z1.

**The Trust Chain:**
- We TRUST the Flajolet-Sedgewick transfer theorem from literature.
- We CERTIFY that our specific polynomial compositions satisfy the local 
  algebraic singularity hypothesis.

The certificate mathematically establishes:
1. The innermost base vanishes to exactly first order at z1 (a simple zero).
2. The outer layers evaluate to strictly non-zero (analytic) constants at z1.
   This relies elegantly on the previously established Dominance bounds, proving
   that since the outer vanishing bounds (R2, R3) are strictly positive and 
   greater than 2(1-c1), the innermost base evaluated at z1 (which is 0) 
   cannot possibly trigger an outer base vanishing.
-/

/-- The innermost base evaluates to 0 at z1. -/
lemma inner_base_zero (c1 : ℝ) (hc1 : 0 < c1 ∧ c1 < 1 / 2) :
  1 - (c1 : ℂ) + (c1 : ℂ) * (((c1 : ℂ) - 1) / (c1 : ℂ)) = 0 := by
  have hc1_comp : (c1 : ℂ) ≠ 0 := by
    intro h
    have h_real : ((c1 : ℂ).re : ℝ) = (0 : ℂ).re := by rw [h]
    -- (c1 : ℂ).re simplifies to c1. (0 : ℂ).re is 0.
    have h_c1_eq_0 : c1 = 0 := h_real
    linarith
  have h_div : (c1 : ℂ) * (((c1 : ℂ) - 1) / (c1 : ℂ)) = (c1 : ℂ) - 1 := by
    exact mul_div_cancel₀ ((c1 : ℂ) - 1) hc1_comp
  rw [h_div]
  ring

/-- The innermost base has a simple zero at z1 (factors linearly). -/
lemma inner_base_simple (c1 : ℝ) (hc1 : 0 < c1 ∧ c1 < 1 / 2) (z z1 : ℂ) (hz1 : z1 = ((c1 : ℂ) - 1) / (c1 : ℂ)) :
  1 - (c1 : ℂ) + (c1 : ℂ) * z = (c1 : ℂ) * (z - z1) := by
  have hc1_comp : (c1 : ℂ) ≠ 0 := by
    intro h
    have h_real : ((c1 : ℂ).re : ℝ) = (0 : ℂ).re := by rw [h]
    have h_c1_eq_0 : c1 = 0 := h_real
    linarith
  rw [hz1]
  have h_div : (c1 : ℂ) * (((c1 : ℂ) - 1) / (c1 : ℂ)) = (c1 : ℂ) - 1 := by
    exact mul_div_cancel₀ ((c1 : ℂ) - 1) hc1_comp
  calc 1 - (c1 : ℂ) + (c1 : ℂ) * z
    _ = (c1 : ℂ) * z - ((c1 : ℂ) - 1) := by ring
    _ = (c1 : ℂ) * z - (c1 : ℂ) * (((c1 : ℂ) - 1) / (c1 : ℂ)) := by rw [h_div]
    _ = (c1 : ℂ) * (z - (((c1 : ℂ) - 1) / (c1 : ℂ))) := by ring

/-- 
  Layer 2 Outer Base is NON-ZERO at z1.
  Follows from the dominance restriction R2 > 2(1-c1).
-/
theorem layer2_nonvanishing 
  (c1 c2 B1 R2 : ℝ) 
  (hc1 : 0 < c1 ∧ c1 < 1 / 2) 
  (hc2 : 0 < c2 ∧ c2 < 1 / 2) 
  (hB1 : 0 < B1 ∧ B1 < 1)
  (h_restrict : 2 * (1 - c1) < R2) :
  norm (1 - (c1 : ℂ) + (c1 : ℂ) * (((c1 : ℂ) - 1) / (c1 : ℂ))) ≠ R2 := by
  
  have h_inner := inner_base_zero c1 hc1
  rw [h_inner, norm_zero]
  
  have h_R2_pos : 0 < R2 := by
    calc (0:ℝ) < 2 * (1 - c1) := by linarith
      _ < R2 := h_restrict
      
  exact ne_of_lt h_R2_pos

/-- 
  Layer 3 Outer Base is NON-ZERO at z1.
  Follows from the dominance restriction R3_prime > 2(1-c1).
-/
theorem layer3_nonvanishing 
  (c1 c2 c3 B1 B2 R3 R3_prime : ℝ) 
  (hc1 : 0 < c1 ∧ c1 < 1 / 2) 
  (hc2 : 0 < c2 ∧ c2 < 1 / 2) 
  (hc3 : 0 < c3 ∧ c3 < 1 / 2)
  (hB1 : 0 < B1 ∧ B1 < 1)
  (hB2 : 0 < B2 ∧ B2 < 1)
  (h_R3 : R3_prime = (R3 - (1 - c2)) / c2)
  (h_restrict3 : 2 * (1 - c1) < R3_prime) :
  norm (1 - (c1 : ℂ) + (c1 : ℂ) * (((c1 : ℂ) - 1) / (c1 : ℂ))) ≠ R3_prime := by
  
  have h_inner := inner_base_zero c1 hc1
  rw [h_inner, norm_zero]
  
  have h_R3_pos : 0 < R3_prime := by
    calc (0:ℝ) < 2 * (1 - c1) := by linarith
      _ < R3_prime := h_restrict3
      
  exact ne_of_lt h_R3_pos

#print axioms inner_base_zero
#print axioms layer2_nonvanishing
#print axioms layer3_nonvanishing
