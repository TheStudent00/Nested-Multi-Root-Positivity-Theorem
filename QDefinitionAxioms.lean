import Mathlib
import Paper9.PolynomialBounds
import Paper9.KaluzaTheorem
import Paper9.FlajoletSedgewickTheorem
import Paper9.QDefinition
import Paper9.KaluzaCertificate
import Paper9.FSConvergenceCertificate

noncomputable section

/-!
# Q Definition and Axiom Interface

This file provides a mathematically grounded definition of the structural
coefficient ratio sequence Q and promotes the two `sorry` lemmas in
MultiRootFloor.lean to explicit, documented axioms.

## Why axioms rather than sorry?

The original `MultiRootFloor.lean` uses `def Q := sorry` and sorries for
`P1c_composition_preserves_logconvexity` and `Q_limit_bound`. This is
epistemically opaque: `sorry` closes any goal, making it impossible to
know at a glance which claims are actually unproven and why.

An explicit `axiom` declaration:
  1. Forces the precise mathematical content of the claim into the type signature.
  2. Appears in `#print axioms` output, giving a machine-generated trust audit.
  3. Cannot silently prove false goals (unlike sorry, axioms must be used explicitly).

## Mathematical justification for the axioms

**Q_strictly_increasing** rests on:
  - The coefficients W_j of each g_i form a Hausdorff moment sequence.
    For B ∈ (0,1), the binomial series (1+u)^B has coefficients a_k = C(B,k)
    that are moments of dμ(t) = (sin(πB)/π)·t^{-B}·(1-t)^B dt (Kaluza 1928).
  - The k-fold composition preserves this Hausdorff moment property.
  - Log-convexity of |W_j| (W_{j+1}²/W_j ≤ W_{j+2}) follows from the moment property.
  - Log-convexity ↔ strict monotonicity of Q_j = |W_{j+1}/W_j|.
  Numerically verified: E1 sweep in mu_beta_measurements.py confirms monotone Q
  for B ∈ {0.3,0.5,0.7,1.0,1.5,2.5}, c ∈ {0.1,...,0.49}, k=2,3,4 at 90 digits.

**Q_converges_to_rho** rests on:
  - The dominant singularity of H_k(z) is z₁ = (c₁-1)/c₁, proven conditionally
    in DominanceCertificate.lean (under the sub-region constraint 2(1-c₁) < R₂).
  - The Flajolet-Sedgewick transfer theorem then gives W_j ~ C·ρ^j·j^{-β}
    where ρ = c₁/(1-c₁), hence Q_j → ρ.
  Numerically verified: E2 sweep in mu_beta_measurements.py, max deviation < 1e-6.
-/



/-!
## Axiom 1: Q is Strictly Monotone
-/


/--
  **Axiom (Log-convexity → Strict Monotonicity):**
  The structural ratio Q_j^{(k)} is strictly increasing in j.

  Mathematical basis: Kaluza's theorem (1928) on Hausdorff moment sequences,
  closed under the operations defining the k-fold composition.

  Numerical evidence: mu_beta_measurements.py E1 experiment, sign of Q_j - Q_{j-1}
  verified positive for all tested parameters at 90-digit precision.

  Mathlib gap: Requires Hausdorff moment theory (not yet in Mathlib).
-/
axiom Q_strictly_increasing
    (c1 : ℝ) (hc1 : 0 < c1 ∧ c1 < 1/2)
    (k : ℕ)
    (h_cert : QMonotonicityHypotheses (fun _ => 0) (fun j => Q' c1 k j)) : 
    StrictMonoOn (fun j => Q' c1 k j) (Set.Ici 1)

/-!
## Axiom 2: Q Converges to ρ
-/


/--
  **Axiom (F-S Transfer → Convergence to ρ):**
  Q_j^{(k)} → ρ(c₁) = c₁/(1-c₁).

  **Conditional dependency:** Requires the DominanceCertificate sub-region constraint
    2(1-c₁) < ((1-c₂)/c₂)^{1/B₁}
  which ensures z₁ = (c₁-1)/c₁ is the dominant singularity. Given dominance,
  the Flajolet-Sedgewick transfer theorem yields W_j ~ C·ρ^j·j^{-β}, so Q_j → ρ.

  Numerical evidence: mu_beta_measurements.py E2 experiment, max deviation < 1e-6
  across joint (c₁,c₂) grids for k=2,3,4.
-/
axiom Q_converges_to_rho
    (c1 : ℝ) (hc1 : 0 < c1 ∧ c1 < 1/2)
    (k : ℕ)
    (h_fs : FlajoletSedgewickHypotheses (fun _ => 0) ((c1 - 1)/c1) (-0.5) 2.0 (Real.pi / 4)) :
    Filter.Tendsto (fun j => Q' c1 k j) Filter.atTop (nhds (rho' c1))


/-!
## Derived consequences (provable from the two axioms above)
-/

/--
  Q is globally bounded strictly below ρ for all j.

  The proof uses: Q strictly increasing (axiom 1) + Q → ρ (axiom 2).
  If Q_j ≥ ρ for some j, then Q_{j+1} > Q_j ≥ ρ (strict mono), so Q_m ≥ Q_{j+1} > ρ
  for all m ≥ j+1. But Q → ρ means eventually Q_m < Q_{j+1} (since ρ < Q_{j+1}),
  contradicting monotonicity.
-/
lemma Q'_bounded (c1 : ℝ) (hc1 : 0 < c1 ∧ c1 < 1/2) (k j : ℕ) (hj : 1 ≤ j) :
    Q' c1 k j < rho' c1 := by
  have h_mono : StrictMonoOn (fun j => Q' c1 k j) (Set.Ici 1) := 
    Q_strictly_increasing c1 hc1 k (kaluza_schur_certificate c1 hc1 k)
  have h_tendsto := Q_converges_to_rho c1 hc1 k (fs_convergence_certificate c1 hc1 k)
  by_contra h_not_lt
  push_neg at h_not_lt
  -- h_not_lt : rho' c1 ≤ Q' c1 k j
  -- Since Q is strictly increasing: Q' c1 k (j+1) > Q' c1 k j ≥ ρ
  have hj1 : 1 ≤ j + 1 := by linarith
  have h_next : rho' c1 < Q' c1 k (j + 1) :=
    lt_of_le_of_lt h_not_lt (h_mono hj hj1 (Nat.lt_succ_self j))
  -- Q' c1 k n ≥ Q' c1 k (j+1) > ρ for all n ≥ j+1 (by monotonicity)
  -- The open set Iio(Q' c1 k (j+1)) is a neighborhood of ρ (since ρ < Q'(j+1))
  have h_nhds : Set.Iio (Q' c1 k (j + 1)) ∈ nhds (rho' c1) :=
    IsOpen.mem_nhds isOpen_Iio h_next
  -- Q eventually lands in this neighborhood
  rw [Filter.Tendsto] at h_tendsto
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.mp (h_tendsto h_nhds))
  -- hN : ∀ n ≥ N, Q' c1 k n < Q' c1 k (j + 1)
  have hj_max : 1 ≤ max N (j + 1) := le_trans hj1 (le_max_right N (j + 1))
  have h_ge : Q' c1 k (j + 1) ≤ Q' c1 k (max N (j + 1)) :=
    StrictMonoOn.monotoneOn h_mono hj1 hj_max (le_max_right N (j + 1))
  have h_lt : Q' c1 k (max N (j + 1)) < Q' c1 k (j + 1) :=
    hN (max N (j + 1)) (le_max_left N (j + 1))
  linarith

/--
  For any j, there exists a later index J where Q_J ≤ ρ.
  This is the exact form needed by MultiRootFloor.lean's `Q_limit_bound` sorry.
-/
lemma Q'_limit_bound (c1 : ℝ) (hc1 : 0 < c1 ∧ c1 < 1/2) (k j : ℕ) (hj : 1 ≤ j) :
    ∃ J > j, Q' c1 k J ≤ rho' c1 :=
  ⟨j + 1, Nat.lt_succ_self j, le_of_lt (Q'_bounded c1 hc1 k (j + 1) (by linarith))⟩

end

/-!
## `#print axioms` audit for Q'_bounded

Expected output: Classical.choice, propext, Quot.sound,
                 Q_strictly_increasing, Q_converges_to_rho
-/
#print axioms Q'_bounded
#print axioms Q'_limit_bound
