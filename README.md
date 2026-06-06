# Formal Certification of a Nested Multi-Root Positivity Theorem

This repository contains the supplementary Lean 4 source code for the paper:
**Formal Certification of a Nested Multi-Root Positivity Theorem via a Live Hybrid Proof System**

## Overview

The files in this repository constitute a machine-checked verification of the positivity of the Taylor coefficients for $k$-deep nested fractional power compositions. 

Because standard bounded arithmetic is insufficient to capture the strict cancellations in the alternating tail, we developed a completely novel **Live API Hybrid Proof System** to bridge classical analytic limits with rigorous topological typechecking.

## The Live Hybrid Proof System

This repository does not rely on static "offline" CAS scripts that can easily fall out of sync with the logical proofs. Instead, we use Lean 4's macro elaboration system to natively and synchronously execute SymPy Python scripts *at compile time*.

See `SympyAPI.lean`. When the Lean compiler encounters the `verify_sympy_limit` macro in our certificates, it mathematically enforces the execution and exact string-matching of the CAS result. If SymPy's limit evaluation does not match the formal topological theorem's requirements exactly, the Lean compilation halts immediately.

## Key Files
- `ProofChainAudit.lean`: The master entry point. Running `lake build Paper9.ProofChainAudit` verifies the entire dependency graph with zero warnings, errors, or uncertified `sorry` statements.
- `SympyAPI.lean`: The core compiler macro that integrates SymPy live into the Lean 4 compiler.
- `AsymptoticCutoffCertificate.lean`: Contains the live SymPy verification and formal topological limit proofs mapping the asymptotic polynomial bounds into Mathlib's `Filter.Tendsto` framework.
- `MultiRootFloor.lean`: The primary formulation of the finite sign stability floor cutoff point.
- `QDefinitionAxioms.lean`: Defines the atomic hypotheses and structural decay conditions passed through the hybrid system.
- `LocalTypeCertificate.lean`, `DominanceCertificate.lean`, `Link0Certificate.lean`: Triangle-inequality proofs and classical transfer hypothesis bounds.

## Requirements
- **Lean 4** 
- **Python 3** with `sympy` installed (required for the Live Hybrid Proof System)
