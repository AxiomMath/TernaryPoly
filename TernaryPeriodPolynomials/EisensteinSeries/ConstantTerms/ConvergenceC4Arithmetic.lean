module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ConvergenceC4

@[expose] public section


/-!
# Proposition C.4: the cusp group `Λ_P` is arithmetic by definition

Formalized by Claude Sonnet 5.5.

The parametric statements of `Statements.ConvergenceC4` (`*_at`, for a `CuspData` `D` that is an arbitrary real
change of basis) carry the typeclass hypotheses `[Λ.HasDetOne] [Λ.IsArithmetic]`, needed to speak of
`CuspForm Λ k` in Mathlib.  The paper makes no such assumption, and none is missing: its seed
is `ω_h` for `h ∈ S_k(Λ_P)` where

> "Let `Γ_P = Γ ∩ P(ℚ)`, and let `Λ_P` be its projection onto the determinant-one binary Levi. If
> `h ∈ S_k(Λ_P)`, set ..."

and `S_k(Λ)` is defined only for finite-index subgroups `Λ ⊂ SL₂(ℤ)` ("For a finite-index subgroup
`Λ ⊂ SL₂(ℤ)`, a weight-`k` cusp form is holomorphic on `𝔥`, satisfies `h|_kγ = h` for `γ ∈ Λ`, and has a
Fourier expansion with only positive powers at every cusp").  All cusps of the paper are rational
("All rational flags are obtained by integral changes of basis, which preserve the principal
congruence subgroup";: "Rationally conjugate the finitely many other plane cusps to `P` and sum the
same construction over them"), so for the paper's data the projection `Λ_P` is a finite-index subgroup of
`SL₂(ℤ)` and the hypotheses are theorems:

* `leviGroup_isArithmetic`, `leviGroup_hasDetOne`: `Λ_P = Γ₂(N)` (the image of the principal congruence
  subgroup of `SL₂(ℤ)`) is arithmetic;
* `levi_projection_eq_leviGroup`: at every plane cusp `h⁻¹ P h` of `Γ(N)`, `h ∈ SL₃(ℤ)` (hence at every
  rational plane cusp, `prop_C_4_rational_cusp_gammaN`), the Levi projection of the cusp stabilizer `Γ_{P'}` IS
  `Γ₂(N)`, so the form space `S_{n+3}(Λ_P)` of the paper is `CuspForm (leviGroup N) (n+3)`;
  no compatibility hypothesis `LeviInCusp` remains.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4

/-- `Λ_P = Γ₂(N)` is an arithmetic subgroup of `SL₂(ℤ)` (finite index), so `S_k(Λ_P)` is defined. -/
theorem leviGroup_isArithmetic (N : ℕ) [NeZero N] : (leviGroup N).IsArithmetic := inferInstance

/-- `Λ_P` consists of determinant-one matrices. -/
theorem leviGroup_hasDetOne (N : ℕ) [NeZero N] : (leviGroup N).HasDetOne := inferInstance

/-- **The Levi data of every plane cusp of `Γ(N)`:** the determinant-one Levi projection `Λ_P`
of the cusp stabilizer `Γ_{P'} = Γ ∩ h⁻¹ P(ℚ) h`, conjugated back to `P`, is exactly `Γ₂(N)`. -/
theorem levi_projection_eq_leviGroup (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (h : SL(3, ℤ)) :
    ∀ g : GL (Fin 2) ℝ, g ∈ leviGroup N ↔ ∃ p ∈ gammaN N, p ∈ stabRow (CuspData.ofSL h).r ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        topBlock ((CuspData.ofSL h).a * realMat p * (CuspData.ofSL h).a⁻¹) :=
  (prop_C_4_cusp_gammaN N h3 h false 4 le_rfl 0).2.1

end TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
