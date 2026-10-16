module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Lit

@[expose] public section


/-!
# `K†` comparison, CMP-1: global inflation is an isomorphism onto the invariants

`litClass_injective`: the literal class of a `K†`-class determines it.  `mem_range_litClass_iff`: a class of `H²(Γ(N), E_n)` is the literal
class of a `K†`-class iff its transport to `Γ ∩ Γ(N)` (the `classPrincipal`) is invariant under the action of `K† = rationalLevel` on
`H²(Γ ∩ Γ(N), E_n)` by conjugation and the coefficient action (`LevelTransfer.actH2`, `invariantsH2`).  The coefficient action is
`rationalCoefficientComponent n trivialCharacter`, so elements of determinant `-1` of `K†` act with their sign (`realCoefficient` retains
`det⁻¹`), as required by the paper.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

/-- **CMP-1 (injectivity).** -/
theorem litClass_injective : Function.Injective (litClass N h3 hN n) := by
  intro a b hab
  have h := congrArg (classPrincipal N h3 n hN) hab
  rw [classPrincipal_litClass, classPrincipal_litClass] at h
  exact resH2_injective (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N)
    (levelPrincipal_norm N) h

/-- **CMP-1 (range).** -/
theorem mem_range_litClass_iff (x : groupCohomology.H2 (gammaRep (gammaN N) n)) :
    x ∈ LinearMap.range (litClass N h3 hN n) ↔
      classPrincipal N h3 n hN x ∈ invariantsH2 (rationalCoefficientComponent n trivialCharacter)
        (levelPrincipal_norm N) := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [classPrincipal_litClass]
    intro s hs
    exact (mem_range_resH2_iff (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N)
      (levelPrincipal_norm N) _).mp ⟨a, rfl⟩ s hs
  · intro hx
    obtain ⟨a, ha⟩ := (mem_range_resH2_iff (rationalCoefficientComponent n trivialCharacter)
      (levelPrincipal_le N) (levelPrincipal_norm N) _).mpr hx
    refine ⟨a, ?_⟩
    change (principalIso N h3 n hN).inv.hom (bridge (rationalCoefficientComponent n trivialCharacter)
      (levelPrincipal N) (resH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N) a)) = x
    rw [ha]
    exact principalIso_inv_classPrincipal N h3 hN n x

end TernaryPeriodPolynomials.Argument.KDaggerComparison
