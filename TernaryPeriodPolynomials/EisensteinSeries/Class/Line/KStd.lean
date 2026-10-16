module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBig
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.BaseCusp

@[expose] public section


/-!
# The standard cusp: `lineA1K` at `k = 1`, `b = false` is `lineA1`

The holomorphic series at the cusp `CuspData.ofSL 1` is the plane series (the `planeEisensteinAt_one_eq`),
hence the two explicit coefficients of the radical average of the line-face form coincide.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

theorem planeEisensteinAtInv_one_eq (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) :
    planeEisensteinAtInv false (CuspData.ofSL 1) (gammaN N) (leviGroup N) n f hn
        (leviInCusp_gammaN N 1) =
      planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N) :=
  toInv_congr _ _ fun _ hy a b => congrArg Coef.mk (planeEisensteinAt_one_eq N n f hy a b)

/-- **At the standard cusp the explicit coefficient `lineA1K` is `lineA1`.** -/
theorem lineA1K_one (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    lineA1K N 1 n f false x p q m = lineA1 N n f x p q m := by
  rw [← lineAvgK_coeff N 1 n f false hn hx p q m, planeEisensteinAtInv_one_eq N n f hn,
    lineAvg_coeff_eq_lineA1 N n f hn hx p q m]

end TernaryPeriodPolynomials.Argument.EisensteinClass
