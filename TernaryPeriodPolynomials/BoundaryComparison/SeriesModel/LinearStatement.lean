module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.FormClass
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaces
public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.ModelUnfolding

@[expose] public section


/-!
# The level-`K†` linear comparison of the form series with the model Eisenstein class (statement only)

Formalized by Claude Sonnet 5.5.  Paper: Proposition C.4 and
the construction of `ℰ_P(ξ)`.

This file DEFINES a proposition; nothing assumes it and no theorem is derived from it.
* `modelClassK`: the class in `H²(K†, E_n)` of the model Eisenstein cocycle `EndpointEisensteinCocycle.globalCocycle` of a plane source of a datum with trivial rank-one character.
* `FormSeriesEqModelLinear N h3 hN n hn`: the linear, cusp-indexed comparison (finite family of data, `ℝ`-linear source dictionary `Φ`, fixed weights `w`): for ALL cusp-indexed
  inputs `f` (including `0` and arbitrary combinations; no eigenform hypothesis, no nonvanishing of the output) the model class of the sources `Φ f` equals the weighted sum of the
  `K†`-corestrictions of the complexified series classes.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.FormSeriesModel
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeriesModel

/-- The class of the model Eisenstein cocycle of a plane source, in `H²(K†, E_n)` (the rank-one character is transported along `hD`). -/
def modelClassK {n : ℕ} (hn : 4 ≤ n) (D : InducingData n) (hD : D.chi = trivialCharacter)
    (src : SourceSpace.sourceCocycles D .plane) :
    H2 rationalLevel (rationalCoefficientComponent n trivialCharacter) :=
  Eq.mp (congrArg (fun χ => H2 rationalLevel (rationalCoefficientComponent n χ)) hD)
    (classOf rationalLevel (rationalCoefficientComponent n D.chi)
      (EndpointEisensteinCocycle.globalCocycle D (planeEisensteinConvergent hn D) hn src))

/-- **The linear comparison (statement).** See the file header. -/
def FormSeriesEqModelLinear (N : ℕ) [NeZero N] [Fintype (PlaneFaces N)] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ) (hn : 4 ≤ n) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (D : ι → InducingData n) (hD : ∀ i, (D i).chi = trivialCharacter)
    (Φ : (PlaneFaces N → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) →ₗ[ℝ]
        ((i : ι) → SourceSpace.sourceCocycles (D i) .plane))
    (w : PlaneFaces N → Bool → ℂ),
    (∃ x b, w x b ≠ 0) ∧
    ∀ f : PlaneFaces N → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ),
      ∑ i, modelClassK hn (D i) (hD i) (Φ f i) =
        ∑ x, ∑ b : Bool, w x b • formClassKAt N h3 hN n hn (f x) (Quotient.out x) b

end TernaryPeriodPolynomials.Argument.FormSeriesModel
