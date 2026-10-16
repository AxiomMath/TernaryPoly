module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Basic
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ChartIntegrals

@[expose] public section


/-!
# The analytic inputs of the restriction formula, without a degree bound

The restriction formula for the global Eisenstein cocycle (`EisensteinGraph.ConstantTerm`) uses the
hypothesis `4 ≤ n` only through four analytic properties of the Eisenstein value `E(f)` at the
cohomological point `s₀ = -3/2` and of the standard partner of a plane source cocycle:

* `EisensteinContinuous`: `E(f)` is a continuous function on `GL₃(𝔸)`;
* `PlaneConstantTermAtEdge`: the constant term of `E(f)` along the plane radical is `f`;
* `SourceRealCovariant`: the vertex values of `E` are covariant under real translations, so that
  `E` defines a global cocycle (`globalCocycle`);
* `LineConstantTermAtEdge`: the coefficients of the line source cocycle are the constant terms of the
  Eisenstein coefficients along the line radical.

This file states the four properties and defines the defect cochain and its translation family
for an arbitrary plane source cocycle `c` and an arbitrary line source cocycle `line`, in place of
the standard continuation `J c` of the absolutely convergent range.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph

variable {n : ℕ}

/-- The Eisenstein value of every plane section at `s₀` is continuous. -/
def EisensteinContinuous (D : InducingData n) (hol : PlaneEisensteinHolomorphic D) : Prop :=
  ∀ f : SectionSpace.inducedSections D .plane cohomologicalPoint,
    Continuous (SectionSpace.sectionEisensteinValue D hol f).val

/-- The constant term along the plane radical of the Eisenstein value of a plane section at `s₀`
is the section itself. -/
def PlaneConstantTermAtEdge (D : InducingData n) (hol : PlaneEisensteinHolomorphic D) : Prop :=
  ∀ (f : SectionSpace.inducedSections D .plane cohomologicalPoint) (g : AdelicGL),
    (∫ point : Adeles × Adeles, (SectionSpace.sectionEisensteinValue D hol f).val
      (planeUnipotent point.1 point.2 * g) ∂planeDomainMeasure) = f.val g

/-- Real covariance of the vertex values of the Eisenstein operator on a plane source cocycle. -/
def SourceRealCovariant (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) : Prop :=
  ∀ (real : RealGL3) (vertices : Fin 3 → RealGL3) (argument : AdelicGL),
    GlobalEisensteinCocycle.sourceValueAtReal D hol c (fun index => real * vertices index)
        argument =
      realCoefficientComponent n D.chi real
        (GlobalEisensteinCocycle.sourceValueAtReal D hol c vertices (argument * atInfinity real))

/-- The coefficients of the line source cocycle `line` are the constant terms along the line
radical of the Eisenstein coefficients of `c`. -/
def LineConstantTermAtEdge (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (line : SourceSpace.sourceCocycles D .line) :
    Prop :=
  ∀ (vertices : Fin 3 → RealGL3) (argument : AdelicGL) (monomial : Fin 3 →₀ ℕ),
    (line.val vertices argument).val.coeff monomial =
      ∫ pair in additiveDomain ×ˢ additiveDomain,
        (GlobalEisensteinCocycle.sourceValueAtReal D hol c vertices
          (lineUnipotent pair.1 pair.2 * argument)).val.coeff monomial ∂radicalMeasure

/-- The global Eisenstein cocycle of a plane source cocycle with real-covariant vertex values. -/
def globalCocycle (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (cov : SourceRealCovariant D hol c) :
    cocycles rationalLevel (rationalCoefficientComponent n D.chi) :=
  GlobalEisensteinCocycle.globalCocycle_of_realCovariance D hol c cov

theorem globalCocycle_realizes (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (cov : SourceRealCovariant D hol c)
    (vertices : Fin 3 → RationalGL3) :
    (globalCocycle D hol c cov).val.val vertices =
      GlobalEisensteinCocycle.evaluatedSourceValue D hol c vertices := rfl

/-- The source cocycle of each side: `c` on the plane stratum and `line` on the line stratum. -/
def sideSource (D : InducingData n) (c : SourceSpace.sourceCocycles D .plane)
    (line : SourceSpace.sourceCocycles D .line) : (side : Side) → SourceSpace.sourceCocycles D side
  | .plane => c
  | .line => line

/-- The defect `(E c - c_side)(y)(g)`. -/
def defectValue (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (line : SourceSpace.sourceCocycles D .line)
    (side : Side) (y : Fin 3 → RealGL3) (g : AdelicGL) : HomogeneousPoly n :=
  ConstantTerm.eisensteinValue D hol c y g - (sideSource D c line side).val y g

/-- The flag 2-cochain measuring the failure of the restriction formula on one stratum. -/
def defectCochain (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (cov : SourceRealCovariant D hol c)
    (line : SourceSpace.sourceCocycles D .line) (side : Side) :
    cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side) 2 :=
  (restrictionCocycle n D.chi side (globalCocycle D hol c cov)).val -
    (SourceSpace.evaluatedSource D side (sideSource D c line side)).val

/-- The real translation family of the defect at the rational flag `q`:
`r ↦ (E c - c_side)(y)(u(K r) q⁻¹)`. -/
def defectFamily (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (line : SourceSpace.sourceCocycles D .line)
    (side : Side) (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) :
    HomogeneousPoly n :=
  defectValue D hol c line side (GlobalEisensteinCocycle.realVertices y)
    (atInfinity (ConstantTerm.sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) * rationalGroup q⁻¹)

end TernaryPeriodPolynomials.EdgeEisenstein
