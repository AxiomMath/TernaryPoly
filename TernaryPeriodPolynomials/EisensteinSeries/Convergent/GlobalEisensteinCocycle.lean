module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.PolynomialEisenstein
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.GlobalEisensteinCocycle

@[expose] public section


/-!
# The global Eisenstein cocycle (convergent)

The global Eisenstein cocycle of a plane source cocycle, assembled from the convergent Eisenstein values.

Re-port of `TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.GlobalEisensteinCocycle` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.GlobalEisensteinCocycle

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.GlobalEisensteinCocycle


open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
def sourceValueAtReal {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane)
    (vertices : Fin 3 → RealGL3) (argument : AdelicGL) : HomogeneousPoly degree :=
  PolynomialEisenstein.polynomialValue data holomorphic
    (PolynomialEisenstein.sourceSection data source vertices) argument

def evaluatedSourceValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane)
    (vertices : Fin 3 → RationalGL3) : HomogeneousPoly degree :=
  sourceValueAtReal data holomorphic source (realVertices vertices)
    (rationalGroup ((vertices 0)⁻¹))

theorem evaluatedSourceValue_eq_anchor {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane)
    (vertices : Fin 3 → RationalGL3) (anchor : RationalGL3) :
    evaluatedSourceValue data holomorphic source vertices =
      PolynomialEisenstein.polynomialValue data holomorphic
        (PolynomialEisenstein.sourceSection data source (realVertices vertices))
        (rationalGroup (anchor⁻¹)) := by
  unfold evaluatedSourceValue
  have argumentEquality : rationalGroup ((vertices 0)⁻¹) =
      rationalGroup ((vertices 0)⁻¹ * anchor) * rationalGroup (anchor⁻¹) := by
    simp [map_mul, mul_assoc]
  rw [argumentEquality]
  exact PolynomialEisenstein.polynomialValue_rational data holomorphic
    (PolynomialEisenstein.sourceSection data source (realVertices vertices))
    ((vertices 0)⁻¹ * anchor) (rationalGroup (anchor⁻¹))

theorem evaluatedSourceValue_fourTerm {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane) (vertices : Fin 4 → RationalGL3) :
    evaluatedSourceValue data holomorphic source ![vertices 1, vertices 2, vertices 3] -
        evaluatedSourceValue data holomorphic source ![vertices 0, vertices 2, vertices 3] +
      evaluatedSourceValue data holomorphic source ![vertices 0, vertices 1, vertices 3] -
        evaluatedSourceValue data holomorphic source ![vertices 0, vertices 1, vertices 2] = 0 := by
  rw [evaluatedSourceValue_eq_anchor data holomorphic source _ (vertices 0),
    evaluatedSourceValue_eq_anchor data holomorphic source _ (vertices 0),
    evaluatedSourceValue_eq_anchor data holomorphic source _ (vertices 0),
    evaluatedSourceValue_eq_anchor data holomorphic source _ (vertices 0)]
  have realFace123 : realVertices ![vertices 1, vertices 2, vertices 3] =
      ![realVertexTuple vertices 1, realVertexTuple vertices 2,
        realVertexTuple vertices 3] := by
    funext index
    fin_cases index <;> rfl
  have realFace023 : realVertices ![vertices 0, vertices 2, vertices 3] =
      ![realVertexTuple vertices 0, realVertexTuple vertices 2,
        realVertexTuple vertices 3] := by
    funext index
    fin_cases index <;> rfl
  have realFace013 : realVertices ![vertices 0, vertices 1, vertices 3] =
      ![realVertexTuple vertices 0, realVertexTuple vertices 1,
        realVertexTuple vertices 3] := by
    funext index
    fin_cases index <;> rfl
  have realFace012 : realVertices ![vertices 0, vertices 1, vertices 2] =
      ![realVertexTuple vertices 0, realVertexTuple vertices 1,
        realVertexTuple vertices 2] := by
    funext index
    fin_cases index <;> rfl
  rw [realFace123, realFace023, realFace013, realFace012]
  exact PolynomialEisenstein.polynomialValue_source_closed data holomorphic source
    (realVertexTuple vertices) (rationalGroup ((vertices 0)⁻¹))

def globalCandidate {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane) :
    (Fin 3 → RationalGL3) → HomogeneousPoly degree :=
  evaluatedSourceValue data holomorphic source

def RationalAnchorCovariance {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane) : Prop :=
  ∀ (element : rationalLevel) (vertices : Fin 3 → RationalGL3),
    sourceValueAtReal data holomorphic source
      (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val *
        realVertices vertices index)
      (rationalGroup ((element.val * vertices 0)⁻¹)) =
    realCoefficientComponent degree data.chi
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val)
      (sourceValueAtReal data holomorphic source (realVertices vertices)
        (rationalGroup ((element.val * vertices 0)⁻¹) * atInfinity
          (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val)))

def globalCocycle_of_rationalAnchorCovariance {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane)
    (covariant : RationalAnchorCovariance data holomorphic source) :
    cocycles rationalLevel (rationalCoefficientComponent degree data.chi) := by
  have candidateEquivariant : ∀ (element : rationalLevel) (vertices : Fin 3 → RationalGL3),
      globalCandidate data holomorphic source (fun index => element.val * vertices index) =
        rationalCoefficientComponent degree data.chi element.val
          (globalCandidate data holomorphic source vertices) := by
    intro element vertices
    let realElement : RealGL3 :=
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val
    have realVertices_mul :
        realVertices (fun index => element.val * vertices index) =
          fun index => realElement * realVertices vertices index := by
      funext index
      simp [realElement, realVertices, map_mul]
    have splitInverse :
        rationalGroup element.val⁻¹ =
          atInfinity realElement⁻¹ * atFinite (rationalFinite element.val⁻¹) := by
      rw [Comparison.rationalGroup_split]
      congr 1
    have argumentRelation :
        rationalGroup ((element.val * vertices 0)⁻¹) * atInfinity realElement =
          rationalGroup ((vertices 0)⁻¹) * atFinite (rationalFinite element.val⁻¹) := by
      calc
        _ = rationalGroup ((vertices 0)⁻¹) *
              (rationalGroup element.val⁻¹ * atInfinity realElement) := by
          simp only [mul_inv_rev, map_mul]
          simp [mul_assoc]
        _ = rationalGroup ((vertices 0)⁻¹) *
              (atInfinity realElement⁻¹ *
                (atFinite (rationalFinite element.val⁻¹) * atInfinity realElement)) := by
          rw [splitInverse]
          simp [mul_assoc]
        _ = rationalGroup ((vertices 0)⁻¹) *
              (atInfinity realElement⁻¹ *
                (atInfinity realElement * atFinite (rationalFinite element.val⁻¹))) := by
          rw [RealTranslations.atFinite_atInfinity_commute]
        _ = rationalGroup ((vertices 0)⁻¹) *
              atFinite (rationalFinite element.val⁻¹) := by
          rw [show atInfinity realElement⁻¹ *
              (atInfinity realElement * atFinite (rationalFinite element.val⁻¹)) =
                (atInfinity realElement⁻¹ * atInfinity realElement) *
                  atFinite (rationalFinite element.val⁻¹) by
            exact (mul_assoc _ _ _).symm]
          rw [← RealTranslations.atInfinity_mul]
          rw [inv_mul_cancel, TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineInductionLaws.atInfinity_one, one_mul]
    have finiteMembership : rationalFinite element.val⁻¹ ∈ finiteLevel := by
      simpa only [map_inv] using
        (finiteLevel.inv_mem (Comparison.rationalLevel_finiteLevel element))
    let finiteElement : finiteLevel := ⟨rationalFinite element.val⁻¹, finiteMembership⟩
    have finiteInvariant :
        sourceValueAtReal data holomorphic source (realVertices vertices)
          (rationalGroup ((vertices 0)⁻¹) * atFinite finiteElement.val) =
        sourceValueAtReal data holomorphic source (realVertices vertices)
          (rationalGroup ((vertices 0)⁻¹)) :=
      PolynomialEisenstein.polynomialValue_finite data holomorphic
        (PolynomialEisenstein.sourceSection data source (realVertices vertices))
        finiteElement (rationalGroup ((vertices 0)⁻¹))
    change evaluatedSourceValue data holomorphic source
        (fun index => element.val * vertices index) =
      rationalCoefficientComponent degree data.chi element.val
        (evaluatedSourceValue data holomorphic source vertices)
    rw [show evaluatedSourceValue data holomorphic source
        (fun index => element.val * vertices index) =
          sourceValueAtReal data holomorphic source
            (realVertices (fun index => element.val * vertices index))
            (rationalGroup ((element.val * vertices 0)⁻¹)) from rfl]
    rw [realVertices_mul]
    rw [show rationalCoefficientComponent degree data.chi element.val =
      realCoefficientComponent degree data.chi realElement from rfl]
    have anchorCovariance := covariant element vertices
    change sourceValueAtReal data holomorphic source
        (fun index => realElement * realVertices vertices index)
        (rationalGroup ((element.val * vertices 0)⁻¹)) =
      realCoefficientComponent degree data.chi realElement
        (sourceValueAtReal data holomorphic source (realVertices vertices)
          (rationalGroup ((element.val * vertices 0)⁻¹) * atInfinity realElement))
      at anchorCovariance
    rw [anchorCovariance]
    rw [argumentRelation, finiteInvariant]
    rfl
  let candidateCochain : cochains rationalLevel
      (rationalCoefficientComponent degree data.chi) 2 :=
    ⟨globalCandidate data holomorphic source, candidateEquivariant⟩
  refine ⟨candidateCochain, ?_⟩
  change (fun vertices : Fin 4 → RationalGL3 =>
    globalCandidate data holomorphic source ![vertices 1, vertices 2, vertices 3] -
        globalCandidate data holomorphic source ![vertices 0, vertices 2, vertices 3] +
      globalCandidate data holomorphic source ![vertices 0, vertices 1, vertices 3] -
        globalCandidate data holomorphic source ![vertices 0, vertices 1, vertices 2]) = 0
  funext vertices
  exact evaluatedSourceValue_fourTerm data holomorphic source vertices

def globalCocycle_of_realCovariance {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane)
    (covariant : ∀ (real : RealGL3) (vertices : Fin 3 → RealGL3) (argument : AdelicGL),
      sourceValueAtReal data holomorphic source (fun index => real * vertices index) argument =
        realCoefficientComponent degree data.chi real
          (sourceValueAtReal data holomorphic source vertices (argument * atInfinity real))) :
    cocycles rationalLevel (rationalCoefficientComponent degree data.chi) := by
  apply globalCocycle_of_rationalAnchorCovariance data holomorphic source
  intro element vertices
  let realElement : RealGL3 :=
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val
  simpa [realElement] using covariant realElement (realVertices vertices)
    (rationalGroup ((element.val * vertices 0)⁻¹))



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.GlobalEisensteinCocycle
