module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PrismTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourceVertexPrism_left_translate {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data side source)
    (projection : RealGL3 → RealGL3) (element : RealGL3)
    (vertices : Fin 2 → RealGL3) (argument : AdelicGL)
    (covariant : ∀ index, projection (element * vertices index) = element * projection (vertices index)) :
    homogeneousVertexPrism (fun vertices => source vertices argument) projection
      (fun index => element * vertices index) =
    realCoefficientComponent degree data.chi element
      (homogeneousVertexPrism (fun vertices => source vertices (argument * atInfinity element)) projection vertices) := by
  have translated (first second third : RealGL3) :
      source ![element * first, element * second, element * third] argument =
      realCoefficientComponent degree data.chi element
        (source ![first, second, third] (argument * atInfinity element)) := by
    have equality := cocycle.2.2.1 element ![first, second, third] argument
    have tuple : (fun index : Fin 3 => element * ![first, second, third] index) =
        ![element * first, element * second, element * third] := by
      funext index
      fin_cases index <;> rfl
    rwa [tuple] at equality
  change source ![projection (element * vertices 0), element * vertices 0, element * vertices 1] argument -
    source ![projection (element * vertices 0), projection (element * vertices 1), element * vertices 1] argument = _
  rw [covariant 0, covariant 1, translated, translated, ← map_sub]
  rfl

theorem sourceRealVertexPrism_left_translate {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data side source)
    (projection : RealGL3 → RealGL3) (element real : RealGL3)
    (vertices : Fin 2 → RealGL3) (finite : FiniteGL)
    (covariant : ∀ index, projection (element * (real * vertices index)) =
      element * projection (real * vertices index)) :
    sourceRealVertexPrism data.chi source projection (element * real) finite vertices =
    sourceRealVertexPrism data.chi
      (fun vertices argument => source vertices (argument * atInfinity element)) projection real finite vertices := by
  simp only [sourceRealVertexPrism, mul_assoc]
  rw [sourceVertexPrism_left_translate data side source cocycle projection element
    (fun index => real * vertices index) (atFinite finite) covariant,
    ← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
