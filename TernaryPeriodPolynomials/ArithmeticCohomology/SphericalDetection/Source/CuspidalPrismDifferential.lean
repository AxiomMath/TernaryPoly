module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineTruncatedShift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def sourceCuspidalRealTranslate {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (real : RealGL3) (base : AdelicGL) (vertices : Fin 3 → RealGL3) :
    cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
  cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
    (sourcePlaneCuspidalValues data source cocycle (fun index => real * vertices index) base)

theorem sourceCuspidalRealTranslate_atInfinity {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (real : RealGL3) (vertices : Fin 3 → RealGL3) :
    sourceCuspidalRealTranslate data source cocycle real 1 vertices =
      sourcePlaneCuspidalValues data source cocycle vertices (atInfinity real) := by
  apply Subtype.ext
  funext argument
  exact (sourcePlaneCuspidalValues_real_translate data source cocycle vertices real argument).symm

theorem sourceCuspidalVertexPrism_differential {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (projection : RealGL3 → RealGL3) (real : RealGL3) (base : AdelicGL) (vertices : Fin 3 → RealGL3) :
    sourceCuspidalRealTranslate data source cocycle real base vertices -
      cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
        (sourcePlaneCuspidalValues data source cocycle (fun index => projection (real * vertices index)) base) =
    sourceCuspidalVertexPrism data source cocycle projection real base ![vertices 1, vertices 2] -
      sourceCuspidalVertexPrism data source cocycle projection real base ![vertices 0, vertices 2] +
      sourceCuspidalVertexPrism data source cocycle projection real base ![vertices 0, vertices 1] := by
  have closed := homogeneousVertexPrism_differential
    (fun vertices => sourcePlaneCuspidalValues data source cocycle vertices base)
    (fun vertices => sourcePlaneCuspidalValues_closed data source cocycle vertices base)
    projection (fun index => real * vertices index)
  have translated_pair (first second : RealGL3) :
      (fun index : Fin 2 => real * ![first, second] index) = ![real * first, real * second] := by
    funext index
    fin_cases index <;> rfl
  rw [sourceCuspidalVertexPrism, sourceCuspidalVertexPrism, sourceCuspidalVertexPrism,
    translated_pair, translated_pair, translated_pair]
  have mapped := congrArg (cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)) closed
  simpa only [map_sub, map_add, sourceCuspidalRealTranslate] using mapped.symm

theorem sourcePlaneCuspidalValues_repeated_first {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (first second : RealGL3) (base : AdelicGL) :
    sourcePlaneCuspidalValues data source cocycle ![first, first, second] base = 0 := by
  apply Subtype.ext
  funext argument
  change normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
    source ![first, first, second] (planeLevi argument 1 * base) = 0
  rw [sourceCocycle_repeated_first data .plane source cocycle diagonal, smul_zero]

theorem sourcePlaneCuspidalValues_repeated_last {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (first second : RealGL3) (base : AdelicGL) :
    sourcePlaneCuspidalValues data source cocycle ![first, second, second] base = 0 := by
  apply Subtype.ext
  funext argument
  change normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
    source ![first, second, second] (planeLevi argument 1 * base) = 0
  rw [sourceCocycle_repeated_last data .plane source cocycle diagonal, smul_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
