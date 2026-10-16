module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineRadicalPrism
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalAnalyticPullback

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def sourceCuspidalVertexPrism {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (projection : RealGL3 → RealGL3) (real : RealGL3) (base : AdelicGL)
    (vertices : Fin 2 → RealGL3) : cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
  cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
    (homogeneousVertexPrism (fun vertices => sourcePlaneCuspidalValues data source cocycle vertices base)
      projection (fun index => real * vertices index))

theorem sourceCuspidalVertexPrism_apply {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (projection : RealGL3 → RealGL3) (real : RealGL3) (base : AdelicGL)
    (vertices : Fin 2 → RealGL3) (argument : BinaryAdelicGL) :
    (sourceCuspidalVertexPrism data source cocycle projection real base vertices).val argument =
    normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
      realCoefficientComponent degree data.chi real⁻¹
        (homogeneousVertexPrism (fun vertices => source vertices (planeLevi argument 1 * base))
          projection (fun index => real * vertices index)) := by
  change realCoefficientComponent degree data.chi real⁻¹
      ((sourcePlaneCuspidalValues data source cocycle
          ![projection (real * vertices 0), real * vertices 0, real * vertices 1] base).val argument -
        (sourcePlaneCuspidalValues data source cocycle
          ![projection (real * vertices 0), projection (real * vertices 1), real * vertices 1] base).val argument) = _
  rw [sourcePlaneCuspidalValues_apply, sourcePlaneCuspidalValues_apply]
  simp only [homogeneousVertexPrism, map_sub, map_smul, smul_sub]

theorem sourceCuspidalVertexPrism_identity {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (projection : RealGL3 → RealGL3) (real : RealGL3) (finite : FiniteGL)
    (vertices : Fin 2 → RealGL3) :
    (sourceCuspidalVertexPrism data source cocycle projection real (atFinite finite) vertices).val 1 =
      sourceRealVertexPrism data.chi source projection real finite vertices := by
  rw [sourceCuspidalVertexPrism_apply, map_one, normPower_one, one_smul,
    show planeLevi (1 : BinaryAdelicGL) 1 = 1 from (planeLeviHom Adeles).map_one, one_mul]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
