module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismRectangleMixed

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourceCuspidalVertexPrism_translate {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (projection : RealGL3 → RealGL3) (real element : RealGL3)
    (base : AdelicGL) (vertices : Fin 2 → RealGL3) :
    sourceCuspidalVertexPrism data source cocycle projection real base
        (fun position => element * vertices position) =
      cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi element)
        (sourceCuspidalVertexPrism data source cocycle projection (real * element) base vertices) := by
  apply Subtype.ext
  funext argument
  change (sourceCuspidalVertexPrism data source cocycle projection real base
      (fun position => element * vertices position)).val argument =
    realCoefficientComponent degree data.chi element
      ((sourceCuspidalVertexPrism data source cocycle projection (real * element) base vertices).val argument)
  simp only [sourceCuspidalVertexPrism_apply, mul_assoc, map_smul, ← Module.End.mul_apply,
    ← map_mul, _root_.mul_inv_rev, mul_inv_cancel_left]

theorem goodLineCuspidalVertexPrism_radical_translate {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (real : ℝ × ℝ) (base : AdelicGL) (radical : RadicalLattice) (vertices : Fin 2 → RealGL3) :
    sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) base
        (fun position => GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical) * vertices position) =
      cuspidalTensorMap data.cusp
        (realCoefficientComponent degree data.chi
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice radical)))
        (sourceCuspidalVertexPrism data source cocycle realUpperLeftLeviProjection
          (standardGoodLineRealArgument (goodLineRadicalRealShift radical real)) base vertices) := by
  rw [sourceCuspidalVertexPrism_translate, standardGoodLineRealArgument_radical]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
