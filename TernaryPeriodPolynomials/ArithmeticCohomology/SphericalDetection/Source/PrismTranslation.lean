module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.VertexPrism

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourceRealVertexPrism_translate {degree : ℕ}
    (character : RankOneCharacter) (source : SourceCochain degree)
    (projection : RealGL3 → RealGL3) (real element : RealGL3)
    (finite : FiniteGL) (vertices : Fin 2 → RealGL3) :
    sourceRealVertexPrism character source projection real finite
      (fun index => element * vertices index) =
    realCoefficientComponent degree character element
      (sourceRealVertexPrism character source projection (real * element) finite vertices) := by
  simp only [sourceRealVertexPrism, mul_assoc, ← Module.End.mul_apply, ← map_mul,
    _root_.mul_inv_rev, mul_inv_cancel_left]

theorem sourceRealVertexPrism_pair_translate {degree : ℕ}
    (character : RankOneCharacter) (source : SourceCochain degree)
    (projection : RealGL3 → RealGL3) (real first second : RealGL3)
    (finite : FiniteGL) :
    sourceRealVertexPrism character source projection real finite ![first, second] =
    realCoefficientComponent degree character first
      (sourceRealVertexPrism character source projection (real * first) finite
        ![1, first⁻¹ * second]) := by
  have vertices : (fun index : Fin 2 => first * ![1, first⁻¹ * second] index) =
      ![first, second] := by
    funext index
    fin_cases index <;> simp
  rw [← vertices, sourceRealVertexPrism_translate]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
