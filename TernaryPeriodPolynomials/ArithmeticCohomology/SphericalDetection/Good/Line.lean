module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Restriction

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def rationalGoodLine : RationalGL3 :=
  ⟨!![0,0,1;0,1,0;1,0,0], !![0,0,1;0,1,0;1,0,0], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem rationalGoodLine_inverse : rationalGoodLine⁻¹ = rationalGoodLine := by
  apply Units.ext
  rfl

theorem rationalGoodLine_at_three :
    GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) rationalGoodLine = localGoodLine := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map_apply, rationalGoodLine, localGoodLine]

theorem rationalGoodLine_good :
    GoodFlag .line (QuotientGroup.mk rationalGoodLine) := by
  refine ⟨![0,0,1], ⟨rationalGoodLine, rfl, ![1,0,0], ⟨rfl, rfl⟩, ?_⟩, ?_⟩
  · funext row
    fin_cases row <;>
      simp [rationalGoodLine, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change (1 : ZMod 3) ≠ 0
    norm_num

theorem rationalGoodLine_restriction_zero {degree : ℕ}
    (character : RankOneCharacter) (coordinate : StratumH2 degree character .line)
    (vanishing : VanishesOnGood degree character .line coordinate) :
    flagRestriction character .line (QuotientGroup.mk rationalGoodLine) coordinate = 0 :=
  vanishesOnGood_flagRestriction_zero character .line coordinate vanishing
    (QuotientGroup.mk rationalGoodLine) rationalGoodLine_good

theorem localStandardMatrix (first second : ℚ_[3]) :
    (weyl⁻¹ * lineUnipotent first second * localGoodLine).val =
      !![0,1,0;1,0,0;second,first,1] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [weyl, lineUnipotent, upperUnipotent, localGoodLine,
      Matrix.mul_apply, Fin.sum_univ_three]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
