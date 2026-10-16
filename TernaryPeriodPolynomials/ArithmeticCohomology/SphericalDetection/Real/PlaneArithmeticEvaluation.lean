module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorArithmetic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneArithmeticComparison
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem identityPlaneRealGroup_right
    (element : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :
    (identityPlaneRealGroup element).right =
      GeneralLinearGroup.map (Int.castRingHom ℝ) (identityPlaneLeviProjection element) := by
  apply Units.ext
  funext row column
  rw [← realPlaneMatrix_binary_entry, identityPlaneRealGroup_matrix]
  have entry := congrFun (congrFun (identityPlaneLeviProjection_spec element) row) column
  change (((identityPlaneLeviProjection element).val row column : ℤ) : ℚ) =
    element.val.val row.castSucc column.castSucc at entry
  change (element.val.val row.castSucc column.castSucc : ℝ) =
    ((identityPlaneLeviProjection element).val row column : ℝ)
  rw [← entry]
  norm_cast

def realPlaneLevelEvaluation (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) :
    realPlaneLevelCuspidalRep degree cusp character →ₗ[ℂ] HomogeneousPoly degree where
  toFun values := values.val.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem realPlaneLevelEvaluation_equivariant (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (element : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
    (values : realPlaneLevelCuspidalRep degree cusp character) :
    realPlaneLevelEvaluation degree cusp character
        ((realPlaneLevelCuspidalRep degree cusp character).ρ (identityPlaneRealGroup element) values) =
      rationalCoefficientComponent degree character element.val (realPlaneLevelEvaluation degree cusp character values) := by
  change ((realPlaneCuspidalRep degree cusp character).ρ (identityPlaneRealGroup element) values.val).val 1 =
    rationalCoefficientComponent degree character element.val (values.val.val 1)
  rw [realPlaneCuspidalRep_apply, identityPlaneRealGroup_right, normPower_binaryIntegralReal,
    one_smul, one_mul, cuspidalTensorFiniteLevel_integralReal cusp values.val values.property,
    identityPlaneRealGroup_matrix]
  rfl

def realPlaneArithmeticEvaluation (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) :
    Rep.res identityPlaneRealGroup (realPlaneLevelCuspidalRep degree cusp character) ⟶
      subgroupCoefficientRep (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent degree character) :=
  Rep.ofHom ⟨realPlaneLevelEvaluation degree cusp character, by
    intro element
    apply LinearMap.ext
    intro values
    exact realPlaneLevelEvaluation_equivariant degree cusp character element values⟩

def realPlaneArithmeticH2 (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) :
    groupCohomology.H2 (realPlaneLevelCuspidalRep degree cusp character) →ₗ[ℂ]
      groupCohomology.H2 (subgroupCoefficientRep
        (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) (rationalCoefficientComponent degree character)) :=
  (groupCohomology.map identityPlaneRealGroup (realPlaneArithmeticEvaluation degree cusp character) 2).hom

def realPlaneArithmeticCocycle (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) :
    groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp character) →ₗ[ℂ]
      groupCohomology.cocycles₂ (subgroupCoefficientRep
        (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) (rationalCoefficientComponent degree character)) :=
  (groupCohomology.mapCocycles₂ identityPlaneRealGroup (realPlaneArithmeticEvaluation degree cusp character)).hom

theorem realPlaneArithmeticCocycle_apply (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp character))
    (first second : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :
    realPlaneArithmeticCocycle degree cusp character cycle (first, second) =
      (cycle (identityPlaneRealGroup first, identityPlaneRealGroup second)).val.val 1 := by
  exact congrFun (groupCohomology.mapCocycles₂_comp_i_apply identityPlaneRealGroup
    (realPlaneArithmeticEvaluation degree cusp character) cycle) (first, second)

theorem realPlaneArithmeticH2_apply (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp character)) :
    realPlaneArithmeticH2 degree cusp character
        (groupCohomology.H2π (realPlaneLevelCuspidalRep degree cusp character) cycle) =
      groupCohomology.H2π (subgroupCoefficientRep
        (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) (rationalCoefficientComponent degree character))
        (realPlaneArithmeticCocycle degree cusp character cycle) :=
  groupCohomology.H2π_comp_map_apply identityPlaneRealGroup (realPlaneArithmeticEvaluation degree cusp character) cycle

end TernaryPeriodPolynomials.SphericalDetection.Helpers
