module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneArithmeticEvaluation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneAmbientEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalSmooth

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def sourcePlaneLevelGroupCocycle {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) :
    groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree data.cusp data.chi) :=
  ⟨fun pair => ⟨sourcePlaneGroupCocycle data source cocycle pair, by
    change sourcePlaneCuspidalValues data source cocycle
      (fun index => realPlaneMatrix (![1, pair.1, pair.1 * pair.2] index)) 1 ∈ _
    simpa only [atInfinity_one] using sourcePlaneCuspidalValues_finiteLevel data source cocycle
      (fun index => realPlaneMatrix (![1, pair.1, pair.1 * pair.2] index)) 1⟩, by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro first second third
    apply Subtype.ext
    exact (groupCohomology.mem_cocycles₂_iff _).mp
      (sourcePlaneGroupCocycle data source cocycle).property first second third⟩

theorem sourcePlaneLevelGroupCocycle_val {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (first second : RealPlaneGroup) :
    (sourcePlaneLevelGroupCocycle data source cocycle (first, second)).val =
      sourcePlaneGroupCocycle data source cocycle (first, second) := rfl

theorem sourcePlaneLevelGroupCocycle_arithmetic {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (cycle : MaximalCycles degree data.chi .plane)
    (evaluates : Evaluates data .plane source cycle) :
    realPlaneArithmeticCocycle degree data.cusp data.chi (sourcePlaneLevelGroupCocycle data source cocycle) =
      ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent degree data.chi)
        (evaluateFlagCycle data.chi .plane (QuotientGroup.mk (1 : RationalGL3)) cycle) := by
  apply Subtype.ext
  funext pair
  rcases pair with ⟨first, second⟩
  change realPlaneArithmeticCocycle degree data.cusp data.chi (sourcePlaneLevelGroupCocycle data source cocycle)
    (first, second) = _
  rw [realPlaneArithmeticCocycle_apply, sourcePlaneLevelGroupCocycle_val]
  exact sourcePlaneGroupCocycle_arithmetic data source cocycle cycle evaluates first second

theorem sourcePlaneLevelH2_arithmetic {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (cycle : MaximalCycles degree data.chi .plane)
    (evaluates : Evaluates data .plane source cycle) :
    realPlaneArithmeticH2 degree data.cusp data.chi
        (groupCohomology.H2π (realPlaneLevelCuspidalRep degree data.cusp data.chi)
          (sourcePlaneLevelGroupCocycle data source cocycle)) =
      groupCohomology.H2π (subgroupCoefficientRep
        (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) (rationalCoefficientComponent degree data.chi))
        (ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
          (rationalCoefficientComponent degree data.chi)
          (evaluateFlagCycle data.chi .plane (QuotientGroup.mk (1 : RationalGL3)) cycle)) := by
  rw [realPlaneArithmeticH2_apply, sourcePlaneLevelGroupCocycle_arithmetic data source cocycle cycle evaluates]

def realPlaneLevelArithmeticBinaryEdge (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cusp : CuspidalRepresentation) (character : RankOneCharacter) (trivial : character = trivialCharacter) :
    groupCohomology.H2 (realPlaneLevelCuspidalRep degree cusp character) →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (degree + 1) (-1)) := by
  subst character
  exact (identityPlaneFullBinaryEdge degree positive odd).comp
    (realPlaneArithmeticH2 degree cusp trivialCharacter)

theorem realPlaneLevelArithmeticBinaryEdge_compare (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cusp : CuspidalRepresentation) (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (sourceClass : groupCohomology.H2 (realPlaneLevelCuspidalRep degree cusp character))
    (targetCycle : Homogeneous.cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent degree character))
    (comparison : realPlaneArithmeticH2 degree cusp character sourceClass =
      groupCohomology.H2π (subgroupCoefficientRep
        (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) (rationalCoefficientComponent degree character))
        (ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
          (rationalCoefficientComponent degree character) targetCycle)) :
    realPlaneLevelArithmeticBinaryEdge degree positive odd cusp character trivial sourceClass =
      identityPlaneAmbientBinaryEdge degree positive odd character trivial targetCycle := by
  subst character
  exact congrArg (identityPlaneFullBinaryEdge degree positive odd) comparison

theorem sourcePlaneLevelBinaryEdge_compare {degree : ℕ} (positive : 0 < degree) (odd : Odd degree)
    (data : InducingData degree) (trivial : data.chi = trivialCharacter) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (cycle : MaximalCycles degree data.chi .plane)
    (evaluates : Evaluates data .plane source cycle) :
    realPlaneLevelArithmeticBinaryEdge degree positive odd data.cusp data.chi trivial
        (groupCohomology.H2π (realPlaneLevelCuspidalRep degree data.cusp data.chi)
          (sourcePlaneLevelGroupCocycle data source cocycle)) =
      identityPlaneAmbientBinaryEdge degree positive odd data.chi trivial
        (evaluateFlagCycle data.chi .plane (QuotientGroup.mk (1 : RationalGL3)) cycle) := by
  exact realPlaneLevelArithmeticBinaryEdge_compare degree positive odd data.cusp data.chi trivial _ _
    (sourcePlaneLevelH2_arithmetic data source cocycle cycle evaluates)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
