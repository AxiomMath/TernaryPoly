module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneGroup
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def normPowerCharacter (exponent : ℂ) : Adelesˣ →* ℂ where
  toFun unit := normPower unit exponent
  map_one' := normPower_one exponent
  map_mul' first second := normPower_mul first second exponent

theorem normPower_mul_neg_cancel (first second : Adelesˣ) (exponent : ℂ) :
    normPower second exponent * normPower (first * second) (-exponent) = normPower first (-exponent) := by
  rw [normPower_mul]
  have cancellation : normPower second exponent * normPower second (-exponent) = 1 := by
    simp only [normPower, neg_mul, Complex.exp_neg]
    exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
  calc
    normPower second exponent * (normPower first (-exponent) * normPower second (-exponent)) =
        normPower first (-exponent) * (normPower second exponent * normPower second (-exponent)) := by ring
    _ = normPower first (-exponent) := by rw [cancellation, mul_one]

def realPlaneBinaryInput : RealPlaneGroup →* BinaryAdelicGL :=
  (atInfinityMonoidHom 2).comp SemidirectProduct.rightHom

def realPlaneCuspidalTwist (degree : ℕ) : RealPlaneGroup →* ℂ :=
  (normPowerCharacter (((degree : ℂ) + 3) / 2)).comp (GeneralLinearGroup.det.comp realPlaneBinaryInput)

def realPlaneCuspidalRep (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) :
    Rep ℂ RealPlaneGroup :=
  Rep.of (X := cuspidalTensorValues cusp (HomogeneousPoly degree)) (cuspidalTensorRepresentation cusp
    ((realCoefficientComponent degree character).comp realPlaneMatrix) realPlaneBinaryInput (realPlaneCuspidalTwist degree))

theorem realPlaneCuspidalRep_apply (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (element : RealPlaneGroup) (values : cuspidalTensorValues cusp (HomogeneousPoly degree)) (argument : BinaryAdelicGL) :
    ((realPlaneCuspidalRep degree cusp character).ρ element values).val argument =
      normPower (GeneralLinearGroup.det (atInfinity element.right)) (((degree : ℂ) + 3) / 2) •
        realCoefficientComponent degree character (realPlaneMatrix element)
          (values.val (argument * atInfinity element.right)) := rfl

theorem atInfinity_planeLeviOne (matrix : BinaryRealGL) :
    atInfinity (planeLevi matrix 1) = planeLevi (atInfinity matrix) 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, combineGL, pairMatrix, planeLevi, planeBlock]

theorem atInfinity_planeUnipotent (first second : ℝ) :
    atInfinity (planeUnipotent first second) = planeUnipotent (first, 0) (second, 0) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, combineGL, pairMatrix, planeUnipotent]

theorem sourcePlane_realPlane_argument {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3)
    (element : RealPlaneGroup) (argument : BinaryAdelicGL) :
    source vertices (planeLevi argument 1 * atInfinity (realPlaneMatrix element)) =
      source vertices (planeLevi (argument * atInfinity element.right) 1) := by
  rw [realPlaneMatrix_apply, atInfinity_mul, atInfinity_planeLeviOne]
  change source vertices (planeLevi argument 1 *
    (atInfinity (planeUnipotent (element.left.toAdd 0) (element.left.toAdd 1)) * planeLevi (atInfinity element.right) 1)) = _
  rw [atInfinity_planeUnipotent, ← mul_assoc, planeLevi_planeUnipotent_commute, mul_assoc,
    sourcePlane_radical_invariant data source cocycle]
  exact congrArg (source vertices) (planeLeviOneHom.map_mul argument (atInfinity element.right)).symm

/-- The source's real parabolic covariance holds in the retained cusp-function coefficient module. -/
theorem sourcePlaneCuspidalValues_equivariant {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3) (element : RealPlaneGroup) :
    sourcePlaneCuspidalValues data source cocycle (fun index => realPlaneMatrix element * vertices index) 1 =
      (realPlaneCuspidalRep degree data.cusp data.chi).ρ element
        (sourcePlaneCuspidalValues data source cocycle vertices 1) := by
  apply Subtype.ext
  funext argument
  rw [sourcePlaneCuspidalValues_apply, realPlaneCuspidalRep_apply, sourcePlaneCuspidalValues_apply,
    mul_one, mul_one, cocycle.2.2.1, sourcePlane_realPlane_argument data source cocycle, map_smul, smul_smul,
    map_mul, normPower_mul_neg_cancel]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
