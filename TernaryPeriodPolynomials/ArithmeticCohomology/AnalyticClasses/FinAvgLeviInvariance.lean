module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FinAvgLeviMeasure
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteWeight
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Norm

@[expose] public section


/-!
# Invariance of the finite good-line average under real integral Levi translations

For a spherical cusp vector `w` and an integral matrix `A`, the finite good-line average of the real
translate `π(A_∞) w` equals that of `w`. The real translate is the finite translate by `A_f⁻¹` on the
left (automorphy), which the transport of finite plane coordinates turns into the change of variables
`f ↦ f A` of the finite radical coordinates, and that change of variables preserves the measure.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The real image of an integral matrix. -/
def realLeviMatrix (A : GeneralLinearGroup (Fin 2) ℤ) : BinaryRealGL :=
  GeneralLinearGroup.map (Int.castRingHom ℝ) A

theorem rationalAdele_intMatrix (A : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map rationalAdele (GeneralLinearGroup.map (Int.castRingHom ℚ) A) =
      atInfinity (realLeviMatrix A) * atFinite (finiteLeviMatrix A) := by
  rw [← PlaneEisensteinContinuation.Norm.combineGL_eq_mul]
  apply Units.ext
  ext row column <;> simp [combineGL, pairMatrix, realLeviMatrix, finiteLeviMatrix, rationalAdele,
    GeneralLinearGroup.map_apply]

/-- The real translate of a smooth vector. -/
def realTranslateVector (cusp : CuspidalRepresentation) (A : GeneralLinearGroup (Fin 2) ℤ)
    (w : cusp.smooth) : cusp.smooth :=
  ⟨cusp.π (atInfinity (realLeviMatrix A)) w.val, cusp.smooth_stable _ _ w.property⟩

theorem realTranslateVector_spherical (cusp : CuspidalRepresentation) (A : GeneralLinearGroup (Fin 2) ℤ)
    (w : cusp.smooth) (spherical : w.val ∈ cuspSphericalValues cusp) :
    (realTranslateVector cusp A w).val ∈ cuspSphericalValues cusp := by
  intro element
  change cusp.π _ (cusp.π _ w.val) = cusp.π _ w.val
  rw [← Module.End.mul_apply, ← map_mul,
    ← (atInfinity_commute_atFinite (realLeviMatrix A) _).eq, map_mul, Module.End.mul_apply,
    spherical element]

theorem realize_realTranslateVector (cusp : CuspidalRepresentation) (A : GeneralLinearGroup (Fin 2) ℤ)
    (w : cusp.smooth) (block : BinaryFiniteGL) :
    cusp.realize (realTranslateVector cusp A w) (atFinite (finiteLeviMatrix A * block)) =
      cusp.realize w (atFinite block) := by
  unfold realTranslateVector
  rw [cusp.equivariant, atFinite_mul, mul_assoc, ← (atInfinity_commute_atFinite (realLeviMatrix A) block).eq,
    ← mul_assoc, ← (atInfinity_commute_atFinite (realLeviMatrix A) (finiteLeviMatrix A)).eq,
    ← rationalAdele_intMatrix, cusp.leftRational]

theorem normPower_finiteLeviMatrix_det (A : GeneralLinearGroup (Fin 2) ℤ) (exponent : ℂ) :
    normPower (finiteAdeleUnit (GeneralLinearGroup.det (finiteLeviMatrix A))) exponent = 1 := by
  have hmap : finiteLeviMatrix A = GeneralLinearGroup.map integralEmbedding
      (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) A) :=
    (map_integralEmbedding_intCast A).symm
  rw [hmap, generalLinearGroup_det_map]
  exact normPower_finiteIntegralUnit _ exponent

/-- The spherical plane value is unchanged by the transport. -/
theorem finiteSphericalPlaneValue_transport (cusp : CuspidalRepresentation) (A : GeneralLinearGroup (Fin 2) ℤ)
    (w : cusp.smooth) (exponent : ℂ) (f : FiniteAwayThree × FiniteAwayThree)
    (coords : FinitePlaneInductionCoordinates (standardGoodLineFiniteArgument (leviRowAction A f))) :
    finiteSphericalPlaneValue cusp (realTranslateVector cusp A w) exponent (transportCoordinates A f coords) =
      finiteSphericalPlaneValue cusp w exponent coords := by
  unfold finiteSphericalPlaneValue
  change normPower (finiteAdeleUnit (GeneralLinearGroup.det (finiteLeviMatrix A * coords.block))) exponent *
      cusp.realize (realTranslateVector cusp A w) (atFinite (finiteLeviMatrix A * coords.block)) = _
  rw [realize_realTranslateVector, map_mul, finiteAdeleUnit_mul, normPower_mul,
    normPower_finiteLeviMatrix_det, one_mul]

/-- **Invariance of the finite good-line average under real integral Levi translations.** -/
theorem goodLineFiniteVectorIntegral_realTranslate (degree : ℕ) (cusp : CuspidalRepresentation)
    (parameter : ℂ) (A : GeneralLinearGroup (Fin 2) ℤ) (w : cusp.smooth)
    (spherical : w.val ∈ cuspSphericalValues cusp) :
    goodLineFiniteVectorIntegral degree cusp parameter (realTranslateVector cusp A w) =
      goodLineFiniteVectorIntegral degree cusp parameter w := by
  rw [goodLineFiniteVectorIntegral_eq_coordinates degree cusp parameter (realTranslateVector cusp A w)
      (realTranslateVector_spherical cusp A w spherical)
      (fun f => transportCoordinates A f (finitePlaneInductionCoordinates _)),
    goodLineFiniteVectorIntegral_eq_coordinates degree cusp parameter w spherical
      (fun f => finitePlaneInductionCoordinates _)]
  simp only [finiteSphericalPlaneValue_transport]
  exact (leviRowAction_measurePreserving A).integral_comp
    (leviRowEquiv A).toHomeomorph.measurableEmbedding
    (fun f => finiteSphericalPlaneValue cusp w ((degree : ℂ) / 2 + 3 + parameter)
      (finitePlaneInductionCoordinates (standardGoodLineFiniteArgument f)))

end TernaryPeriodPolynomials.AnalyticClasses
