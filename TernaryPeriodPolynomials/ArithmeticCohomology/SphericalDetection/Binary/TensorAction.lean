module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SmoothCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspSmoothAction (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    Module.End ℂ cusp.smooth where
  toFun vector := ⟨cusp.π matrix vector.val,
    cusp.smooth_stable matrix vector.val vector.property⟩
  map_add' first second := Subtype.ext (map_add (cusp.π matrix) first.val second.val)
  map_smul' scalar vector := Subtype.ext (map_smul (cusp.π matrix) scalar vector.val)

theorem cuspSmoothAction_realize (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    (vector : cusp.smooth) (argument : BinaryAdelicGL) :
    cusp.realize (cuspSmoothAction cusp matrix vector) argument =
      cusp.realize vector (argument * matrix) := cusp.equivariant matrix vector argument

theorem binarySmoothCoordinate_right_translate {degree : ℕ}
    (cusp : CuspidalRepresentation)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (values : binaryCuspidalValues cusp degree) (matrix : BinaryAdelicGL) :
    binarySmoothCoordinate cusp functional (binaryRightTranslation cusp degree matrix values) =
      cuspSmoothAction cusp matrix (binarySmoothCoordinate cusp functional values) := by
  apply cusp.injective
  funext argument
  rw [binarySmoothCoordinate_realize, cuspSmoothAction_realize, binarySmoothCoordinate_realize]
  rfl

theorem binarySmoothCoordinates_action {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrix : BinaryRealGL) (values : binaryCuspidalValues cusp degree) (position : index) :
    binarySmoothCoordinates cusp basis (binaryCuspidalRepresentation cusp degree matrix values)
      position =
    normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
      ∑ source, basis.coord position (binaryCoefficient degree matrix (basis source)) •
        cuspSmoothAction cusp (atInfinity matrix) (binarySmoothCoordinates cusp basis values source) := by
  classical
  apply cusp.injective
  funext argument
  change cusp.realize (binarySmoothCoordinate cusp (basis.coord position) _) argument = _
  rw [binarySmoothCoordinate_realize]
  change basis.coord position (binaryCohomologicalAction degree matrix values.val argument) = _
  simp only [binaryCohomologicalAction, map_smul, map_sum, Finset.sum_apply, Pi.smul_apply,
    cuspSmoothAction_realize, binarySmoothCoordinates, LinearMap.pi_apply,
    binarySmoothCoordinate_realize]
  congr 1
  have expansion := congrArg
    (fun polynomial => basis.coord position (binaryCoefficient degree matrix polynomial))
    (basis.sum_repr (values.val (argument * atInfinity matrix)))
  simpa only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm] using
    expansion.symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
