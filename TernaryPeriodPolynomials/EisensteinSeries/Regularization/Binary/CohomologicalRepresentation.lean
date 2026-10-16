module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CuspCoefficientAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem binaryCohomologicalAction_one (degree : ℕ)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) (argument : BinaryAdelicGL) :
    binaryCohomologicalAction degree 1 values argument = values argument := by
  simp only [binaryCohomologicalAction, binaryCoefficient, binary_atInfinity_one, map_one,
    normPower_one, Module.End.one_apply, mul_one, one_smul]

theorem binaryCohomologicalAction_mul (degree : ℕ) (first second : BinaryRealGL)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) (argument : BinaryAdelicGL) :
    binaryCohomologicalAction degree (first * second) values argument =
      binaryCohomologicalAction degree first (binaryCohomologicalAction degree second values) argument := by
  simp only [binaryCohomologicalAction, binaryCoefficient, binary_atInfinity_mul, map_mul,
    normPower_mul, Module.End.mul_apply, map_smul, smul_smul, mul_assoc]

noncomputable def binaryCuspRightAction (cusp : CuspidalRepresentation) (degree : ℕ)
    (matrix : BinaryAdelicGL) : Module.End ℂ (BinaryDegreeMonomial (degree + 1) → cusp.smooth) :=
  LinearMap.pi (fun monomial => (cuspSmoothAction cusp matrix).comp (LinearMap.proj monomial))

noncomputable def binaryCuspTwistedAction (cusp : CuspidalRepresentation) (degree : ℕ)
    (matrix : BinaryRealGL) : Module.End ℂ (BinaryDegreeMonomial (degree + 1) → cusp.smooth) :=
  (binaryCuspCoefficientAction cusp degree
    (normPower (GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
      binaryCoefficient degree matrix)).comp (binaryCuspRightAction cusp degree (atInfinity matrix))

theorem binaryCuspTwistedAction_realize (cusp : CuspidalRepresentation) (degree : ℕ)
    (matrix : BinaryRealGL) (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth)
    (argument : BinaryAdelicGL) :
    binaryCuspRealize cusp degree (binaryCuspTwistedAction cusp degree matrix vectors) argument =
      binaryCohomologicalAction degree matrix (binaryCuspRealize cusp degree vectors) argument := by
  change binaryCuspRealize cusp degree (binaryCuspCoefficientAction cusp degree _
    (fun monomial => cuspSmoothAction cusp (atInfinity matrix) (vectors monomial))) argument = _
  rw [binaryCuspCoefficientAction_realize, binaryCuspRealize_translate]
  rfl

noncomputable def binaryCohomologicalRepresentation (cusp : CuspidalRepresentation) (degree : ℕ) :
    Representation ℂ BinaryRealGL (BinaryDegreeMonomial (degree + 1) → cusp.smooth) where
  toFun := binaryCuspTwistedAction cusp degree
  map_one' := by
    apply LinearMap.ext
    intro vectors
    apply binaryCuspRealize_injective cusp degree
    funext argument
    rw [binaryCuspTwistedAction_realize, binaryCohomologicalAction_one]
    rfl
  map_mul' first second := by
    apply LinearMap.ext
    intro vectors
    apply binaryCuspRealize_injective cusp degree
    funext argument
    simp only [Module.End.mul_apply, binaryCuspTwistedAction_realize, binaryCohomologicalAction_mul]
    apply congrArg (fun values => binaryCohomologicalAction degree first values argument)
    funext other
    exact (binaryCuspTwistedAction_realize cusp degree second vectors other).symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
