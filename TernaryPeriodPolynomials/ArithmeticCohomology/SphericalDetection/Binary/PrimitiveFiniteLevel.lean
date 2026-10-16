module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorArithmetic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.InvariantValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryCuspidalPrimitive_unique (degree : ℕ) (cusp : CuspidalRepresentation)
    (first second : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)))
    (same : ∀ matrix argument,
      binaryCohomologicalAction degree matrix first.val argument - first.val argument =
        binaryCohomologicalAction degree matrix second.val argument - second.val argument) : first = second := by
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply binaryValues_invariant_eq_zero cusp (first - second).val
    ((cuspidalTensorValues_binary_iff cusp degree _).mp (first - second).property)
  intro matrix argument
  have equality := same matrix argument
  change binaryCohomologicalAction degree matrix (first.val - second.val) argument =
    first.val argument - second.val argument
  change binaryCohomologicalOperator degree matrix (first.val - second.val) argument = _
  rw [map_sub]
  change binaryCohomologicalAction degree matrix first.val argument -
    binaryCohomologicalAction degree matrix second.val argument = _
  linear_combination (norm := abel) equality

theorem binaryCuspidalPrimitive_finiteLevel (degree : ℕ) (cusp : CuspidalRepresentation)
    (potential : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)))
    (cycle : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (boundary : ∀ matrix argument, cycle matrix argument =
      binaryCohomologicalAction degree matrix potential.val argument - potential.val argument)
    (fixed : ∀ matrix integral argument,
      cycle matrix (argument * atFinite (GeneralLinearGroup.map integralEmbedding integral)) = cycle matrix argument) :
    potential ∈ cuspidalTensorFiniteLevel cusp (Binary.HomogeneousPoly (degree + 1)) := by
  intro integral argument
  have equality : cuspidalTensorTranslation cusp (atFinite (GeneralLinearGroup.map integralEmbedding integral)) potential =
      potential := by
    apply binaryCuspidalPrimitive_unique degree cusp
    intro matrix base
    change binaryCohomologicalAction degree matrix
        (fun point => potential.val (point * atFinite (GeneralLinearGroup.map integralEmbedding integral))) base -
        potential.val (base * atFinite (GeneralLinearGroup.map integralEmbedding integral)) = _
    have commute : binaryCohomologicalAction degree matrix
        (fun point => potential.val (point * atFinite (GeneralLinearGroup.map integralEmbedding integral))) base =
        binaryCohomologicalAction degree matrix potential.val
          (base * atFinite (GeneralLinearGroup.map integralEmbedding integral)) := by
      unfold binaryCohomologicalAction
      dsimp only
      rw [mul_assoc, (atInfinity_commute_atFinite matrix (GeneralLinearGroup.map integralEmbedding integral)).eq,
        ← mul_assoc]
    rw [commute, ← boundary, fixed, boundary]
  exact congrArg (fun values : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)) => values.val argument) equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
