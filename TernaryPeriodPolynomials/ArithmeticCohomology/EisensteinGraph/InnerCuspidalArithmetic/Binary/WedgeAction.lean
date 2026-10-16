module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InvariantCocycles

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem binaryUntwistedHomogeneous_val (degree : ℕ) (binary : Binary.GL2)
    (polynomial : Binary.HomogeneousPoly degree) :
    (Binary.homogeneousAction degree 0 binary polynomial).val =
      Binary.substitute binary.inv polynomial.val := by
  change Binary.action 0 binary polynomial.val = _
  simp [Binary.action_apply, Binary.determinantCharacter]

theorem binarySubstitute_inverse (binary : Binary.GL2) (polynomial : Binary.Poly) :
    Binary.substitute binary.val (Binary.substitute binary.inv polynomial) = polynomial := by
  rw [← AlgHom.comp_apply, Binary.substitute_comp, binary.inv_val, Binary.substitute_one]
  rfl

theorem binarySubstitute_injective (binary : Binary.GL2) :
    Function.Injective (Binary.substitute binary.val) := by
  intro first second equality
  have mapped := congrArg (Binary.substitute binary.inv) equality
  simpa only [← AlgHom.comp_apply, Binary.substitute_comp, binary.val_inv,
    Binary.substitute_one, AlgHom.id_apply] using mapped

def binaryMatrixPairAction (degree : ℕ) (binary : Binary.GL2)
    (pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree) :
    Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree :=
  ((GeneralLinearGroup.det binary).val⁻¹ •
      (binary.val 0 0 • Binary.homogeneousAction degree 0 binary pair.1 +
        binary.val 0 1 • Binary.homogeneousAction degree 0 binary pair.2),
    (GeneralLinearGroup.det binary).val⁻¹ •
      (binary.val 1 0 • Binary.homogeneousAction degree 0 binary pair.1 +
        binary.val 1 1 • Binary.homogeneousAction degree 0 binary pair.2))

theorem binaryPairWedge_matrixAction (degree : ℕ) (binary : Binary.GL2)
    (pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree) :
    binaryPairWedge degree (binaryMatrixPairAction degree binary pair) =
      Binary.homogeneousAction (degree + 1) 0 binary (binaryPairWedge degree pair) := by
  apply Subtype.ext
  rw [binaryUntwistedHomogeneous_val]
  apply binarySubstitute_injective binary
  rw [binarySubstitute_inverse]
  change Binary.substitute binary.val
    (X 0 * ((GeneralLinearGroup.det binary).val⁻¹ •
      (binary.val 1 0 • (Binary.homogeneousAction degree 0 binary pair.1).val +
        binary.val 1 1 • (Binary.homogeneousAction degree 0 binary pair.2).val)) -
      X 1 * ((GeneralLinearGroup.det binary).val⁻¹ •
        (binary.val 0 0 • (Binary.homogeneousAction degree 0 binary pair.1).val +
          binary.val 0 1 • (Binary.homogeneousAction degree 0 binary pair.2).val))) =
    X 0 * pair.2.val - X 1 * pair.1.val
  simp only [binaryUntwistedHomogeneous_val, map_sub, map_mul, map_smul, map_add,
    Binary.substitute_X, binarySubstitute_inverse]
  have determinantEquation :
      (C (GeneralLinearGroup.det binary).val⁻¹ : Binary.Poly) *
        (C (binary.val 0 0) * C (binary.val 1 1) -
          C (binary.val 0 1) * C (binary.val 1 0)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, ← Matrix.det_fin_two, ← map_mul]
    rw [GeneralLinearGroup.val_det_apply, inv_mul_cancel₀ (GeneralLinearGroup.det_ne_zero binary)]
    exact map_one _
  simp only [Binary.linearForm, Fin.sum_univ_two, Algebra.smul_def]
  change (C (binary.val 0 0) * X 0 + C (binary.val 0 1) * X 1) *
      (C (GeneralLinearGroup.det binary).val⁻¹ *
        (C (binary.val 1 0) * pair.1.val + C (binary.val 1 1) * pair.2.val)) -
    (C (binary.val 1 0) * X 0 + C (binary.val 1 1) * X 1) *
      (C (GeneralLinearGroup.det binary).val⁻¹ *
        (C (binary.val 0 0) * pair.1.val + C (binary.val 0 1) * pair.2.val)) = _
  calc
    _ = (C (GeneralLinearGroup.det binary).val⁻¹ *
      (C (binary.val 0 0) * C (binary.val 1 1) -
        C (binary.val 0 1) * C (binary.val 1 0))) * (X 0 * pair.2.val - X 1 * pair.1.val) := by ring
    _ = _ := by rw [determinantEquation, one_mul]

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
